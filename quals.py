#!/usr/bin/env python3
"""Quals for svenn (quals = tests; see https://blog.beeminder.com/quals).

These are the functional spec. Each qual prints PASS or FAIL; a FAIL prints
replicata (how to reproduce), expectata (what should happen) and resultata
(what happened). Exit status is the number of failing quals.

Usage:  python3 quals.py            run every qual
        python3 quals.py cert svg   run only quals whose name contains a word

Jargon, defined once here and used throughout:
  label  an n-bit integer naming a region: bit i is 1 iff the region is inside
         curve i. In the JSON certificates a label is an n-character string,
         least significant bit first.
  face   one crossing of the Venn diagram, given as the four labels of the
         regions around it. (A face of the dual map, hence the name.)
  cert   short for certificate: {"n": n, "faces": [...]}, the dual map of a
         simple symmetric n-Venn diagram, in the format of Chris Dzoba's
         github.com/dzoba/venn17 repo.
  placeholder  someone else's published drawing of an n-Venn diagram, shown
         on the card for n, credited as its license requires, until this site
         has drawn its own. Listed in PLACEHOLDER below.
"""
import html
import html.parser
import json
import hashlib
import math
import os
import re
import struct
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zlib
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from scipy.spatial import cKDTree

import cert
from geom import candidate_pairs, nets, rotate, sample, segment_hits

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor' / 'venn17'))
import plotter_svg  # noqa: E402   (vendored; see venn.py)
NS = (2, 3, 5, 7, 11, 13, 17, 19, 23)  # every prime up to the largest n with a known diagram
DRAWN = NS                             # n for which a cert is available and a drawing is shown
# SHA-256 of the three certs taken from github.com/dzoba/venn17: the ones formally verified in Lean 4
PUBLISHED_SHA256 = {
    17: 'c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77',  # venn17-local-c3-s2.json
    19: 'ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d',  # venn19-closure-s196002.json
    23: 'adc5a02eeaac6e49ac56ed9acfe6aebf5325ca13ebe070486c792b0d80eae2b1',  # venn23-c25-s230025.json
}
# Placeholders: n -> (file, its SHA-256, the page it was copied from). Each file is byte-identical to one at
# github.com/dzoba/venn17 commit e89d6f6, under CC BY 4.0 like the rest of that repo's images and paper.
PLACEHOLDER = {}
CC_BY = 'https://creativecommons.org/licenses/by/4.0/'
PNG_ONLY = (23,)   # n whose card links to its PNG: view.html can't show 8,388,606 crossings
# n whose card opens view.html on this site's own drawing
VIEWED = tuple(n for n in DRAWN if n not in PLACEHOLDER and n not in PNG_ONLY)
PAGES = ('index.html', 'view.html')                        # the site's pages: the list, and the viewer
DOMAIN = 'svenn.dreev.es'


def cert_path(n): return HERE / 'certs' / f'venn-{n:02d}.json'
def svg_path(n): return HERE / 'img' / f'venn-{n:02d}.svg'


# ------------------------------------------------------------------ cert checking
def read_cert(n): return cert.read(cert_path(n), n)


def is_pow2(x): return (x > 0) & ((x & (x - 1)) == 0)


def check_cert(n, F):
    """Return {condition: bool} for the cert faces F (m x 4 ints). All True means F is the dual map of
    a simple n-Venn diagram on the sphere that is symmetric under the n-fold label rotation."""
    m, N = len(F), 1 << n
    r = {}
    r['face count is 2^n - 2'] = m == N - 2
    a, b, c, d = F.T
    e1, e2 = a ^ b, b ^ c
    # transversal crossing: the quadrilateral is a square of the n-cube with two distinct curve bits
    r['every face is a cube square'] = bool(np.all(is_pow2(e1) & is_pow2(e2) & (e1 != e2)
                                                  & ((c ^ d) == e1) & ((d ^ a) == e2)))
    r['all 2^n labels present'] = len(np.unique(F)) == N
    U, V = np.minimum(F, np.roll(F, -1, 1)).ravel(), np.maximum(F, np.roll(F, -1, 1)).ravel()
    key = U * N + V
    uk, cnt = np.unique(key, return_counts=True)
    r['every edge borders exactly two faces'] = bool(np.all(cnt == 2))
    r['Euler characteristic 2'] = N - len(uk) + m == 2
    del U, V, key, cnt   # 0.9 GB at n = 23
    r['faces orient consistently'], O = orient(F, N)
    r['every region is a disk'] = single_rotation_cycles(O, N)
    del O
    ek = uk  # undirected edges as U*N+V
    eu, ev = ek // N, ek % N
    ok = True
    for i in range(n):
        for side in (0, 1):
            keep = (((eu >> i) & 1) == side) & (((ev >> i) & 1) == side)
            verts = np.flatnonzero(((np.arange(N) >> i) & 1) == side)
            idx = np.full(N, -1)
            idx[verts] = np.arange(len(verts))
            g = coo_matrix((np.ones(keep.sum()), (idx[eu[keep]], idx[ev[keep]])), shape=(len(verts),) * 2)
            ok &= connected_components(g, directed=False)[0] == 1
    r['both sides of every curve connected'] = bool(ok)
    canon = np.sort(F, 1)
    rotated = np.sort(cert.rot(F, n), 1)   # the label rotation x[j] <- x[j+1] (its inverse works equally well)
    s1 = canon[np.lexsort(canon.T[::-1])]
    s2 = rotated[np.lexsort(rotated.T[::-1])]
    r['symmetric under label rotation'] = bool(np.array_equal(s1, s2))
    return r


def orient(F, N):
    """Orient every face so each edge is traversed once each way (BFS over shared edges). Returns whether that
    worked, and the faces with each flipped or not as the BFS chose."""
    m = len(F)
    start = F.ravel()                                # slot s = 4*face + j is the edge F[face, j] -> F[face, j+1]
    end = np.roll(F, -1, 1).ravel()
    key = np.minimum(start, end) * N + np.maximum(start, end)
    order = np.argsort(key, kind='stable')
    k2 = key[order]
    assert np.all(k2[0::2] == k2[1::2]) and np.all(k2[1:-1:2] != k2[2::2]), 'edge multiplicity is not 2'
    partner = np.empty(4 * m, np.int64)             # the other slot on the same edge
    partner[order[0::2]] = order[1::2]
    partner[order[1::2]] = order[0::2]
    # Two faces sharing an edge are consistently oriented iff they traverse it in opposite directions,
    # so their flips must differ exactly when, as listed, they traverse it the same way.
    need = (start[partner] == start).astype(np.int8)
    del end, key, order, k2
    flip = np.full(m, -1, np.int8)
    flip[0] = 0
    frontier = np.zeros(1, np.int64)
    while len(frontier):
        # The frontier's slots, face by face; a face not yet flipped takes its flip from the first slot that reaches
        # it and joins the next frontier in that order (so this is the face-at-a-time BFS, a level at a time).
        s = (4 * frontier[:, None] + np.arange(4)).ravel()
        s = s[flip[partner[s] // 4] < 0]
        g, first = np.unique(partner[s] // 4, return_index=True)
        flip[g] = flip[s[first] // 4] ^ need[s[first]]
        frontier = g[np.argsort(first)]
    reached = bool(np.all(flip >= 0))
    consistent = reached and bool(np.all((flip[np.arange(4 * m) // 4] ^ flip[partner // 4]) == need))
    O = np.where(flip[:, None] == 1, F[:, ::-1], F)
    return consistent, O


def single_rotation_cycles(O, N):
    """Around each label, chaining its faces through shared edges must give one cycle. This is the walk a dict of
    dicts would do, nxt[v][p] = q for each corner of each face in turn (label v, p before it and q after it), then
    for each v from the first p it got, failing if it reaches a p with no entry: done for every label at once, with
    sorted arrays for the dicts."""
    v = O.ravel()                            # corner c = 4*face + k: label v[c] between p[c] and q[c]
    p = np.roll(O, 1, 1).ravel()
    key = v * N + p
    order = np.argsort(key, kind='stable')
    ks = key[order]
    last = np.r_[ks[1:] != ks[:-1], True]    # the last corner with each (v, p), whose q the dict keeps
    node, to = ks[last], np.roll(O, -1, 1).ravel()[order[last]]   # the dicts' keys (v, p), as v*N + p, and values q
    del key, order, ks, last
    labels, first = np.unique(v, return_index=True)
    size = np.unique(node // N, return_counts=True)[1]          # len(nxt[v])
    home = np.searchsorted(node, labels * N + p[first])          # the key v's walk starts from
    del p
    goal = node // N * N + to
    nxt = np.minimum(np.searchsorted(node, goal), len(node) - 1)
    nxt[node[nxt] != goal] = -1                                  # the key each step lands on, or -1: a KeyError
    del goal
    ok = np.zeros(len(labels), bool)
    walk, at, steps = np.arange(len(labels)), nxt[home], 1   # the labels still walking, and where
    while len(walk):
        back = at == home[walk]
        ok[walk[back]] = steps == size[walk[back]]
        go = ~back & (at >= 0) & (steps < size[walk])
        walk, at, steps = walk[go], nxt[at[go]], steps + 1
    return bool(ok.all()) and len(labels) == N


# ------------------------------------------------------------------ drawing checking
def read_svg(path):
    """Return (curve, page, degrees): the (k x 4 x 2) array of cubic Bezier control nets of the SVG's one path, <path
    id="curve">, and for each curve i, drawn as <use id="curve-i">, the degrees it turns that path by about the page
    centre. Curve i is rotate(curve, page, degrees[i])."""
    t = path.read_text()
    page = float(re.search(r'viewBox="0 0 ([\d.]+) [\d.]+"', t).group(1))
    base = nets(re.search(r'<path id="curve" d="([^"]+)"/>', t).group(1))
    uses = re.findall(r'<use id="curve-(\d+)" href="#curve" [^>]*transform="rotate\(([-\d.e]+) ([\d.]+) ([\d.]+)\)"/>', t)
    assert [int(i) for i, _, _, _ in uses] == list(range(len(uses))), 'curve ids out of order'
    assert {(float(x), float(y)) for _, _, x, y in uses} == {(page / 2, page / 2)}, 'rotations not about the page centre'
    return base, page, [float(a) for _, a, _, _ in uses]


def inside(points, polys):
    """Even-odd membership of each point in each closed polyline: (P x n) bool."""
    out = np.zeros((len(points), len(polys)), bool)
    for c, P in enumerate(polys):
        Q = np.roll(P, -1, 0)
        for k, (x, y) in enumerate(points):
            cond = (P[:, 1] > y) != (Q[:, 1] > y)
            xs = P[cond, 0] + (y - P[cond, 1]) * (Q[cond, 0] - P[cond, 0]) / (Q[cond, 1] - P[cond, 1])
            out[k, c] = (xs > x).sum() % 2 == 1
    return out


def point_segment_distance(x, A, B):
    ab = B - A
    t = np.clip(((x - A) * ab).sum(1) / np.maximum((ab * ab).sum(1), 1e-300), 0, 1)
    return np.linalg.norm(x - (A + t[:, None] * ab), axis=1)


def drawn_faces(path, n):
    """Sample the curves of the drawing at path, find every crossing, and label the regions around each by walking
    each curve through its crossings, toggling the labels of the regions on its two sides; all from one sector (a
    1/n slice of the disk about the page centre).

    Curve i is the SVG's one path turned by k_i sectors, each k from 0 to n - 1 once (asserted, to within 1e-9 of a
    sector). So the drawing is the path's polyline P and n - 1 turned copies of it, and its crossings come in orbits
    (a crossing and its n - 1 turns by multiples of a sector). Each orbit has a crossing in the sector from angle 0
    to 360/n degrees, and both segments that crossing lies on reach into the sector; so intersecting the segments of
    every copy of P that reach into it finds every orbit. It finds some twice, near the sector's edges, so an orbit is
    named by the two segments of P its crossings lie on and the number of sectors between their copies of P. Each
    orbit has two crossings on P itself: one with the copy d sectors on, and that one turned back d sectors, which is
    on the copy d sectors back. Walking P through all of them is walking every curve, turned; turning a crossing
    turns its labels too, each curve's bit moving to the curve as many sectors on. Returns what walking every curve
    gives: the number of crossings (n per orbit); their faces (each orbit's turned n ways); and how many crossings the
    two curves through them label differently. Segment contacts and self-intersections fail asserts, counted over the
    whole drawing."""
    base, page, degrees = read_svg(path)
    assert len(degrees) == n, (len(degrees), n)
    turns = np.array(degrees) * n / 360
    k = np.round(turns).astype(np.int64) % n
    assert np.allclose(turns, np.round(turns), rtol=0, atol=1e-9) and sorted(k.tolist()) == list(range(n)), degrees
    curve = np.argsort(k)                        # curve[j] is the path turned by j sectors
    deg = np.array(degrees)[curve]               # by deg[j] degrees, as the file says
    P = sample(base, float(np.median(np.linalg.norm(base[:, 3] - base[:, 0], axis=1))) / 6)[0]
    A, B, M = P, np.roll(P, -1, 0), len(P)       # segment s of P runs from P[s] to P[s + 1]
    assert n * M * M < 2 ** 63, 'orbit names overflow'
    # each segment spans the angles lo to lo + width about the page centre (rotate() adds to angles)
    a0 = np.arctan2(A[:, 1] - page / 2, A[:, 0] - page / 2)
    sweep = np.remainder(np.arctan2(B[:, 1] - page / 2, B[:, 0] - page / 2) - a0 + math.pi, 2 * math.pi) - math.pi
    lo, width, th = a0 + np.minimum(sweep, 0), np.abs(sweep), 2 * math.pi / n
    assert width.max() < math.pi / 2, 'a segment passes too near the page centre'
    reach = []                                   # the segments of each copy of P that reach into the sector
    for j in range(n):
        ang = np.remainder(lo + j * th, 2 * math.pi)
        sel = np.flatnonzero((ang <= th + 1e-6) | (ang + width >= 2 * math.pi - 1e-6))   # a margin costs only time
        reach.append((sel, np.full(len(sel), j), rotate(A[sel], page, deg[j]), rotate(B[sel], page, deg[j])))
    seg, turn, SA, SB = (np.concatenate(x) for x in zip(*reach))
    del reach, a0, sweep, lo, width
    hits = [segment_hits(SA, SB, turn, seg, np.full(len(seg), M), i[q:q + 2_000_000], j[q:q + 2_000_000])
            for i, j in candidate_pairs(0.5 * (SA + SB), float(np.linalg.norm(B - A, axis=1).max()) * 1.0001)
            for q in range(0, len(i), 2_000_000)]
    i, j, t, u, ti, tj = (np.concatenate(h) for h in zip(*hits))
    del hits, SA, SB

    def orbit(i, j):
        """The name of the orbit of the crossing of found segments i and j, d * M^2 + s1 * M + s2 for segments s1 and
        s2 of P and copies of P d sectors apart, from whichever end makes it smaller; and whether that is i's end."""
        d = (turn[j] - turn[i]) % n
        fwd, bwd = (d * M + seg[i]) * M + seg[j], ((n - d) % n * M + seg[j]) * M + seg[i]
        return np.minimum(fwd, bwd), fwd <= bwd

    touches = n * len(np.unique(orbit(ti, tj)[0]))
    assert touches == 0, f'{touches} degenerate segment contacts'
    name, ahead = orbit(i, j)
    o = np.unique(name, return_index=True)[1]    # one crossing of each orbit
    i, j, t, u, ahead = i[o], j[o], t[o], u[o], ahead[o]
    d = np.where(ahead, turn[j] - turn[i], turn[i] - turn[j]) % n
    s1, t1 = np.where(ahead, seg[i], seg[j]), np.where(ahead, t, u)
    s2, t2 = np.where(ahead, seg[j], seg[i]), np.where(ahead, u, t)
    assert not np.any(d == 0), f'{n * int(np.sum(d == 0))} self-intersections'
    # P's crossings: each orbit's at s1 + t1, with the curve d sectors on; then each orbit's at s2 + t2, with the curve
    # d sectors back
    K = len(d)
    pos = np.concatenate([s1 + t1, s2 + t2])
    other = curve[np.concatenate([d, (n - d) % n])]
    order = np.roll(np.argsort(pos), -1)         # the walk starts just after crossing 0 and ends with it
    # start between crossings 0 and 1, offset to both sides by a third of the clearance
    mid = 0.5 * (pos[order[-1]] + pos[order[0]])
    s, f = int(mid), mid - int(mid)
    a, b = P[s], P[(s + 1) % M]
    x = a + f * (b - a)
    nrm = np.array([-(b - a)[1], (b - a)[0]]) / np.linalg.norm(b - a)
    # clearance: distance to every segment except this one and its two neighbours. A point's distance from curve[j],
    # and whether it is inside curve[j], are those of the point turned back j sectors from P.
    near = np.abs((np.arange(M) - s + 1) % M) <= 2
    eps = min(float(point_segment_distance(rotate(x, page, -deg[j]), A, B)[(j > 0) | ~near].min())
              for j in range(n)) / 3
    y = np.array([x + eps * nrm, x - eps * nrm])
    lab = inside(np.concatenate([rotate(y, page, -deg[j]) for j in range(n)]), [P]).reshape(n, 2).T @ (1 << curve)
    L, R = int(lab[0]), int(lab[1])
    assert L ^ R == 1 << int(curve[0]), 'the two start points do not straddle exactly this curve'
    bit = 1 << other[order]
    before = np.bitwise_xor.accumulate(bit) ^ bit   # the bits toggled before each crossing of the walk
    face = np.empty((2 * K, 4), np.int64)
    face[order] = np.stack([L ^ before, R ^ before, L ^ before ^ bit, R ^ before ^ bit], 1)
    # every label turned by a sector: curve c's bit moves to the curve a sector on
    turned = sum(((np.arange(1 << n) >> c) & 1) << int(curve[(k[c] + 1) % n]) for c in range(n))
    seen = face[K:].copy()                       # each orbit's crossing on P as its other curve labels it
    for step in range(1, n):
        seen[d >= step] = turned[seen[d >= step]]
    mismatched = n * int(np.sum(np.any(np.sort(face[:K], 1) != np.sort(seen, 1), 1)))
    faces = [face[:K]]
    for _ in range(n - 1):
        faces.append(turned[faces[-1]])
    return n * K, np.concatenate(faces), mismatched


def distinct(F):
    """The rows of F as a set of sets: one row for each different set of labels, its labels in order after a -1 for
    each repeat in it (so rows with repeats, as no face has, compare as Python's frozensets do)."""
    s = np.sort(F, 1)
    s[:, 1:][s[:, 1:] == s[:, :-1]] = -1
    return np.unique(np.sort(s, 1), axis=0)


# ------------------------------------------------------------------ image checking
def png_rgba(data):
    """The pixels (h x w x 4) of an 8-bit RGBA PNG whose rows are all filtered with None or Sub, the kind
    tools/svg2png.mjs writes (resvg filters every row with Sub). Any other PNG fails an assert."""
    assert data[:8] == b'\x89PNG\r\n\x1a\n', 'not a PNG'
    chunks, i = {}, 8
    while i < len(data):
        size, kind = struct.unpack('>I4s', data[i:i + 8])
        chunks[kind] = chunks.get(kind, b'') + data[i + 8:i + 8 + size]
        i += 12 + size
    w, h, depth, color, _, _, interlace = struct.unpack('>IIBBBBB', chunks[b'IHDR'])
    assert (depth, color, interlace) == (8, 6, 0), f'bit depth {depth}, colour type {color}, interlace {interlace}'
    rows = np.frombuffer(zlib.decompress(chunks[b'IDAT']), np.uint8).reshape(h, 1 + 4 * w)
    assert set(rows[:, 0].tolist()) <= {0, 1}, f'row filters {sorted(set(rows[:, 0].tolist()))}'
    px = rows[:, 1:].reshape(h, w, 4).astype(np.int64)
    sub = rows[:, 0] == 1
    px[sub] = np.cumsum(px[sub], axis=1)   # Sub stores each byte minus the same channel's byte a pixel to the left
    return (px % 256).astype(np.uint8)


def ico_pngs(data):
    """The images in an ICO file, as {(width, height): pixels}. Each must be a PNG that png_rgba reads."""
    reserved, kind, count = struct.unpack('<HHH', data[:6])
    assert (reserved, kind) == (0, 1), 'not an ICO file'
    out = {}
    for k in range(count):
        w, h, _, _, _, _, size, offset = struct.unpack('<BBBBHHII', data[6 + 16 * k:22 + 16 * k])
        px = png_rgba(data[offset:offset + size])
        assert px.shape[:2] == (h, w), f'directory says {w}x{h}, PNG is {px.shape[1]}x{px.shape[0]}'
        out[w, h] = px
    return out


# ------------------------------------------------------------------ the quals
QUALS = []


def qual(fn):
    QUALS.append(fn)
    return fn


@qual
def qual_cert_valid():
    """Replicata: python3 venn.py certs; read certs/venn-NN.json for every drawn n.
    Expectata: each cert is the dual map of a simple n-Venn diagram symmetric under rotation."""
    bad = []
    for n in DRAWN:
        r = check_cert(n, read_cert(n))
        bad += [f'n={n}: {k}' for k, v in r.items() if not v]
    return bad


@qual
def qual_cert_provenance():
    """Replicata: sha256sum certs/venn-17.json certs/venn-19.json certs/venn-23.json.
    Expectata: the published SHA-256 of the Lean-verified certs from github.com/dzoba/venn17."""
    return [f'n={n}: sha256 {h[:12]}... is not {want[:12]}...'
            for n, want in PUBLISHED_SHA256.items()
            for h in [hashlib.file_digest(open(cert_path(n), 'rb'), 'sha256').hexdigest()] if h != want]


@qual
def qual_cert_read():
    """Replicata: cert.read(certs/venn-NN.json, n), with which venn.py reads every cert, for each drawn n whose cert
    json.loads can read (all but 23's, 889 MB); then on copies of the 7's with a space after a comma, a label of 8
    characters, a 2 in a label, an apostrophe for a quote mark, a semicolon between faces, a face missing, a face too
    many, "n":8, and a second "faces" key, empty, after the first. Expectata: the faces json.loads gives, in the same
    order; and on each bad copy, an exception, not faces."""
    bad = []
    for n in (2, 3, 5, 7, 11, 13, 17, 19):
        want = np.array([[int(s[::-1], 2) for s in f] for f in json.loads(cert_path(n).read_text())['faces']])
        if not np.array_equal(cert.read(cert_path(n), n), want):
            bad.append(f'n={n}: not the faces json.loads gives')
    t = cert_path(7).read_text()
    first = t.index('["')
    face = t[first:t.index(']', first) + 1]
    for what, copy in (('a space after a comma', t.replace('","', '", "', 1)),
                       ('a label of 8 characters', t.replace('"0000000"', '"00000000"', 1)),
                       ('a 2 in a label', t.replace('1', '2', 1)),
                       ('an apostrophe for a quote mark', t.replace('"1000000"', "'1000000'", 1)),
                       ('a semicolon between faces', t.replace('],[', '];[', 1)),
                       ('a face missing', t.replace(face + ',', '', 1)),
                       ('a face too many', t.replace(face, face + ',' + face, 1)),
                       ('"n":8', t.replace('"n":7', '"n":8', 1)),
                       ('a second "faces" key', t.replace(']]}', ']],"faces":[]}', 1))):
        assert copy != t, what
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / 'c.json').write_text(copy)
            try:
                cert.read(Path(tmp) / 'c.json', 7)
                bad.append(f'with {what}, read without an exception')
            except Exception:
                pass
    return bad


def orbits(part, items):
    """The partition of items by their parts' ids."""
    by = {}
    for x, p in zip(items, part):
        by.setdefault(p, set()).add(x)
    return {frozenset(s) for s in by.values()}


@qual
def qual_crossing_graph():
    """Replicata: cert.Primal, which venn.py lays out in place of the vendored plotter_svg.Primal (2 GB at n = 19, so
    it could not take 23), for n = 7, 11 and 13, and for the 7's cert with its faces listed in reverse order (so that
    the first is not on the outer face). Expectata: the crossing graph plotter_svg.Primal builds from the same
    cert, crossing for crossing (crossings matched by their faces): the same arcs, each on the same curve; the same
    orbits of crossings and of arcs; the same outer face, the same way round or the other (the vendored one's way
    round depends on PYTHONHASHSEED), with the shift to match; and curve 0's crossings in the same order, one way round
    or the other. And plotter_svg.layout() makes the same drawing of either, every crossing within 1e-9 of where it
    should be, but turned (and reflected, if the outer face goes the other way round). And given the 7's faces with
    the first written T, T|A, T, T|B, which is not a square of the cube, cert.Primal raises, as the vendored one does."""
    bad = []
    tmp = tempfile.TemporaryDirectory()
    flipped = Path(tmp.name) / 'venn-07-reversed.json'
    flipped.write_text(json.dumps({'n': 7, 'faces': json.loads(cert_path(7).read_text())['faces'][::-1]},
                                  separators=(',', ':')))
    for n, path in [(n, cert_path(n)) for n in (7, 11, 13)] + [(7, flipped)]:
        F = cert.read(path, n)
        P, Q = cert.Primal(F, n), plotter_svg.Primal(str(path))
        ours = {frozenset(f): v for v, f in enumerate(F.tolist())}
        pi = np.array([ours[frozenset(int(s[::-1], 2) for s in f)] for f in Q.faces])   # Q's crossing u is P's pi[u]
        arcs = lambda src, dst, bit: {(int(a), int(b), int(c)) for a, b, c in zip(src, dst, bit)}
        q_bit = [Q.curve_of[(int(u), int(w))] for u, w in zip(Q.esrc, Q.edst)]
        outer, cycle = pi[Q.outer].tolist(), pi[Q.cycles[0]].tolist()
        outer = outer[outer.index(P.outer[0]):] + outer[:outer.index(P.outer[0])]           # both from P's start
        cycle = cycle[cycle.index(P.cycle0[0]):] + cycle[:cycle.index(P.cycle0[0])]
        reverse = lambda c: c[:1] + c[:0:-1]                       # the same cycle the other way round, same start
        same_way = outer == P.outer
        zq = np.empty(P.V, complex)
        zq[pi] = plotter_svg.layout(Q, iters=300, power=1.0, damp=0.5)
        zq = zq if same_way else np.conj(zq)
        zp = plotter_svg.layout(P, iters=300, power=1.0, damp=0.5)
        r = zp[P.outer[0]] / zq[P.outer[0]]
        for what, ok in (
                ('arcs', arcs(P.esrc, P.edst, P.ebit) == arcs(pi[Q.esrc], pi[Q.edst], q_bit)),
                ('orbits of crossings',
                 orbits(P.orb.tolist(), range(P.V)) == orbits(Q.orb[np.argsort(pi)].tolist(), range(P.V))),
                ('orbits of arcs', orbits(P.eorb.tolist(), [frozenset(e) for e in zip(P.esrc.tolist(), P.edst.tolist())])
                 == orbits(Q.eorb.tolist(), [frozenset(e) for e in zip(pi[Q.esrc].tolist(), pi[Q.edst].tolist())])),
                ('outer face', P.outer in (outer, reverse(outer))),
                ('shift', P.shift == (Q.shift if same_way else n - Q.shift)),
                ('curve 0', P.cycle0.tolist() in (cycle, reverse(cycle))),
                ('layout', abs(abs(r) - 1) < 1e-9 and float(np.abs(zp - r * zq).max()) < 1e-9)):
            if not ok:
                bad.append(f'{path.name}: not the same {what}')
    tmp.cleanup()
    F = cert.read(cert_path(7), 7)
    F[0, 2] = F[0, 0]                     # the first face is T, T|A, T|A|B, T|B: make it T, T|A, T, T|B
    try:
        cert.Primal(F, 7)
        bad.append('a face written T, T|A, T, T|B: built without an exception')
    except Exception:
        pass
    return bad


@qual
def qual_candidate_pairs():
    """Replicata: geom.candidate_pairs(points, 0.02, budget=20000) on 4000 random points in the unit
    square, half of them crowded into a disk of radius 0.01. Expectata: every pair i < j at distance
    at most 0.02, each exactly once, in batches of fewer than 20000 pairs plus the most neighbours
    within 0.02 that any one point has (so memory stays bounded however crowded the points are)."""
    rng = np.random.default_rng(1)
    crowd = 0.5 + 0.5j + 0.01 * np.sqrt(rng.random(2000)) * np.exp(2j * np.pi * rng.random(2000))
    pts = np.concatenate([rng.random((2000, 2)), np.stack([crowd.real, crowd.imag], 1)])
    batches = list(candidate_pairs(pts, 0.02, budget=20000))
    got = np.concatenate([np.stack(b, 1) for b in batches])
    d = np.linalg.norm(pts[:, None] - pts[None], axis=2)
    want = np.argwhere(np.triu(d <= 0.02, 1))
    bad = []
    if len(got) != len(np.unique(got, axis=0)):
        bad.append(f'{len(got) - len(np.unique(got, axis=0))} pairs yielded more than once')
    g, w = {tuple(p) for p in got.tolist()}, {tuple(p) for p in want.tolist()}
    if g != w:
        bad.append(f'{len(w - g)} pairs missing, {len(g - w)} pairs yielded that are not within 0.02 or not i < j')
    most = int((d <= 0.02).sum(1).max())
    if max(len(b[0]) for b in batches) >= 20000 + most:
        bad.append(f'a batch of {max(len(b[0]) for b in batches)} pairs, with at most {most} neighbours a point')
    return bad


@qual
def qual_svg_matches_cert():
    """Replicata: read img/venn-NN.svg, sample its curves, find every crossing, label regions by
    walking each curve. Expectata: no self-intersections, exactly 2^n - 2 crossings, both curves
    through a crossing agree on its four region labels, and the crossings are exactly the cert's faces.
    (The crossings are found in one sector, as drawn_faces says, so this also asserts that the curves are the path
    turned by multiples of 360/n degrees, which qual_svg_symmetric checks too, and that no sampled segment spans 90
    degrees or more about the page centre, as none comes near it.)"""
    bad = []
    for n in DRAWN:
        npts, faces, mismatched = drawn_faces(svg_path(n), n)
        if npts != (1 << n) - 2:
            bad.append(f'n={n}: {npts} crossings drawn, not {(1 << n) - 2}')
            continue
        if mismatched:
            bad.append(f'n={n}: {mismatched} crossings labelled differently by their two curves')
            continue
        drawn, cert = distinct(faces), distinct(read_cert(n))
        both = len(drawn) + len(cert) - len(distinct(np.concatenate([drawn, cert])))
        if not len(drawn) == len(cert) == both:
            bad.append(f'n={n}: {len(drawn) - both} drawn faces not in the cert, '
                       f'{len(cert) - both} cert faces not drawn')
    return bad


@qual
def qual_smoothing_edges():
    """Replicata: lay out and smooth 7 as `python3 venn.py draw 7` does, find the intersection of its curves nearest an
    edge of the sector venn.offenders() looks at (angles 0 to 360/7 degrees about the page centre), and turn curve 0 so
    that this intersection lies 1e-12 or 1e-13 radians to either side of that edge. Expectata: offenders() finds
    nothing wrong, every time, as with the drawing unturned: it is the same drawing turned. (The file's angles have 12
    significant digits, so the copies of an intersection are turned copies of each other only to within about 1e-11
    radians; a check that kept the intersections it found inside the sector would keep one near an edge twice or not
    at all.)"""
    import contextlib, io, venn
    n = 7
    with contextlib.redirect_stderr(io.StringIO()):   # smooth() reports its attempts
        knots, kvid, orb, kof, s = venn.plotter_layout(n)
        ctrl = venn.smooth(n, knots, kvid, orb, kof, s)
    th, c = 2 * math.pi / n, venn.PAGE / 2
    P = sample(ctrl, float(np.median(np.linalg.norm(ctrl[:, 3] - ctrl[:, 0], axis=1))) / 6)[0]
    A = np.concatenate([rotate(P, venn.PAGE, venn.turn(k, n)) for k in range(n)])
    B = np.concatenate([np.roll(rotate(P, venn.PAGE, venn.turn(k, n)), -1, 0) for k in range(n)])
    cid, sid = np.repeat(np.arange(n), len(P)), np.tile(np.arange(len(P)), n)
    reach = 2 * float(np.linalg.norm(B - A, axis=1).max())
    i, j = np.concatenate([np.stack(p, 1) for p in candidate_pairs(0.5 * (A + B), reach)]).T
    hi, _, t, _, _, _ = segment_hits(A, B, cid, sid, np.full(len(A), len(P)), i, j)
    X = A[hi] + t[:, None] * (B[hi] - A[hi])
    angle = np.arctan2(X[:, 1] - c, X[:, 0] - c)
    off = float((angle - np.round(angle / th) * th)[np.argmin(np.abs(angle - np.round(angle / th) * th))])
    bad = [] if len(venn.offenders(n, ctrl, kvid, orb, kof, s)) == 0 else ['unturned: offenders found']
    for eps in (1e-12, -1e-12, 1e-13, -1e-13):
        got = venn.offenders(n, rotate(ctrl, venn.PAGE, math.degrees(eps - off)), kvid, orb, kof, s)
        if len(got):
            bad.append(f'with the intersection {eps:+.0e} rad from the edge, offenders() finds orbits {got.tolist()}')
    return bad


@qual
def qual_svg_reproducible():
    """Replicata: draw each n up to 13 again as `python3 venn.py draw N` does, into a temporary file, under a
    PYTHONHASHSEED other than this process's. Expectata: byte for byte the SVG in img/, so the drawings are what the
    code makes, and depend on nothing else (until the third session the plotter's order of crossings, and so each
    curve's first point, depended on PYTHONHASHSEED)."""
    script = ('import sys, venn; from pathlib import Path; n = int(sys.argv[1]); '
              'venn.write_svg(Path(sys.argv[2]), n, *venn.DRAWER[n](n))')
    bad = []
    with tempfile.TemporaryDirectory() as tmp:
        for n in (2, 3, 5, 7, 11, 13):
            out = Path(tmp) / f'venn-{n:02d}.svg'
            subprocess.run([sys.executable, '-c', script, str(n), str(out)], cwd=HERE, check=True,
                           env={**os.environ, 'PYTHONHASHSEED': '12345'}, capture_output=True)
            if out.read_bytes() != svg_path(n).read_bytes():
                bad.append(f'n={n}: drawn again, not the bytes of {svg_path(n).relative_to(HERE)}')
    return bad


@qual
def qual_png_matches_svg():
    """Replicata: render each img/venn-NN.svg to a PNG as `python3 venn.py draw N` does (tools/svg2png.mjs, resvg,
    venn.PNG_PX pixels wide). Expectata: byte for byte img/venn-NN.png, the picture each card shows (and, for 23, the
    one view of it the site gives)."""
    import venn
    bad = []
    with tempfile.TemporaryDirectory() as tmp:
        for n in DRAWN:
            png = Path(tmp) / f'venn-{n:02d}.png'
            venn.svg2png(svg_path(n), png, venn.PNG_PX)
            if png.read_bytes() != svg_path(n).with_suffix('.png').read_bytes():
                bad.append(f'n={n}: img/venn-{n:02d}.png is not what its SVG renders to')
    return bad


@qual
def qual_svg_symmetric():
    """Replicata: read img/venn-NN.svg for each drawn n. Expectata: it is symmetric by construction, exactly the tree
    venn.py's write_svg() writes: an <svg> with only a version and a viewBox, holding <defs> with one path, <path
    id="curve" d="...">, and then the n curves, <use id="curve-i" href="#curve">, each with just its stroke (fill none,
    a colour #rrggbb, a width over 0, round caps and joins) and a transform rotating that path about the page centre
    by a multiple of 360/n degrees, each multiple from 0 to n - 1 once (to within 1e-9 of a multiple). Nothing else,
    no other attribute or element, so nothing can be drawn but those n rotations. (The drawers make only curve 0, and
    write_svg() the rotations; qual_svg_matches_cert checks the result against the cert.)"""
    svg, style = '{http://www.w3.org/2000/svg}', {'fill', 'stroke', 'stroke-width', 'stroke-linecap', 'stroke-linejoin'}
    bad = []
    for n in DRAWN:
        root = ET.parse(svg_path(n)).getroot()
        kids = list(root)
        tags = [k.tag.removeprefix(svg) for k in kids]
        if root.tag != svg + 'svg' or set(root.attrib) != {'version', 'viewBox'} or tags != ['defs'] + ['use'] * n:
            bad.append(f'n={n}: <{root.tag}> with {sorted(root.attrib)} holding {tags}')
            continue
        defs = list(kids[0])
        if [d.tag for d in defs] != [svg + 'path'] or set(defs[0].attrib) != {'id', 'd'} or defs[0].get('id') != 'curve' \
                or len(defs[0]):
            bad.append(f'n={n}: <defs> holds {[(d.tag, d.attrib.get("id")) for d in defs]}, not just <path id="curve" d>')
        for i, use in enumerate(kids[1:]):
            want = (f'curve-{i}', '#curve', 'none', True, True, 'round', 'round', {'id', 'href', 'transform'} | style, 0)
            got = (use.get('id'), use.get('href'), use.get('fill'),
                   bool(re.fullmatch(r'#[0-9a-f]{6}', use.get('stroke') or '')), float(use.get('stroke-width') or 0) > 0,
                   use.get('stroke-linecap'), use.get('stroke-linejoin'), set(use.attrib), len(use))
            if got != want:
                bad.append(f'n={n}: use {i} has id, href, fill, a colour, a width, caps, joins, attributes, children {got}')
        _, _, degrees = read_svg(svg_path(n))
        multiples = sorted(a * n / 360 for a in degrees)
        if not np.allclose(multiples, range(n), rtol=0, atol=1e-9):
            bad.append(f'n={n}: curves turned by {degrees} degrees, not each multiple of 360/{n} once')
    return bad


class PageParser(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.cards, self.links, self.latin_bad, self.last = [], [], [], None
        self.stack = []
        self.tags = []                                    # (tag, attributes) of every start tag, in order
        self.outside = dict(imgs=[], links=[], text='')   # collects what is in no card, and is never read
        self.card = self.outside                          # the card being parsed

    def handle_comment(self, data):
        self.last = ('comment', data.strip())

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        self.tags.append((tag, a))
        if 'latin' in (a.get('class') or '').split():
            if not (self.last and self.last[0] == 'comment' and self.last[1].startswith('TODO')):
                self.latin_bad.append(f'<{tag} class="{a.get("class")}"> lacks a TODO comment right above it')
        if 'card' in (a.get('class') or '').split():
            self.card = dict(n=a.get('data-n'), regions=a.get('data-regions'),
                             crossings=a.get('data-crossings'), imgs=[], links=[], text='')
            self.cards.append(self.card)
        if tag == 'img':
            self.card['imgs'].append(a.get('src'))
        for k in ('href', 'src'):            # every URL the page links or loads, for qual_local_links and qual_links_live
            if a.get(k):
                self.links.append(a[k])
        if a.get('href'):                    # a card's links are what clicking in it opens; its images are in imgs
            self.card['links'].append(a['href'])
        self.last = ('tag', tag)

    def handle_endtag(self, tag):
        if tag == 'section':
            self.card = self.outside

    def handle_data(self, data):
        if data.strip():
            self.last = ('data', data)
        self.card['text'] += data


def parse_page(name='index.html'):
    p = PageParser()
    p.feed((HERE / name).read_text())
    return p


@qual
def qual_page_cards():
    """Replicata: open index.html. Expectata: one card per prime n from 2 to 23 in order, each stating
    2^n regions and 2^n - 2 crossings (in data attributes and in its visible text), each showing an
    image file that exists in the repo."""
    p = parse_page()
    bad = []
    ns = [int(c['n']) for c in p.cards]
    if ns != list(NS):
        bad.append(f'cards are for n = {ns}, not {list(NS)}')
    for c in p.cards:
        n = int(c['n'])
        digits = re.sub(r'\D', '', c['text'])
        for what, want in (('regions', 1 << n), ('crossings', (1 << n) - 2)):
            if c[what] != str(want) or str(want) not in digits:
                bad.append(f'n={n}: {what} should be {want}')
        if len(c['imgs']) != 1 or not (HERE / c['imgs'][0]).is_file():
            bad.append(f'n={n}: image {c["imgs"]} missing')
    return bad


@qual
def qual_local_links():
    """Replicata: open index.html and view.html and follow every link in them that is neither an absolute URL nor an
    in-page #anchor. Expectata: each names a file in the repo (whatever query string or #anchor follows the name)."""
    return [f'{name}: {u} missing' for name in PAGES for u in sorted(set(parse_page(name).links))
            if not u.startswith(('http', '#')) and not (HERE / urllib.parse.urlsplit(u).path).is_file()]


@qual
def qual_placeholder_provenance():
    """Replicata: shasum -a 256 on each placeholder file. Expectata: byte-identical to the file it was copied
    from (the raw form of its source URL: blob/ changed to raw/)."""
    return [f'n={n}: {path} sha256 {h[:12]}... is not {want[:12]}...'
            for n, (path, want, src) in PLACEHOLDER.items()
            for h in [hashlib.sha256((HERE / path).read_bytes()).hexdigest()] if h != want]


@qual
def qual_placeholder_credited():
    """Replicata: open index.html. Expectata: the card for each n with a placeholder shows it, and links to the
    page it was copied from and to the CC BY 4.0 license, as that license's attribution terms require."""
    cards = {int(c['n']): c for c in parse_page().cards}
    return [f'n={n}: the card does not {what}'
            for n, (path, sha, src) in PLACEHOLDER.items()
            for what, ok in ((f'show {path} as its one image', cards[n]['imgs'] == [path]),
                             (f'link to {src}', src in cards[n]['links']),
                             (f'link to {CC_BY}', CC_BY in cards[n]['links'])) if not ok]


@qual
def qual_placeholder_until_drawn():
    """Replicata: python3 venn.py draw N, for an n with a placeholder. Expectata: no n has both a placeholder and
    a drawing of this site's own (img/venn-NN.svg); once it is drawn, its card shows img/venn-NN.png again and
    its placeholder file and PLACEHOLDER entry go."""
    return [f'n={n}: {svg_path(n).relative_to(HERE)} exists, so placeholder {path} should go'
            for n, (path, sha, src) in PLACEHOLDER.items() if svg_path(n).exists()]


@qual
def qual_icons():
    """Replicata: open index.html and every icon it links. Expectata: favicon.ico at the site root, where browsers
    look for it unbidden, holding 16, 32 and 48 pixel PNGs, the sizes its link gives; img/icon.svg, with a square
    viewBox, linked as an SVG icon; apple-touch-icon.png at the root, 180 pixels square; and a web app manifest
    whose icons are PNGs 192 and 512 pixels square, each the size it says. Those last three are home-screen icons,
    so they are opaque: a home screen shows transparency as black."""
    links = [a for t, a in parse_page().tags if t == 'link']
    bad = [f'no <link> with exactly the attributes {want}' for want in (
        dict(rel='icon', href='favicon.ico', sizes='16x16 32x32 48x48'),
        dict(rel='icon', href='img/icon.svg', type='image/svg+xml'),
        dict(rel='apple-touch-icon', href='apple-touch-icon.png'),
        dict(rel='manifest', href='manifest.webmanifest')) if want not in links]
    tab = sorted(ico_pngs((HERE / 'favicon.ico').read_bytes()))
    if tab != [(16, 16), (32, 32), (48, 48)]:
        bad.append(f'favicon.ico holds images of sizes {tab}')
    box = re.search(r'viewBox="([^"]+)"', (HERE / 'img/icon.svg').read_text()).group(1).split()
    if box[2] != box[3]:
        bad.append(f'img/icon.svg has viewBox {box}')
    icons = json.loads((HERE / 'manifest.webmanifest').read_text())['icons']
    if sorted(i['sizes'] for i in icons) != ['192x192', '512x512'] or {i['type'] for i in icons} != {'image/png'}:
        bad.append(f'the manifest\'s icons are {icons}')
    for path, sizes in [('apple-touch-icon.png', '180x180')] + [(i['src'], i['sizes']) for i in icons]:
        px = png_rgba((HERE / path).read_bytes())
        got = (f'{px.shape[1]}x{px.shape[0]}', int(px[..., 3].min()))
        if got != (sizes, 255):
            bad.append(f'{path} is {got[0]} with least alpha {got[1]}, not {sizes} and opaque')
    return bad


@qual
def qual_link_preview():
    """Replicata: paste https://svenn.dreev.es/ into a chat app or a social site. Expectata: a large-image link
    preview, from tags in index.html: a canonical link and og:url, both the site's root URL; og:type website;
    og:title, the page's title; og:description, its meta description; og:image, an absolute URL on the site of an
    opaque PNG in the repo (some previews show transparency as black) whose actual size, 1200 by 630, is what
    og:image:width and og:image:height say; og:image:alt; and twitter:card summary_large_image."""
    p = parse_page()
    root = f'https://{DOMAIN}/'
    meta = {(k, a[k]): a.get('content') for t, a in p.tags if t == 'meta' for k in ('name', 'property') if k in a}
    og = lambda k: meta.get(('property', 'og:' + k))
    title = html.unescape(re.search(r'<title[^>]*>(.*?)</title>', (HERE / 'index.html').read_text(), re.S).group(1))
    assert (og('image') or '').startswith(root), f'og:image {og("image")!r} is not a URL under {root}'
    px = png_rgba((HERE / og('image')[len(root):]).read_bytes())
    checks = [('the canonical link', [a.get('href') for t, a in p.tags if t == 'link' and a.get('rel') == 'canonical'],
               [root]),
              ('og:url', og('url'), root),
              ('og:type', og('type'), 'website'),
              ('og:title', og('title'), title),
              ('the meta description, present', bool(meta.get(('name', 'description'))), True),
              ('og:description', og('description'), meta.get(('name', 'description'))),
              ('og:image:width and og:image:height', (og('image:width'), og('image:height')), ('1200', '630')),
              ('og:image\'s actual width and height', (px.shape[1], px.shape[0]), (1200, 630)),
              ('og:image\'s least alpha', int(px[..., 3].min()), 255),
              ('og:image:alt, present', bool(og('image:alt')), True),
              ('twitter:card', meta.get(('name', 'twitter:card')), 'summary_large_image')]
    return [f'{what} is {got!r}, not {want!r}' for what, got, want in checks if got != want]


@qual
def qual_page_english():
    """Replicata: open the page in Safari, or in anything else built on WebKit. Expectata: every u is drawn as a u.
    EB Garamond's locl feature for the Latin language draws u as v (and U as V), WebKit applies it even under
    font-feature-settings: "locl" 0, and the page said lang="la", so on 2026-10-06 Safari showed "Grünbavm" and
    "congrvent". The pages are in English, so each one's one lang attribute is <html lang="en">."""
    return [f'{name}: lang attributes {langs}, not just <html lang="en">' for name in PAGES
            for langs in [[(t, a['lang']) for t, a in parse_page(name).tags if 'lang' in a]] if langs != [('html', 'en')]]


@qual
def qual_page_latin():
    """Replicata: read index.html and view.html. Expectata: every element of class latin (UI copy, which starts out in
    Latin per AGENTS.md rule 7) has a TODO comment right above it recapping the intended English."""
    return [f'{name}: {bad}' for name in PAGES for bad in parse_page(name).latin_bad]


_browser = {}


def browser(check):
    """The problems tools/browser_quals.mjs found with view.html, the viewer, in one of its checks, in Chromium, WebKit
    or Firefox. All the checks run together, on first use. They need `cd tools && npm ci`, and Playwright's builds of
    the three browsers (`cd tools && npx playwright install` if they are not already installed)."""
    if 'run' not in _browser:   # kept even when it failed, so that a failing run isn't repeated by every qual
        _browser['run'] = subprocess.run(['node', str(HERE / 'tools' / 'browser_quals.mjs'), *map(str, VIEWED)],
                                         capture_output=True, text=True)
    run = _browser['run']
    assert run.returncode == 0, run.stderr[-3000:]
    return json.loads(run.stdout)[check]


@qual
def qual_viewer_linked():
    """Replicata: on index.html, click the picture on each card whose drawing is this site's own. Expectata: it opens
    view.html?n=N, the viewer."""
    cards = {int(c['n']): c for c in parse_page().cards}
    return [f'n={n}: the card links to {cards[n]["links"]}' for n in VIEWED if f'view.html?n={n}' not in cards[n]['links']]


@qual
def qual_png_only():
    """Replicata: on index.html, click the picture on the card for each n whose drawing view.html can't show (23, with
    8,388,606 crossings). Expectata: it opens the PNG the card shows, img/venn-NN.png."""
    cards = {int(c['n']): c for c in parse_page().cards}
    return [f'n={n}: the card shows {cards[n]["imgs"]} and links to {cards[n]["links"]}' for n in PNG_ONLY
            for png in [f'img/venn-{n:02d}.png'] if cards[n]['imgs'] != [png] or png not in cards[n]['links']]


@qual
def qual_viewer_fit():
    """Replicata: open view.html?n=N for every n it shows, in Chromium, WebKit and Firefox, in a 1200 by 800 window.
    Expectata: for each n, the drawing's square page fits the space below the controls along the top and clear of
    the swatches, which stand in a row along the bottom or, in a landscape window like this one, in a column along the
    right edge; it is centred in that space, so no control covers it; each curve is a
    path of its own, path i the file's one path turned as its use i says (every coordinate within 0.001) in use i's
    colour, whose line is as wide on screen as the SVG's own stroke-width makes it at that size, and doesn't scale
    (vector-effect: non-scaling-stroke), so lines keep that width when zoomed in and bundles of nearly parallel curves
    come apart."""
    return browser('fit')


@qual
def qual_viewer_curves():
    """Replicata: open view.html?n=7; click the first swatch, then the third, then the third again, then the
    seventh; click the second and press Escape. Expectata: one swatch per curve, in its curve's colour. Each swatch
    shows the curves up to and including its own, so that clicking them in order adds the curves one at a time:
    the first shows curve 0 alone (counting from 0, as the SVG's ids curve-0 to curve-6 do), the third curves 0 to 2,
    clicking it again changes nothing, and the seventh, like Escape, shows all seven, as on opening. Exactly the
    swatches of the curves shown are pressed (aria-pressed) and in their curves' colours; the others are faded by their
    fill, not their opacity, which would fade their focus rings too."""
    return browser('curves')


@qual
def qual_viewer_wheel():
    """Replicata: in view.html?n=7, point at a spot and turn the wheel 400 pixels up; then hold ctrl and turn it 100
    pixels down, which is how browsers report a trackpad pinch; then turn a wheel that counts in lines 25 lines up,
    and one that counts in pages half a page up; then zoom in far. Expectata: the drawing zooms in by a factor of e,
    then out by e, then in by e twice (a line counting as 16 pixels, a page as the window's height), each time about
    the spot pointed at, which stays put; and the lines stay as wide on screen as before zooming."""
    return browser('wheel')


@qual
def qual_viewer_drag():
    """Replicata: in view.html?n=7, drag the drawing 120 pixels right and 80 down; point at a curve; drag from the
    middle of the top bar and from the first end of the swatches, beside them. Expectata: the point grabbed
    moves with the pointer, ending under it, each time; the scale doesn't change. The curves never take the pointer:
    it reaches the stage beneath them, since hit-testing 17's or 19's strokes on every move takes seconds; nor do the
    bars, between their controls."""
    return browser('drag')


@qual
def qual_viewer_pinch():
    """Replicata: in view.html?n=7, put two fingers down 120 pixels apart and move one of them away from the other
    until they are 240 apart. Expectata: the drawing zooms in by 2, the point under the finger that stayed put staying
    under it. The page has touch-action: none, so that a pinch that starts over the controls doesn't zoom the page."""
    return browser('pinch')


@qual
def qual_viewer_mouse():
    """Replicata: in view.html?n=7, drag with the right button, then with the middle one; then press the left button
    and move the mouse with no button down, as when the release never arrives (after a context menu, say).
    Expectata: the drawing doesn't move."""
    return browser('mouse')


@qual
def qual_viewer_controls():
    """Replicata: in view.html?n=7, turn the wheel 400 pixels up over the + button; hold ctrl and turn it 100 pixels
    down over the first swatch; turn it 400 pixels up over the number. Expectata: each zooms the drawing as it would
    over the drawing itself (by e, by 1/e, by e), about the spot pointed at, not the page."""
    return browser('controls')


@qual
def qual_viewer_cancel():
    """Replicata: in view.html?n=7, turn the wheel over the drawing, over + with ctrl held (a trackpad pinch), and over
    the swatches; send gesturestart and gesturechange (Safari's trackpad pinch) over +. Expectata: the viewer cancels
    each of them (preventDefault), which keeps the browser from zooming or scrolling the page itself."""
    return browser('cancel')


@qual
def qual_viewer_gesture():
    """Replicata: in Safari (WebKit), pinch on a trackpad over view.html?n=7 to twice the size, which Safari reports
    as gesturestart and gesturechange events carrying the scale so far from 1; pinch again to twice the size; then
    pinch on a touchscreen, which Safari reports as touch pointers and gesture events both. Expectata: each trackpad
    pinch zooms in by 2 about the spot pinched (4 in all); the touchscreen's gesture events add nothing to what its
    pointers do."""
    return browser('gesture')


@qual
def qual_viewer_settle():
    """Replicata: open the viewer for the largest n (drawing 19 anew takes a tenth to half a second); drag the drawing
    as a hand does, a move every 16 ms, then turn the wheel and pinch the same way, then stop. Expectata: meanwhile it
    moves without being drawn anew: the SVG keeps its viewBox and a CSS transform on the picture already drawn (the
    div #picture, which has will-change: transform) moves it, which browsers do cheaply. Within 2 seconds of the last
    event it is drawn anew at the new view, sharp again, where the moved picture showed it (each point within half a
    pixel, the same scale) with lines as wide as at fit, and the picture's transform back to the identity. (The
    identity, not none: from none, WebKit's next gesture began with a 115-140 ms frame at n = 19.)"""
    return browser('settle')


@qual
def qual_viewer_slow():
    """Replicata: in view.html?n=7, drag the drawing, a move a frame; then let one frame take 400 ms (as moving 19's
    picture does in Firefox when it scales), then let go. Expectata: no note during the quick frames; after the slow
    one, a note saying that moving is slow here and the drawing sharpens when the view keeps still; the note gone once
    the drawing has been drawn anew."""
    return browser('slow')


@qual
def qual_viewer_dblclick():
    """Replicata: in view.html?n=7, double-click a spot. Expectata: the drawing zooms in by 2 about that spot."""
    return browser('dblclick')


@qual
def qual_viewer_buttons():
    """Replicata: in view.html?n=7, click +, then − twice; drag; click the fit button. Expectata: + zooms in by 2
    and − out by 2, about the centre of the space the drawing fits on opening (between the controls along the top and
    the swatches); fit puts the drawing back as it was on opening."""
    return browser('buttons')


@qual
def qual_viewer_keys():
    """Replicata: in view.html?n=7, press +, then ctrl+0 and cmd+0, then - twice, then 0, then =, then alt+0, then
    0 and the four arrows. Expectata: + (or =, the same key without shift) and - zoom in and out by 2 about the
    centre of the space the drawing fits on opening; 0 fits the drawing as on opening; ctrl+0, cmd+0 and alt+0, the
    browser's own keys, do nothing to the drawing; each arrow pans a tenth of the side of the drawing as it fits on
    opening its way, so the point that was that far from the centre in its direction is now at the centre."""
    return browser('keys')


@qual
def qual_viewer_limits():
    """Replicata: in view.html?n=7, in a 1200 by 800 window, click − six times; then turn the wheel far up.
    Expectata: zooming out stops at half the size that fits the window, and zooming in stops at 1000 times it (where a
    pixel is about 0.07 units of the SVG's 51200-unit page, still coarser than the 0.001 the SVG gives coordinates to)."""
    return browser('limits')


@qual
def qual_viewer_resize():
    """Replicata: in view.html?n=7 in a 1200 by 800 window, click +, then make the window 800 by 600. Expectata: the
    point at the centre of the space the drawing fits stays at that space's centre, and the drawing keeps its size
    relative to that space (twice the size that fits). Then make it 1200 by 100, too short for the controls: the drawing
    still shows, at least half the window's shorter side across (overlapping the controls), never vanishing."""
    return browser('resize')


@qual
def qual_viewer_links():
    """Replicata: open view.html?n=7. Expectata: its title is "7 · " then the list's title; the back arrow links to
    index.html#n7, the card on the list; the SVG link to img/venn-07.svg, the bare file; and the drawing is an image
    to a screen reader (role img) with a label that says n."""
    return browser('links')


@qual
def qual_viewer_loading():
    """Replicata: open view.html?n=7 while img/venn-07.svg is slow to arrive, and click +. Expectata: meanwhile the
    viewer shows img/venn-07.png, the card's picture, placed as the drawing would be and zoomed by + as it would be,
    a line saying that the full drawing is on its way (visible, as Playwright judges it), and seven swatches, all
    disabled; once the SVG arrives, its seven curves replace the picture, the line goes, and the swatches work."""
    return browser('loading')


@qual
def qual_viewer_error():
    """Replicata: open view.html?n=4, for which there is no drawing; then view.html?n=abc, view.html?n= and
    view.html?n=10000000. Expectata: for n=4, a visible error saying that img/venn-04.svg could not be loaded, ending
    with the server's status in brackets, "(404)" (status text alone would be empty over HTTP/2, as GitHub Pages
    serves it), four swatches, all disabled, no loading line and no broken picture in the drawing area; for the
    others, an error within 3 seconds and no swatches."""
    return browser('error')


@qual
def qual_viewer_phone():
    """Replicata: open the viewer for the largest n on phones with touch screens, 375 by 667, 320 by 568, and 844 by
    390 (one on its side); tap +.
    Expectata: the controls (the back arrow and number; the SVG link and zoom buttons; the swatches) all fit in the
    window without overlapping each other, the page doesn't scroll, and every button and link is at least 44 by 44
    pixels, Apple's guideline for something to touch. After the tap, + looks as it did before it (no hover look stays
    behind, as it does on touch screens unless hover styles are kept to devices that can hover). On the phone on its
    side the swatches stand in a column along the right edge and the drawing fits in at least 300 pixels."""
    return browser('phone')


@qual
def qual_shared_style():
    """Replicata: read index.html and view.html. Expectata: both link site.css, which holds what they share (the
    colours, the font, the base rules), and neither defines any of site.css's colours itself."""
    tokens = re.findall(r'--([\w-]+):', (HERE / 'site.css').read_text())
    bad = [f'{name} does not link site.css' for name in PAGES
           if not any(t == 'link' and a.get('rel') == 'stylesheet' and a.get('href') == 'site.css'
                      for t, a in parse_page(name).tags)]
    return bad + [f'{name} defines --{token} itself' for name in PAGES for token in tokens
                  if f'--{token}:' in (HERE / name).read_text()] + ([] if tokens else ['site.css defines no colours'])


@qual
def qual_pages_config():
    """Replicata: cat CNAME; ls .nojekyll. Expectata: GitHub Pages serves the repo as-is at svenn.dreev.es."""
    bad = []
    if (HERE / 'CNAME').read_text().strip() != DOMAIN:
        bad.append('CNAME is not ' + DOMAIN)
    if not (HERE / '.nojekyll').is_file():
        bad.append('.nojekyll missing')
    return bad


@qual
def qual_links_live():
    """Replicata: request every absolute URL that index.html links to. Expectata: HTTP 200 for each,
    after redirects."""
    bad = []
    for url in sorted({u for u in parse_page().links if u.startswith('http')}):
        req = urllib.request.Request(url, headers={'User-Agent': 'svenn-quals'})
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                status = resp.status
        except Exception as e:  # report every failure kind as a FAIL line rather than crashing the run
            status = repr(e)
        if status != 200:
            bad.append(f'{url} -> {status}')
    return bad


def main():
    words = sys.argv[1:]
    failed = 0
    for fn in QUALS:
        if words and not any(w in fn.__name__ for w in words):
            continue
        try:
            problems = fn()
        except Exception as e:
            problems = [f'{type(e).__name__}: {e}']
        status = 'PASS' if not problems else 'FAIL'
        print(f'{status} {fn.__name__}')
        if problems:
            failed += 1
            print('  ' + fn.__doc__.strip().replace('\n', '\n  '))
            print('  Resultata:')
            for p in problems[:20]:
                print('    ' + p)
    print(f'{failed} failing')
    sys.exit(failed)


if __name__ == '__main__':
    main()
