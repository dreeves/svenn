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
  canvas  in a browser qual of the viewer's canvas (CANVAS below), the
         canvas the viewer draws the curves on, the first in #stage; every
         viewer also has a canvas of its own for the shading, in #region.
  reference  for a browser qual of the viewer's canvas (CANVAS below), the
         curves of img/venn-NN.svg as the qual draws them itself, on a canvas
         of its own the size of the viewer's: curve 0's path data handed to
         the browser's Path2D, stroked once for each curve shown, turned as
         that curve's use says, in its colour, at the view the qual expects
         (from its own arithmetic, not the viewer's), with lines as wide on
         screen as at fit.
  matches  the viewer's canvas matches its reference when its pixels differ
         from the reference's by at most a fifth of the reference's ink (the
         summed difference of their colours, each weighted by its alpha,
         after scaling the canvas's alpha to the reference's total), and its
         total ink (alpha) is within a fifth of the reference's.
  shading  the region of the drawing that view.html shades, in site.css's
         --line colour, beneath the curves: the one inside every curve whose
         checkbox is checked and outside every other, i.e. the region whose
         label has bit i set iff checkbox i is checked (with none checked,
         the region outside every curve).
  probe  for a browser qual of the shading, a point of the drawing's page
         at least half a line's width plus 1.5 pixels on screen from every
         curve of img/venn-NN.svg (from its centreline; lines are as wide on
         screen at any zoom as at fit), whose label the qual finds itself
         from the file: the point is inside curve i iff, turned back by the
         angle of use i, it is inside curve 0, iff a ray from it crosses
         curve 0 an odd number of times. A probe is shaded when a screenshot
         shows it in --line, unshaded when it shows it in --paper (each
         channel within 8).
  turn   (as in venn.py) a rotation about the page's centre. The turn
         button turns the drawing by 1/n of a full turn anticlockwise on
         screen: -360/n degrees in SVG's rotate(), whose positive angles turn
         clockwise on screen. That carries curve i, which use i turns by a_i
         degrees, onto the curve j whose a_j is a_i - 360/n (mod 360): curve
         i lands on curve j.
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

import cert
from crossings import crossings, cut, point, samples, segdist
from geom import nets, rotate

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
# n whose card opens view.html on this site's own drawing
VIEWED = tuple(n for n in DRAWN if n not in PLACEHOLDER)
# n whose drawing view.html draws on a canvas, not as SVG paths: 23's curves have 729,449 spans each, too many for SVG
# paths (see view.html's canvasRenderer())
CANVAS = (23,)
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


def drawn_faces(path, n):
    """Find every crossing of the curves of the drawing at path, exactly (crossings.py: certified, not sampled), and
    label the regions around each by walking each curve through its crossings, toggling the labels of the regions on
    its two sides.

    Curve i is the SVG's one path turned by k_i sectors, each k from 0 to n - 1 once (asserted, to within 1e-9 of a
    sector). So the drawing is the path P and n - 1 turned copies of it, and its crossings come in orbits (a crossing
    and its n - 1 turns by multiples of a sector). crossings() gives each orbit once, as a crossing of P with the copy
    d sectors on, 1 <= d <= n/2, at positions span + t along P and along the copy. Each orbit has two crossings on P
    itself: that one, and that one turned back d sectors, which is on the copy d sectors back. Walking P through all of
    them is walking every curve, turned; turning a crossing turns its labels too, each curve's bit moving to the curve
    as many sectors on. Returns what walking every curve gives: the number of crossings (n per orbit); their faces (each
    orbit's turned n ways); and how many crossings the two curves through them label differently. Contacts (places
    where crossings() could certify neither a crossing nor its absence) and self-intersections fail asserts, counted
    over the whole drawing. Still sampled: the labels the walk starts from, those of two points either side of P
    between two crossings, by even-odd tests against polylines through samples of every curve."""
    base, page, degrees = read_svg(path)
    assert len(degrees) == n, (len(degrees), n)
    turns = np.array(degrees) * n / 360
    k = np.round(turns).astype(np.int64) % n
    assert np.allclose(turns, np.round(turns), rtol=0, atol=1e-9) and sorted(k.tolist()) == list(range(n)), degrees
    curve = np.argsort(k)                        # curve[j] is the path turned by j sectors
    deg = np.array(degrees)[curve]               # by deg[j] degrees, as the file says
    X, C = crossings(base, page, deg)
    assert len(C) == 0, f'{n * len(C)} contacts'
    d = X[:, 0].astype(np.int64)
    assert not np.any(d == 0), f'{n * int(np.sum(d == 0))} self-intersections'
    # P's crossings: each orbit's at span + t along P, with the curve d sectors on; then each orbit's at span + t along
    # the copy, with the curve d sectors back
    K = len(d)
    pos = np.concatenate([X[:, 1] + X[:, 2], X[:, 3] + X[:, 4]])
    other = curve[np.concatenate([d, (n - d) % n])]
    order = np.roll(np.argsort(pos), -1)         # the walk starts just after crossing 0 and ends with it
    # start between crossings 0 and 1, at x on P, offset to both sides by a third of the clearance, judged against the
    # polyline through P's samples (segment s of it runs from sample s to sample s + 1)
    mid = 0.5 * (pos[order[-1]] + pos[order[0]])
    span, t = samples(base, 6.0, 4)
    A = point(base[span], t)
    B, M = np.roll(A, -1, 0), len(A)
    x = point(base[[int(mid)]], np.array([mid - int(mid)]))[0]
    s = int(np.searchsorted(span + t, mid)) - 1
    a, b = A[s % M], B[s % M]
    nrm = np.array([-(b - a)[1], (b - a)[0]]) / np.linalg.norm(b - a)
    # clearance: distance to every segment except this one and its two neighbours. A point's distance from curve[j],
    # and whether it is inside curve[j], are those of the point turned back j sectors from P.
    near = np.abs((np.arange(M) - s + 1) % M) <= 2
    eps = min(float(segdist(rotate(x, page, -deg[j]), A, B)[(j > 0) | ~near].min())
              for j in range(n)) / 3
    y = np.array([x + eps * nrm, x - eps * nrm])
    lab = inside(np.concatenate([rotate(y, page, -deg[j]) for j in range(n)]), [A]).reshape(n, 2).T @ (1 << curve)
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


# ------------------------------------------------------------------ constructed drawings, for crossings()
FEATURE = 8000.0   # how far out from the page centre, along the x axis, a constructed drawing has its feature


def u(degrees): return np.array([math.cos(math.radians(degrees)), math.sin(math.radians(degrees))])


def line(p, q):
    """A straight span from p to q, its handles a third of the way."""
    p, q = np.asarray(p, float), np.asarray(q, float)
    return np.stack([p, p + (q - p) / 3, p + 2 * (q - p) / 3, q])[None]


def flat(p, q):
    """A straight span from p to q with zero handles (P1 = P0, P2 = P3), as the drawings' straight arcs have."""
    p, q = np.asarray(p, float), np.asarray(q, float)
    return np.stack([p, p, q, q])[None]


def poly(points, span=line):
    return np.concatenate([span(p, q) for p, q in zip(points[:-1], points[1:])])


def circle(o, r, a0, a1, most=30.0):
    """Cubic spans along the circle of radius r about o from angle a0 to a1 (degrees, either way round), each over at
    most `most` degrees."""
    k = max(1, math.ceil(abs(a1 - a0) / most))
    out = []
    for b0, b1 in zip(np.linspace(a0, a1, k + 1)[:-1], np.linspace(a0, a1, k + 1)[1:]):
        h = 4 / 3 * math.tan(math.radians(b1 - b0) / 4) * r
        p0, p3 = o + r * u(b0), o + r * u(b1)
        out.append(np.stack([p0, p0 + h * u(b0 + 90), p3 - h * u(b1 + 90), p3]))
    return np.array(out)


def parabola(lift, w=48.0, h=48.0):
    """y = h (x / w)^2 + lift from x = -w to w as one span, its control points integers when w / 3, h / 3 and lift
    are."""
    return np.array([[(-w, h + lift), (-w / 3, -h / 3 + lift), (w / 3, -h / 3 + lift), (w, h + lift)]], float)


def connector(p, r, exit, way):
    """The way out from end p of one of a feature's arcs (in the feature's local coordinates, under 100 from its point):
    out from the point to 100, out to r, round the circle of radius r about the point to angle `exit` (counterclockwise
    for way 1, clockwise for -1), out to 200, and on to 300 above or below."""
    th = math.degrees(math.atan2(p[1], p[0]))
    e = th + way * (way * (exit - th) % 360)
    end = 200 * u(e)
    return np.concatenate([line(p, 100 * u(th)), line(100 * u(th), r * u(th)), circle(np.zeros(2), r, th, e),
                           line(r * u(e), end), line(end, (end[0], math.copysign(300.0, end[1])))])


def feature(A, B, page):
    """Curve 0 of a three-curve drawing (copies turned the SVG's 120 and 240 degrees) holding one feature: arc A of
    curve 0 near the point FEATURE out along the x axis from the page centre, and arc B that copy 1 is to have there,
    put into curve 0 turned back 120 degrees. The arcs are in the feature's local coordinates (about the point, x
    outward, y the way angles grow), each from its left end (x < 0) to its right end (x > 0), under 100 from the point.
    Curve 0 leaves A's ends downward, toward smaller angles, and copy 1 leaves B's upward, by connector(), A's round a
    circle of radius 150 and B's of 125: so the connectors cross once, at a right angle, for each end of A that is
    above B's end on the same side, as seen from the point, and nowhere else. Then curve 0 goes round circles about the
    page centre to B's ends, turned back."""
    assert [q[0] < 0 for q in (A[0, 0], A[-1, 3], B[0, 0], B[-1, 3])] == [True, False, True, False]
    c = page / 2
    F = np.array([c + FEATURE, c])
    AL, AR = connector(A[0, 0], 150.0, 255.0, 1), connector(A[-1, 3], 150.0, -75.0, -1)
    BL, BR = connector(B[0, 0], 125.0, 105.0, -1), connector(B[-1, 3], 125.0, 75.0, 1)
    here = lambda N: N + F                                  # local coordinates to the page's
    back = lambda N: rotate(N + F, page, -120.0)            # copy 1's local coordinates to curve 0's on the page
    angle = lambda q: math.degrees(math.atan2(q[1] - c, q[0] - c))
    ends = [(here(AR)[-1, 3], back(BR)[-1, 3]), (back(BL)[-1, 3], here(AL)[-1, 3])]
    right, left = (circle(np.array([c, c]), float(np.hypot(*(q0 - c))), angle(q0), angle(q1), 10.0) for q0, q1 in ends)
    for arc, (q0, q1) in zip((right, left), ends):          # from q0 to q1 exactly
        assert np.abs(arc[0, 0] - q0).max() < 1e-6 and np.abs(arc[-1, 3] - q1).max() < 1e-6
        arc[0, 0], arc[-1, 3] = q0, q1
    rev = lambda N: N[::-1, ::-1]                           # the same spans the other way
    N = np.concatenate([here(A), here(AR), right, rev(back(BR)), rev(back(B)), back(BL), left, rev(here(AL))])
    assert np.array_equal(N[:, 3], np.roll(N[:, 0], -1, 0)), 'not one closed curve'
    return N


def corners(off, alpha, turn_a, turn_b, phi, page):
    """feature(): A turns turn_a degrees at the point, B turns turn_b degrees at a knot off away from it in direction
    phi, arriving alpha degrees round from A; both of two straight spans with zero handles, as straight arcs are."""
    o = off * u(phi)
    return feature(poly([-50 * u(0), (0.0, 0.0), 50 * u(turn_a)], flat),
                   poly([o - 50 * u(alpha), o, o + 50 * u(alpha + turn_b)], flat), page)


# Corners: (alpha, turn_a, turn_b) -> {phi: crossings of curve 0 with copy 1}, the connectors' 1 or 2 included. Here
# same turns cross once, or three times when B's knot is off A's in a direction between 0 and turn_a degrees (B
# crossing A's first span, its second, and its second again); opposite turns cross twice when B's knot is above A's,
# and not at all when it is below.
CORNERS = {(3.0, 20.0, 20.0): {37.0: 2, 217.0: 2, 100.0: 2, 300.0: 2},
           (0.1, 20.0, 20.0): {37.0: 2, 217.0: 2, 100.0: 2, 300.0: 2},
           (0.01, 5.0, 5.0): {37.0: 2, 217.0: 2},
           (1.0, 60.0, 60.0): {37.0: 4, 217.0: 2},
           (0.1, 20.0, -20.0): {37.0: 4, 217.0: 2, 100.0: 4, 300.0: 2}}


@qual
def qual_crossings_known():
    """Replicata: crossings.crossings() on constructed curves: the conics venn.py draws for n = 2, 3 and 5; and
    three-curve drawings, each made by feature() to hold one feature (copy 1's arc near curve 0's): straight spans
    crossing at the middles of both; a parabola passing 1e-6 above a straight span, touching it, and dipping 1e-8
    below it; a sharper one dipping 1e-6 below it, crossing it twice 2.8e-5 apart; a cubic crossing a straight span
    three times; two curves turning at knots (corners, with zero handles, as the drawings' straight arcs have) 1e-9,
    1e-8, 1e-7 and 1e-6 apart, crossing at 0.01 to 3 degrees; corners 1e-6 apart pointing at each other; a corner and
    a straight span passing 1e-6 from it, inside the corner and outside it; two curves smooth through knots at one
    point, crossing at 1e-3 degrees there; a curve with a loop 1, or 1e-4, across; a curve passing 1e-6 from itself,
    touching itself exactly, and doubling back 1e-6 from itself for 100 units (a hairpin); a span whose control points
    cross over, which has a cusp; a straight span lying along curve 0's for 70 units; and the first of those drawings
    with a span of length zero added, or with its last span ending 50 units from its first point. Expectata: for each,
    as many crossings of curve 0 with itself and with each copy as listed here, one per orbit (for n = 2, one of the two
    crossings of the circles, which are turns of each other), and no contact, except that where curves touch, at the
    cusp and along the overlap there is a contact and no crossing is claimed; the straight spans' crossing at t = 1/2 on
    both; and for the span of length zero and for the curve that does not close, an AssertionError. (Each count was
    checked with an exact rational verifier, which was undecided only at touches and at the crossing where both curves
    have knots.)"""
    import venn
    page = venn.PAGE
    deg = lambda n: [venn.turn(k, n) for k in range(n)]
    plain = line((-50, 80), (50, 80))           # copy 1's arc where the feature is curve 0 with itself
    lines = feature(line((-48, 0), (48, 0)), line(50 * u(240), 50 * u(60)), page)

    def itself(lift):
        """Along y = 0 through the point, round, and back as the parabola, right to left."""
        P = parabola(lift)[:, ::-1]
        return feature(np.concatenate([line((-80, 0), (55, 0)), poly([(55, 0), (62, 25), P[0, 0]]), P,
                                       poly([P[-1, 3], (-48, 62), (62, 62)])]), plain, page)

    def loop(w):
        return feature(np.concatenate([line((-80, 0), (-w, 0)), np.array([[(-w, 0), (2 * w, w), (-2 * w, w), (w, 0)]]),
                                       line((w, 0), (80, 0))]), plain, page)
    tilt = np.array([[math.cos(math.radians(1e-3)), math.sin(math.radians(1e-3))],
                     [-math.sin(math.radians(1e-3)), math.cos(math.radians(1e-3))]])
    tilted = np.array([(-60, -4), (-40, -1.5), (-20, 0), (0, 0), (20, 0), (40, -1), (60, -3)], float) @ tilt
    near = lambda sign: np.array([0.0, sign * 1e-6 / math.cos(math.radians(15))])
    sharp = parabola(-1e-6, 1e-3, 5e-3)        # y = 5000 x^2 - 1e-6, crossing y = 0 at x = +-1.4e-5
    # (what, curve 0, degrees of its copies, crossings with each copy d = 0 .. n // 2, a contact)
    cases = [(f'conics for n = {n}', venn.draw_conics(n)[0], deg(n), want, False)
             for n, want in ((2, (0, 1)), (3, (0, 2)), (5, (0, 4, 2)))]
    cases += [(what, N, deg(3), want, touch) for what, N, want, touch in (
        # 1 at the middles, and 1 where the connectors cross
        ('straight spans crossing at both their middles', lines, (0, 2), False),
        ('a parabola 1e-6 above a straight span', feature(line((-48, 0), (48, 0)), parabola(1e-6), page), (0, 0),
         False),
        ('a parabola touching a straight span (to within the turning\'s rounding)',
         feature(line((-48, 0), (48, 0)), parabola(0.0), page), (0, 0), True),
        ('a parabola dipping 1e-8 below a straight span, crossing it twice 1.4e-3 apart',
         feature(line((-48, 0), (48, 0)), parabola(-1e-8), page), (0, 2), False),
        ('a sharp parabola dipping 1e-6 below a straight span, crossing it twice 2.8e-5 apart',
         feature(line((-48, 0), (48, 0)), np.concatenate([line((-48, 48), sharp[0, 0]), sharp,
                                                          line(sharp[0, 3], (48, 48))]), page), (0, 2), False),
        # 3, and 1 where the connectors cross
        ('a cubic crossing a straight span three times',
         feature(line((-48, 0), (48, 0)), np.array([[(-48, -20), (-16, 40), (16, -40), (48, 20)]], float), page),
         (0, 4), False),
        ('corners 1e-6 apart pointing at each other',
         feature(poly([(-50, -50), (0, 0), (50, -50)], flat), poly([(-50, 50), (0, 1e-6), (50, 50)], flat), page),
         (0, 0), False),
        # 2 or none, and 2 where the connectors cross
        ('a corner and a straight span 1e-6 from it, inside the corner',
         feature(poly([(-50, 0), (0, 0), 50 * u(30)], flat), line(near(1) - 50 * u(15), near(1) + 50 * u(15)), page),
         (0, 4), False),
        ('a corner and a straight span 1e-6 from it, outside the corner',
         feature(poly([(-50, 0), (0, 0), 50 * u(30)], flat), line(near(-1) - 50 * u(15), near(-1) + 50 * u(15)), page),
         (0, 2), False),
        # 2 (at the knots, and 0.007 on), and 2 where the connectors cross
        ('curves smooth through knots at one point, crossing at 1e-3 degrees',
         feature(np.array([[(-60, 3), (-40, 1), (-20, 0), (0, 0)], [(0, 0), (20, 0), (40, 2), (60, 6)]], float),
                 np.stack([tilted[0:4], tilted[3:7]]), page), (0, 4), False),
        ('a loop 1 across', loop(1.0), (1, 0), False),
        ('a loop 1e-4 across', loop(1e-4), (1, 0), False),
        ('a curve passing 1e-6 from itself', itself(1e-6), (0, 0), False),
        ('a curve touching itself exactly', itself(0.0), (0, 0), True),
        ('a hairpin', feature(np.concatenate([
            line((-80, 0), (50, 0)), np.array([[(50, 0), (50 + 1e-6, 0), (50 + 1e-6, 1e-6), (50, 1e-6)]]),
            line((50, 1e-6), (-50, 2e-6)), poly([(-50, 2e-6), (-50, 40), (70, 40)])]), plain, page), (0, 0), False),
        ('a span with a cusp', feature(np.array([[(-50, -50), (50, 50), (-50, 50), (50, -50)]], float), plain, page),
         (0, 0), True),
        ("a straight span lying along curve 0's for 70 units",
         feature(line((-48, 0), (48, 0)), poly([(-60, 30), (-35, 0), (35, 0), (60, 30)], flat), page), (0, 0), True))]
    cases += [(f'corners {off:g} apart, crossing at {alpha:g} degrees, turning {ta:g} and {tb:g}, knots in direction '
               f'{phi:g}', corners(off, alpha, ta, tb, phi, page), deg(3), (0, want[phi]), False)
              for off in (1e-9, 1e-8, 1e-7, 1e-6) for (alpha, ta, tb), want in CORNERS.items() for phi in (37.0, 217.0)]
    bad = []
    for what, N, degrees, want, touch in cases:
        try:
            X, C = crossings(N, page, degrees)
        except Exception as e:   # reported as this case's failure, so that the other cases are still checked
            bad.append(f'{what}: {type(e).__name__} {e}')
            continue
        got = tuple(np.bincount(X[:, 0].astype(int), minlength=len(want)).tolist())
        if (got, len(C) > 0) != (want, touch):
            bad.append(f'{what}: crossings with each copy {got} and {len(C)} contacts, not {want} and '
                       f'{"some" if touch else "none"}')
    on_a = crossings(lines, page, deg(3))[0]
    on_a = on_a[on_a[:, 1] == 0]                # on curve 0's first span, the straight span A
    if not (len(on_a) == 1 and np.allclose(on_a[0, [2, 4]], 0.5, rtol=0, atol=1e-12)):
        bad.append(f'straight spans crossing at both their middles: crossings on the first {on_a.tolist()}, not one at '
                   f't = 1/2 of both')
    zero = np.concatenate([lines[:1], np.repeat(lines[1:2, :1], 4, 1), lines[1:]])
    opened = lines.copy()
    opened[-1, 3] += 50
    for what, N in (('a span of length zero', zero), ('a curve that does not close', opened)):
        try:
            crossings(N, page, deg(3))
            bad.append(f'{what}: no AssertionError')
        except AssertionError:
            pass
    return bad


@qual
def qual_crossings_limit():
    """Replicata: crossings.crossings() on the corners of qual_crossings_known, but with their knots 1e-10 and 3e-10
    apart, where it cannot always certify a crossing or its absence, and B's knot in two or four directions from A's.
    Expectata: for each, either a contact or the right count (that of an exact rational verifier, as listed in
    CORNERS), never a wrong count without a contact."""
    import venn
    bad = []
    for off in (1e-10, 3e-10):
        for (alpha, ta, tb), want in CORNERS.items():
            for phi, count in want.items():
                X, C = crossings(corners(off, alpha, ta, tb, phi, venn.PAGE), venn.PAGE,
                                 [venn.turn(k, 3) for k in range(3)])
                got = tuple(np.bincount(X[:, 0].astype(int), minlength=2).tolist())
                if len(C) == 0 and got != (0, count):
                    bad.append(f'corners {off:g} apart, at {alpha:g} degrees, turning {ta:g} and {tb:g}, knots in '
                               f'direction {phi:g}: crossings with each copy {got} and no contact, not (0, {count})')
    return bad


@qual
def qual_svg_matches_cert():
    """Replicata: read img/venn-NN.svg, find every crossing of its curves exactly (crossings.py), label regions by
    walking each curve. Expectata: no self-intersections, exactly 2^n - 2 crossings, both curves
    through a crossing agree on its four region labels, and the crossings are exactly the cert's faces.
    (The crossings are found as crossings of the path with its turned copies, as drawn_faces says, so this also asserts
    that the curves are the path turned by multiples of 360/n degrees, which qual_svg_symmetric checks too, and that
    crossings() leaves no contact, a place where it could certify neither a crossing nor its absence.)"""
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
def qual_offenders_known():
    """Replicata: lay out and smooth 7 as `python3 venn.py draw 7` does, and give venn.offenders() its curve 0; then
    the same curve with a loop 0.01 across put into the middle of one span (curve 0 crossing itself there), and with a
    loop from the middle of that span back to it instead (curve 0 crossing itself exactly at a knot, where crossings()
    can certify neither a crossing nor its absence: a contact). Expectata: no offenders for the curve as smoothed; for
    each loop, exactly the orbits of the two crossings that bound the arc the span is on."""
    import contextlib, io, venn
    n = 7
    with contextlib.redirect_stderr(io.StringIO()):   # smooth() reports its attempts
        knots, kvid, orb, kof, s = venn.plotter_layout(n)
        ctrl = venn.smooth(n, knots, kvid, orb, kof, s)
    k, w = len(ctrl) // 3, 0.005
    on = [i for i in range(len(kvid)) if kvid[i] >= 0]         # the knots that are crossings
    bound = {int(orb[kvid[max(i for i in on if i <= k)]]), int(orb[kvid[min(i for i in on if i > k)]])}
    L, R = cut(ctrl[k:k + 1], 0.5)                              # span k cut at its middle, p
    p = L[0, 3]
    tan = (R[0, 1] - L[0, 2]) / np.linalg.norm(R[0, 1] - L[0, 2])   # the way the curve goes at p
    nrm = np.array([-tan[1], tan[0]])
    a, b = p - w * tan, p + w * tan
    La, Rb = L.copy(), R.copy()
    La[0, 3], Rb[0, 0] = a, b                                   # ending at a and starting at b instead
    loop = np.array([[a, a + 3 * w * tan + w * nrm, b - 3 * w * tan + w * nrm, b]])
    back = np.array([[p, p + w * (2 * tan + nrm), p + w * (-2 * tan + nrm), p]])
    kv = np.concatenate([kvid[:k + 1], [-1, -1], kvid[k + 1:]])  # two new knots, at no crossing
    bad = []
    for what, curve, kvids, want in (
            ('as smoothed', ctrl, kvid, set()),
            ('with a loop in span k', np.concatenate([ctrl[:k], La, loop, Rb, ctrl[k + 1:]]), kv, bound),
            ('with a loop from a knot back to it', np.concatenate([ctrl[:k], L, back, R, ctrl[k + 1:]]), kv, bound)):
        got = set(venn.offenders(n, curve, kvids, orb, kof, s).tolist())
        if got != want:
            bad.append(f'{what}: offenders {sorted(got)}, not {sorted(want)}')
    return bad


@qual
def qual_svg_defects():
    """Replicata: drawn_faces(), which qual_svg_matches_cert runs, on copies of img/venn-07.svg whose path has a loop
    0.01 across put into the middle of one span, or instead a loop from the middle of that span back to it. Expectata:
    an AssertionError saying how many self-intersections the first has, and one saying how many contacts the second
    has (curve 0 crossing itself exactly where the loop starts, where crossings() can certify neither a crossing nor
    its absence)."""
    text = svg_path(7).read_text()
    d = re.search(r'<path id="curve" d="([^"]+)"/>', text).group(1)
    N = nets(d)
    k, w = len(N) // 3, 0.005
    L, R = cut(N[k:k + 1], 0.5)                                 # span k cut at its middle, p
    p = L[0, 3]
    tan = (R[0, 1] - L[0, 2]) / np.linalg.norm(R[0, 1] - L[0, 2])   # the way the curve goes at p
    nrm = np.array([-tan[1], tan[0]])
    a, b = p - w * tan, p + w * tan
    La, Rb = L.copy(), R.copy()
    La[0, 3], Rb[0, 0] = a, b                                   # ending at a and starting at b instead
    loop = np.array([[a, a + 3 * w * tan + w * nrm, b - 3 * w * tan + w * nrm, b]])
    back = np.array([[p, p + w * (2 * tan + nrm), p + w * (-2 * tan + nrm), p]])
    fmt = lambda x: f'{x:.6f}'.rstrip('0').rstrip('.')
    path = lambda M: ' '.join([f'M{fmt(M[0, 0, 0])},{fmt(M[0, 0, 1])}'] + [
        f'C{fmt(x1)},{fmt(y1)} {fmt(x2)},{fmt(y2)} {fmt(x3)},{fmt(y3)}'
        for (x1, y1), (x2, y2), (x3, y3) in M[:, 1:].tolist()] + ['Z'])
    bad = []
    with tempfile.TemporaryDirectory() as tmp:
        for what, M, want in (('a loop in a span', np.concatenate([N[:k], La, loop, Rb, N[k + 1:]]), 'self-intersections'),
                              ('a loop from a knot back to it', np.concatenate([N[:k], L, back, R, N[k + 1:]]), 'contacts')):
            f = Path(tmp) / 'venn-07.svg'
            f.write_text(text.replace(d, path(M)))
            try:
                drawn_faces(f, 7)
                bad.append(f'{what}: no AssertionError')
            except AssertionError as e:
                if want not in str(e):
                    bad.append(f'{what}: AssertionError {e}, not about {want}')
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
        _browser['run'] = subprocess.run(['node', str(HERE / 'tools' / 'browser_quals.mjs'),
                                          *[str(n) for n in VIEWED if n not in CANVAS], 'canvas', *map(str, CANVAS)],
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
def qual_viewer_fit():
    """Replicata: open view.html?n=N for every n it draws as SVG paths (every n it shows but those in CANVAS), in
    Chromium, WebKit and Firefox, in a 1200 by 800 window.
    Expectata: for each n, the drawing's square page fits the space below the controls along the top and clear of
    the swatches and their checkboxes, which stand in a row along the bottom or, in a landscape window like this one,
    in a column along the right edge; it is centred in that space, so no control covers it; each curve is a
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
    """Replicata: open the viewer for the largest n it draws as SVG paths (drawing 19 anew takes a tenth to half a
    second); drag the drawing as a hand does, a move every 16 ms, then turn the wheel and pinch the same way, then stop.
    Expectata: meanwhile it
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
    browser's own keys, do nothing to the drawing; while no swatch has the focus, each arrow pans a tenth of the side
    of the drawing as it fits on opening its way, so the point that was that far from the centre in its direction is
    now at the centre (on a swatch the arrows move the slider: qual_viewer_slider)."""
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
def qual_viewer_download():
    """Replicata: open view.html?n=N for every n the viewer shows, as SVG paths or on a canvas, in Chromium, WebKit and
    Firefox, from a server that sends no cache headers, so that every fetch reaches it; wait for each one's first
    drawing. Expectata: img/venn-NN.svg is requested exactly once each time: the page fetches it and hands its bytes
    over to the worker, which draws the shading for every n (19's file is 4.2 MB)."""
    return browser('download')


@qual
def qual_viewer_error():
    """Replicata: open view.html?n=4, for which there is no drawing; then view.html?n=abc, view.html?n= and
    view.html?n=10000000; then view.html?n=7 with img/venn-07.svg's use 3 turning its curve a degree more than the
    file does, so that no curve lands on curve 3 (see turn, above). Expectata: for n=4, a visible error saying that
    img/venn-04.svg could not be loaded, ending
    with the server's status in brackets, "(404)" (status text alone would be empty over HTTP/2, as GitHub Pages
    serves it), four swatches, all disabled, no loading line and no broken picture in the drawing area; for the
    others, an error within 3 seconds and no swatches; for the turned use, the error saying that img/venn-07.svg
    could not be loaded with what went wrong in brackets in numbers and symbols alone, no words (AGENTS.md rule 7),
    and the seven swatches disabled."""
    return browser('error')


@qual
def qual_viewer_phone():
    """Replicata: open the viewer for every n it shows, as SVG paths or on a canvas, on phones with touch screens, 375
    by 667, 320 by 568, and 844 by 390 (one on its side); tap +.
    Expectata: the controls (the back arrow and number; the SVG link, zoom buttons and turn button; the swatches and
    their checkboxes) all fit in the window without overlapping each other, the page doesn't scroll, and every button
    and link, and every checkbox's target (it and its label), is at least 44 by 44 pixels, Apple's guideline for
    something to touch. After the tap, + looks as it did before it (no hover look stays
    behind, as it does on touch screens unless hover styles are kept to devices that can hover). On the phone on its
    side the swatches stand in a column along the right edge and the drawing fits in at least 300 pixels."""
    return browser('phone')


@qual
def qual_viewer_shading():
    """Replicata: open view.html?n=3, view.html?n=7 and view.html?n=13 in Chromium, WebKit and Firefox, in a 1200 by 800
    window; check the checkboxes of one set of curves after another: at n = 3 every set, from none to all three; at
    n = 7 none, {0}, {1, 2}, {0, 2, 4}, all but curve 6, and all seven; at n = 13 none. Each time, once the drawing of
    the shading has arrived (a worker draws it, for every n), take a screenshot and look at the probes it shows outside
    the controls, every 2 pixels across and down the window; and at n = 3, whose lines (2.8 pixels wide here) are wide
    enough to cover whole pixels, at the pixels a line covers wholly, at least 5 pixels from every other curve.
    Expectata: exactly the probes of the checked set's label are shaded and every other probe is unshaded: the shading
    is the region inside every checked curve and outside every other, beneath the curves, and with nothing checked it
    is the region outside every curve. Beneath them: at n = 3, each pixel a line covers wholly beside the shaded region
    is in that line's colour (each channel within 8). (Each set's label has probes in view, or the qual fails.)"""
    return browser('shading')


@qual
def qual_viewer_checks():
    """Replicata: open view.html?n=7 in a 1200 by 800 window while img/venn-07.svg is slow to arrive, then let it
    arrive; click curve 0's checkbox, then curve 3's; focus curve 0's and press Space. Open it in a 600 by 800 window,
    and on a phone with a touch screen, 375 by 667, where tap curve 6's checkbox twice. Expectata: one checkbox per
    curve, all unchecked on opening and disabled until the drawing has arrived, as the swatches are; checkbox i under
    swatch i and centred on it (beside it, to its right, where the swatches stand in a column, as in the 1200 by 800
    window); each with an accessible name, a different one, holding i + 1 (as swatch i's title, "Curve i + 1", does).
    Each click, Space and tap toggles its checkbox, and the shading follows: once its drawing has arrived, exactly the
    probes of the checked set's label are shaded (as in qual_viewer_shading). The clicks and Space in the 1200 by 800
    window leave the curves' SVG as it was (a MutationObserver sees no attribute, child or descendant of it change):
    only the shading is drawn anew. On the touch screen each checkbox's target (it and its label) is at least 44 by 44
    pixels, Apple's guideline, as in qual_viewer_phone."""
    return browser('checks')


@qual
def qual_viewer_slider():
    """Replicata: in view.html?n=7, press on the first swatch and drag along the swatches to the fifth, a swatch at a
    time, then on past the last; press on the third and drag back past the first; with a finger on a touch screen,
    drag from the second swatch to the fourth; then focus the fourth swatch and press →, ↓, ←, ↑, ↑, Home and End.
    Expectata: the swatches are the stops of a slider. While a press that began on a swatch moves, the curves shown
    are those up to and including the swatch nearest the pointer (curves 0 to k for swatch k, counting from 0, as in
    qual_viewer_curves), with exactly their swatches pressed; past an end, that end's swatch. A key moves it a stop:
    → and ↓ forward, ← and ↑ back, Home to the first and End to the last, and the focus goes to the swatch of the last
    curve shown; while a swatch has the focus, the arrow keys don't pan the drawing. Nothing here moves the drawing."""
    return browser('slider')


@qual
def qual_viewer_turn():
    """Replicata: open view.html?n=3 and view.html?n=7; check {0} at n = 3 and {0, 2} at n = 7, focus the turn button
    and press Enter; once it has turned, press Enter again; then click it, and click it again while it turns; then
    check every curve and click it once more. Expectata: the button's face is τ/n with n's value (τ/3, τ/7), inside the
    button. Each press and click turns the shading 1/n of a full turn anticlockwise about the page's centre, animated
    (the element #region, which holds the shading and nothing else, turned about the page's centre by angles from 0 to
    -360/n degrees, at least one strictly between), while the curves stay as they are; meanwhile the button stays
    enabled and keeps the focus, so Enter pressed twice on it turns twice, and the click during a turn turns once more
    after the turn under way. Once it has turned, the checkboxes checked are those of the curves the checked ones land
    on (see turn, above), found from the file's angles: at n = 7, whose use i turns curve 0 by -360i/7 degrees, curve
    i lands on curve i + 1 (mod 7), so {0, 2} becomes {1, 3}, then {2, 4}, {3, 5} and {4, 6}; at n = 3, whose use i
    turns it by 120i, curve i lands on curve i - 1 (mod 3), so {0} becomes {2}, then {1}, {0} and {2}. The shading
    stays turned until the drawing for the new set has arrived: from the moment the checkboxes change until a drawing
    asked for after that is shown, #region is turned by exactly -360/n degrees; then exactly the probes of the new
    set's label are shaded, #region's transform is the identity again, and the curves are as they were (each path's
    data and colour unchanged). With every curve checked, the turn changes nothing: every curve lands on a curve."""
    return browser('turn')


@qual
def qual_viewer_follow():
    """Replicata: in view.html?n=7, check curves 0 and 2; from a probe of the region they shade, drag the drawing, then
    turn the wheel and pinch where the drag left it, as in qual_viewer_settle (a move every 16 ms), and wait; then
    double-click there. Expectata: at every event the shading moves with the curves: the canvas it is drawn on, in
    #picture, is moved by #picture's transform as the curves are (its box on the screen within half a pixel of where
    that transform puts the box it had); and once the curves are drawn anew, until the shading drawn anew arrives, the
    old one stays where the gestures left it (within half a pixel). Then, after the gestures and after the
    double-click, exactly the probes of label 5 (curves 0 and 2) are shaded, wherever the new view puts them."""
    return browser('follow')


@qual
def qual_viewer_canvas_fit():
    """Replicata: open view.html?n=23 (each n in CANVAS, which the viewer draws on a canvas) in Chromium, WebKit and
    Firefox, in a 1200 by 800 window; turn the wheel to zoom in by 4 about a point on curve 0, then by 16 more about
    the same spot (64 in all), then as far as it goes (1000); then open it again with two device pixels to a CSS pixel.
    Expectata: each time, once the drawing has arrived, the canvas covers the window with a pixel for each device pixel
    (while that keeps lines under 0.85 of its pixels wide: qual_viewer_canvas_big) and matches its reference: at fit
    the page where qual_viewer_fit puts it, then zoomed about the spot pointed at, which stays put, the lines as wide on
    screen as at fit, so that bundles of nearly parallel curves come apart."""
    return browser('canvasFit')


@qual
def qual_viewer_canvas_curves():
    """Replicata: open view.html?n=23; click the first swatch, then the third, then press Escape. Expectata: one swatch
    per curve, in its curve's colour (the file's); once each drawing has arrived, the canvas matches its reference
    with curve 0 alone, then curves 0 to 2, then all 23, and exactly their swatches are pressed (aria-pressed), as in
    qual_viewer_curves."""
    return browser('canvasCurves')


@qual
def qual_viewer_canvas_settle():
    """Replicata: open view.html?n=23 and wait for its drawing; drag the drawing as a hand does, a move every 16 ms,
    then turn the wheel and pinch the same way, then stop; then show curve 0 alone, and once it is drawn press Escape
    and at once drag again, until the drawing of all 23 curves has arrived. Expectata: meanwhile nothing is drawn
    anew: the page asks its worker for nothing (no postMessage), shows no new drawing on its canvas, and draws on or
    resizes no canvas itself; at every event a CSS transform on the div #picture moves the picture already drawn, the
    canvas with it (its box on the screen within half a pixel of where the transform puts the box it had). Within 2
    seconds of the last event the page asks for a new drawing; until that arrives the old one stays where the gestures
    left it (within half a pixel), and once it has arrived, the picture's transform is the identity again and the
    canvas matches its reference where the moved picture showed the drawing, with lines as wide as at fit. A drawing
    asked for before a drag and arriving during it appears where the picture's transform puts it (within half a
    pixel)."""
    return browser('canvasSettle')


@qual
def qual_viewer_canvas_resize():
    """Replicata: open view.html?n=23 in a 1200 by 800 window and wait for its drawing; make the window 1400 by 900;
    then, in Chromium (the one browser in which these quals can change a page's devicePixelRatio without resizing it,
    through the DevTools protocol), give it two device pixels to a CSS pixel, as when a window moves to another screen,
    and send its resolution media query the change event a browser sends then (Chromium doesn't, for this). Expectata: each time it is drawn anew for the window as it now is: the canvas covers the window at its resolution
    (qual_viewer_canvas_fit) and matches its reference at the view that fits the window."""
    return browser('canvasResize')


@qual
def qual_viewer_canvas_loading():
    """Replicata: open view.html?n=23 while img/venn-23.svg is slow to arrive, and click +. Expectata: meanwhile the
    viewer shows img/venn-23.png, the card's picture, placed as the drawing would be and zoomed by + as it would be,
    the line saying that the full drawing is on its way, and 23 swatches, all disabled; nothing is drawn on the canvas.
    Once the SVG has arrived and its first drawing is shown, the PNG and the line are gone, the swatches work, and the
    canvas matches its reference, zoomed by +."""
    return browser('canvasLoading')


@qual
def qual_viewer_canvas_error():
    """Replicata: open view.html?n=23 with img/venn-23.svg replaced by a small drawing of 23 curves in venn.py's format
    (curve 0 cut to a span and another back to its start); then with img/venn-23.svg answering 404; then with the small
    drawing changed in one way each: an angle of NaN; a stroke-width of Infinity; a 24th use; the last use gone;
    another viewBox; an L command in the path; a use of another href; cut short halfway through the path; and then,
    with img/venn-23.svg as it is, with no Worker to be had, with canvas.js answering 404, and with the worker failing
    after its first drawing. Expectata: the small drawing as it is is drawn; each of the broken ones shows a visible
    error saying that img/venn-23.svg couldn't be loaded, with what went wrong in brackets ("(404)" for the 404), and no
    loading line; the 23 swatches stay disabled, nothing is drawn, and the PNG stays as the picture; and each of the
    last three shows the same error, with what failed in its brackets (canvas.js, for its 404)."""
    return browser('canvasError')


@qual
def qual_viewer_canvas_frames():
    """Replicata: open view.html?n=23 in a 2560 by 1440 window with two device pixels to a CSS pixel, and wait for its
    drawing; click + three times, each time waiting for the new drawing, timing the page's animation frames.
    Expectata: from the first click until a second after the last drawing has been shown, no frame takes over 100 ms:
    the worker draws, so the page goes on answering the pointer. (100 ms is the most a response to input may take and
    still feel immediate, the response budget of web.dev's RAIL model. On the machine these quals were written on, with
    its load average near 200, each redraw of 19's SVG paths held the page's frames up for 0.2 to 1.6 s in WebKit and
    1.3 to 12 s in Firefox.)"""
    return browser('canvasFrames')


@qual
def qual_viewer_canvas_big():
    """Replicata: open view.html?n=23 in a 2560 by 1440 window with two device pixels to a CSS pixel, as on a large
    external display. Expectata: its lines, 0.68 CSS pixel wide at that size, would be 1.35 device pixels wide;
    instead the canvas has fewer pixels than the screen, as many as keep its lines 0.85 of its pixels wide, and matches
    its reference at that size; and the first drawing arrives within 20 seconds of opening: Nielsen's 10-second limit
    for keeping a user's attention, doubled for a busy machine (on the one these quals were written on, with other
    jobs keeping its load average at 50 to 250, it took 1.4 to 4.1 s, and once over 10). Lines wider than about 0.9
    device pixel fall off the browsers' fast path for thin lines: with a pixel for each device pixel, this first
    drawing took 12.5 s in Chromium, 30 in Firefox, and 62 in WebKit, which then showed nothing."""
    return browser('canvasBig')


@qual
def qual_viewer_canvas_shading():
    """Replicata: open view.html?n=23 (each n in CANVAS) in a 1200 by 800 window and wait for its drawing; with
    nothing checked, take a screenshot at fit; check all 23 curves and take another; zoom in by 64 about a point P on
    curve 0, as in qual_viewer_canvas_fit, check the curves of the label most of the probes there have, and take
    another; drag the drawing 100 pixels left, and take another. Expectata: once each drawing has arrived, exactly the
    probes of the checked set's label are shaded, as in qual_viewer_shading (at fit, with nothing checked, the region
    outside every curve; with all checked, the one inside them all, about the page's centre; then the region checked
    about P, before and after the drag), at the places the qual's own arithmetic gives the probes; and the canvas of
    the curves, the first in #stage, still matches its reference: the shading is on a canvas of its own, beneath."""
    return browser('canvasShading')


@qual
def qual_viewer_canvas_turn():
    """Replicata: open view.html?n=23 and zoom in by 64 about a point P on curve 0, as in qual_viewer_canvas_fit; check
    the curves of the label most of the probes there have, and click the turn button; once it has turned, drag the
    drawing so that the point P turned by -360/23 degrees about the page's centre is where P was. Expectata: the
    button, whose face is τ/23, turns the shading as in qual_viewer_turn, and it stays turned until the drawing for the
    new set has arrived;
    then the checkboxes checked are those of the curves the checked ones land on: curve i lands on curve i + 1
    (mod 23), since use i turns curve 0 by -360i/23 degrees; exactly the probes of the new set's label are shaded, at
    the places the qual's own arithmetic gives them; and the canvas of the curves matches its reference."""
    return browser('canvasTurn')


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
