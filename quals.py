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
"""
import html.parser
import json
import hashlib
import math
import re
import sys
import urllib.request
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from scipy.spatial import cKDTree

from geom import candidate_pairs, intersections, sample

HERE = Path(__file__).resolve().parent
NS = (3, 5, 7, 11, 13, 17, 19, 23)     # every prime from 3 to the largest n with a known diagram
DRAWN = (3, 5, 7, 11, 13, 17, 19)      # n for which a cert is available and a drawing is shown
PENDING = (23,)                        # n announced but with no downloadable cert yet
assert DRAWN + PENDING == NS
# SHA-256 of the two certs taken from github.com/dzoba/venn17: the ones formally verified in Lean 4
PUBLISHED_SHA256 = {
    17: 'c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77',  # venn17-local-c3-s2.json
    19: 'ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d',  # venn19-closure-s196002.json
}
DOMAIN = 'svenn.dreev.es'


def cert_path(n): return HERE / 'certs' / f'venn-{n:02d}.json'
def svg_path(n): return HERE / 'img' / f'venn-{n:02d}.svg'


# ------------------------------------------------------------------ cert checking
def read_cert(n):
    d = json.loads(cert_path(n).read_text())
    assert d['n'] == n, (d['n'], n)
    weights = 1 << np.arange(n, dtype=np.int64)
    flat = [s for f in d['faces'] for s in f]
    assert all(len(s) == n and set(s) <= {'0', '1'} for s in flat), 'labels are not n-bit strings'
    bits = np.frombuffer(''.join(flat).encode(), np.uint8).reshape(-1, n) - ord('0')
    return (bits.astype(np.int64) @ weights).reshape(-1, 4)


def is_pow2(x): return (x > 0) & ((x & (x - 1)) == 0)


def rot(x, n):
    """The label rotation x[j] <- x[j+1] (Dzoba's convention; its inverse works equally well)."""
    return (x >> 1) | ((x & 1) << (n - 1))


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
    r['faces orient consistently'], O = orient(F, N)
    r['every region is a disk'] = single_rotation_cycles(O, N) if O is not None else False
    ek = uk  # undirected edges as U*N+V
    eu, ev = ek // N, ek % N
    bit = eu ^ ev
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
    rotated = np.sort(rot(F, n), 1)
    s1 = canon[np.lexsort(canon.T[::-1])]
    s2 = rotated[np.lexsort(rotated.T[::-1])]
    r['symmetric under label rotation'] = bool(np.array_equal(s1, s2))
    return r


def orient(F, N):
    """Orient every face so each edge is traversed once each way (BFS over shared edges). Returns
    (True, oriented faces) or (False, None) when no consistent orientation exists."""
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
    flip = np.full(m, -1, np.int8)
    flip[0] = 0
    frontier = [0]
    nbr, nd = (partner // 4).tolist(), need.tolist()
    while frontier:
        nxt = []
        for f in frontier:
            for s in range(4 * f, 4 * f + 4):
                g = nbr[s]
                if flip[g] < 0:
                    flip[g] = flip[f] ^ nd[s]
                    nxt.append(g)
        frontier = nxt
    reached = bool(np.all(flip >= 0))
    consistent = reached and bool(np.all((flip[np.arange(4 * m) // 4] ^ flip[partner // 4]) == need))
    O = np.where(flip[:, None] == 1, F[:, ::-1], F)
    return consistent, O


def single_rotation_cycles(O, N):
    """Around each label, chaining its faces through shared edges must give one cycle."""
    nxt = {}
    for row in O.tolist():
        for k in range(4):
            v, p, q = row[k], row[k - 1], row[(k + 1) % 4]
            nxt.setdefault(v, {})[p] = q
    for v, m in nxt.items():
        start = next(iter(m))
        x, steps = m[start], 1
        while x != start:
            x, steps = m[x], steps + 1
            if steps > len(m):
                return False
        if steps != len(m):
            return False
    return len(nxt) == N


# ------------------------------------------------------------------ drawing checking
def read_svg(path):
    """Return (curves, page) where curves[i] is the (k x 4 x 2) array of cubic Bezier control nets of the
    path with id curve-i."""
    t = path.read_text()
    page = float(re.search(r'viewBox="0 0 ([\d.]+) [\d.]+"', t).group(1))
    curves = {}
    for m in re.finditer(r'<path id="curve-(\d+)"[^>]* d="([^"]+)"', t):
        nums = np.array(re.findall(r'-?\d+(?:\.\d+)?', m.group(2)), float).reshape(-1, 2)
        assert m.group(2).startswith('M') and m.group(2).rstrip().endswith('Z')
        start, rest = nums[0], nums[1:].reshape(-1, 3, 2)
        p0 = np.vstack([start, rest[:-1, 2]])
        curves[int(m.group(1))] = np.concatenate([p0[:, None], rest], 1)
    return [curves[i] for i in range(len(curves))], page


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


def drawn_faces(polys):
    """Walk each curve through its crossings in order, toggling the labels of the regions on its two
    sides, and return {crossing point id: face} for every crossing, from each of its two curves."""
    n = len(polys)
    ca, sa, ta, cb, sb, tb, pts, touches = intersections(polys)
    assert len(touches) == 0, f'{len(touches)} degenerate segment contacts'
    assert not np.any(ca == cb), f'{int(np.sum(ca == cb))} self-intersections'
    SA = np.concatenate(polys)
    SB = np.concatenate([np.roll(p, -1, 0) for p in polys])
    scid = np.concatenate([np.full(len(p), i) for i, p in enumerate(polys)])
    ssid = np.concatenate([np.arange(len(p)) for p in polys])
    found = []
    for c in range(n):
        mine = np.concatenate([np.flatnonzero(ca == c), np.flatnonzero(cb == c)])
        pos = np.concatenate([sa[ca == c] + ta[ca == c], sb[cb == c] + tb[cb == c]])
        partner = np.concatenate([cb[ca == c], ca[cb == c]])
        order = np.roll(np.argsort(pos), -1)   # the walk starts just after crossing 0 and ends with it
        mine, pos, partner = mine[order], pos[order], partner[order]
        # start between crossings 0 and 1, offset to both sides by a third of the clearance
        mid = 0.5 * (pos[-1] + pos[0])
        k, f = int(mid), mid - int(mid)
        P = polys[c]
        a, b = P[k], P[(k + 1) % len(P)]
        x = a + f * (b - a)
        nrm = np.array([-(b - a)[1], (b - a)[0]]) / np.linalg.norm(b - a)
        # clearance: distance to every segment except this one and its two neighbours
        d = point_segment_distance(x, SA, SB)
        near = (scid == c) & (np.abs((ssid - k + 1) % len(P)) <= 2)
        eps = float(d[~near].min()) / 3
        lab = inside(np.array([x + eps * nrm, x - eps * nrm]), polys) @ (1 << np.arange(n))
        L, R = int(lab[0]), int(lab[1])
        assert L ^ R == 1 << c, 'the two start points do not straddle exactly this curve'
        for pid, b in zip(mine.tolist(), partner.tolist()):
            found.append((pid, frozenset((L, R, L ^ (1 << b), R ^ (1 << b)))))
            L, R = L ^ (1 << b), R ^ (1 << b)
    return found, len(pts)


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
    """Replicata: sha256sum certs/venn-17.json certs/venn-19.json.
    Expectata: the published SHA-256 of the Lean-verified certs from github.com/dzoba/venn17."""
    return [f'n={n}: sha256 {h[:12]}... is not {want[:12]}...'
            for n, want in PUBLISHED_SHA256.items()
            for h in [hashlib.sha256(cert_path(n).read_bytes()).hexdigest()] if h != want]


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
    through a crossing agree on its four region labels, and the crossings are exactly the cert's faces."""
    bad = []
    for n in DRAWN:
        nets, page = read_svg(svg_path(n))
        assert len(nets) == n, (len(nets), n)
        lens = np.concatenate([np.linalg.norm(c[:, 3] - c[:, 0], axis=1) for c in nets])
        polys = [sample(c, float(np.median(lens)) / 6)[0] for c in nets]
        found, npts = drawn_faces(polys)
        if npts != (1 << n) - 2:
            bad.append(f'n={n}: {npts} crossings drawn, not {(1 << n) - 2}')
            continue
        by = {}
        for pid, face in found:
            by.setdefault(pid, set()).add(face)
        if any(len(v) != 1 for v in by.values()):
            bad.append(f'n={n}: {sum(len(v) != 1 for v in by.values())} crossings labelled differently '
                       f'by their two curves')
            continue
        drawn = {next(iter(v)) for v in by.values()}
        cert = {frozenset(row) for row in read_cert(n).tolist()}
        if drawn != cert:
            bad.append(f'n={n}: {len(drawn - cert)} drawn faces not in the cert, '
                       f'{len(cert - drawn)} cert faces not drawn')
    return bad


@qual
def qual_svg_symmetric():
    """Replicata: rotate each curve of img/venn-NN.svg by 2 pi / n about the page centre.
    Expectata: it lands on another curve of the same drawing, the same shift for every curve,
    to within half the sampling step (a twentieth of the median span's chord) plus 0.002 for the
    SVG's rounding to three decimals."""
    bad = []
    for n in DRAWN:
        nets, page = read_svg(svg_path(n))
        lens = np.concatenate([np.linalg.norm(c[:, 3] - c[:, 0], axis=1) for c in nets])
        step = float(np.median(lens)) / 10
        polys = [sample(c, step)[0] for c in nets]
        trees = [cKDTree(p) for p in polys]
        w = np.exp(2j * np.pi / n)
        rotated = []
        for p in polys:
            z = ((p[:, 0] - page / 2) + 1j * (p[:, 1] - page / 2)) * w
            rotated.append(np.stack([z.real + page / 2, z.imag + page / 2], 1))
        # the curve that curve 0 lands on fixes the shift; every curve must land on its shifted partner
        shift = int(np.argmin([t.query(rotated[0][:50])[0].max() for t in trees]))
        worst = max(float(trees[(i + shift) % n].query(q)[0].max()) for i, q in enumerate(rotated))
        # a point of a curve is within half a sample spacing of a sample, and spacings average at most `step`
        if shift == 0 or worst > step / 2 + 0.002:
            bad.append(f'n={n}: shift {shift}, worst deviation {worst:.4g} (step {step:.4g}, in SVG units)')
    return bad


class PageParser(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.cards, self.links, self.latin_bad, self.last = [], [], [], None
        self.stack = []

    def handle_comment(self, data):
        self.last = ('comment', data.strip())

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if 'latin' in (a.get('class') or '').split():
            if not (self.last and self.last[0] == 'comment' and self.last[1].startswith('TODO')):
                self.latin_bad.append(f'<{tag} class="{a.get("class")}"> lacks a TODO comment right above it')
        if 'card' in (a.get('class') or '').split():
            self.cards.append(dict(n=a.get('data-n'), regions=a.get('data-regions'),
                                   crossings=a.get('data-crossings'), imgs=[], text=''))
        if tag == 'img' and self.cards:
            self.cards[-1]['imgs'].append(a.get('src'))
        for k in ('href', 'src'):
            if a.get(k):
                self.links.append(a[k])
        self.last = ('tag', tag)

    def handle_data(self, data):
        if data.strip():
            self.last = ('data', data)
        if self.cards:
            self.cards[-1]['text'] += data


def parse_page():
    p = PageParser()
    p.feed((HERE / 'index.html').read_text())
    return p


@qual
def qual_page_cards():
    """Replicata: open index.html. Expectata: one card per prime n from 3 to 23 in order, each stating
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
def qual_page_latin():
    """Replicata: read index.html. Expectata: every element of class latin (UI copy, which starts out in
    Latin per AGENTS.md rule 7) has a TODO comment right above it recapping the intended English."""
    return parse_page().latin_bad


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
