#!/usr/bin/env python3
"""Build the certificates and drawings for the svenn site.

Usage:  python3 venn.py certs          write certs/venn-NN.json for every drawn n
        python3 venn.py draw [N ...]   write img/venn-NN.svg and img/venn-NN.png
        python3 venn.py icons          write img/icon.svg, favicon.ico and the home-screen icons
        python3 venn.py preview        write img/preview.png, the link preview, from the drawings

Jargon (see also quals.py):
  xseq   crossing sequence. Draw a simple monotone symmetric n-Venn diagram so
         that every ray from the centre meets every curve once; along such a
         ray the curves sit at positions 1 (outermost) to n (innermost). As the
         ray sweeps around, each crossing swaps the curves at positions i and
         i+1 and is recorded as the number i. The first 1/n of the sweep
         determines the whole diagram. (Mamakani & Ruskey, Discrete Comput Geom
         52 (2014) 71-87, Section 2.)
  alpha  the free part of an xseq of a crosscut-symmetric diagram, which is
         rho, alpha, delta, alpha^r+ with rho = 1,3,2,5,4,...,n-2,n-3, delta =
         n-1,n-2,...,2, and alpha^r+ = alpha reversed with 1 added to each entry
         (ibid., Theorem 1).
"""
import gzip
import hashlib
import json
import math
import re
import struct
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

import numpy as np

import cert

HERE = Path(__file__).resolve().parent
DRAWN = (2, 3, 5, 7, 11, 13, 17, 19, 23)

# The alpha of each monotone diagram shown, copied from the papers named.
ALPHA = {
    # two circles: a half turn has one crossing, which is rho = 1, with alpha and delta empty (worked out here; the
    # papers give no crossing sequence for n = 2)
    2: [],
    # three circles (Venn 1880) and Grunbaum's five ellipses (1975): alpha is empty (Mamakani & Ruskey 2014, Sec. 2)
    3: [],
    5: [],
    # "Hamilton", named by A. W. F. Edwards (Mamakani & Ruskey 2014, Sec. 3: alpha_H = 3, 2, 4, 3)
    7: [3, 2, 4, 3],
    # "Newroz", the first simple symmetric 11-Venn diagram (Mamakani & Ruskey, arXiv:1207.6452, and 2014, Sec. 2)
    11: [int(c) for c in '323434543234345434545654565676543254346545'
                          '676787656543457654658765457656876546576567'],
    # the first simple symmetric 13-Venn diagram (Mamakani & Ruskey 2014, Table 1, alpha_T)
    13: [3, 2, 4, 3, 5, 4, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 5, 4, 6, 5, 7, 6, 5, 4, 3, 2, 3, 4,
         3, 4, 5, 4, 5, 6, 5, 4, 3, 6, 5, 6, 5, 4, 5, 4, 7, 6, 5, 4, 6, 5, 7, 6, 8, 7, 6, 5,
         4, 3, 7, 8, 6, 7, 5, 6, 7, 8, 5, 6, 5, 6, 7, 6, 7, 4, 5, 6, 7, 6, 5, 6, 5, 4, 5, 4,
         9, 8, 7, 6, 5, 4, 3, 2, 3, 4, 3, 4, 5, 4, 5, 6, 5, 4, 3, 5, 4, 6, 5, 4, 5, 6, 7, 6,
         5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 7, 6, 7, 8, 7, 6, 5, 4, 3, 5, 4, 6, 5, 7, 6, 5, 4, 6,
         5, 7, 6, 8, 7, 8, 7, 6, 5, 4, 5, 6, 7, 6, 5, 4, 7, 6, 8, 7, 6, 5, 7, 6, 5, 8, 7, 6,
         9, 8, 7, 6, 5, 4, 8, 7, 8, 7, 6, 7, 6, 5, 9, 8, 7, 6, 8, 7, 6, 5, 9, 8, 7, 6, 10, 9,
         8, 7, 6, 5, 4, 3, 7, 8, 9, 10, 6, 7, 8, 9, 7, 8, 9, 10, 6, 7, 8, 7, 8, 9, 8, 9, 5, 6,
         7, 8, 9, 10, 7, 8, 9, 6, 7, 8, 6, 7, 8, 9, 7, 8, 5, 6, 7, 8, 7, 6, 5, 6, 7, 8, 9, 8,
         9, 7, 8, 6, 7, 5, 6, 7, 8, 6, 7, 5, 6, 4, 5, 6, 7, 8, 9, 8, 7, 8, 7, 6, 7, 8, 7, 6,
         7, 6, 5, 6, 7, 8, 7, 6, 5, 6, 7, 5, 6, 4, 5, 6, 7, 6, 5, 6, 5, 4, 5, 4],
}

# Non-monotone diagrams: certs from github.com/dzoba/venn17 (CC BY 4.0), checked by SHA-256. These three are the ones
# formally verified in Lean 4. The 17 and 19 are in the repo, pinned to a commit; the 23, at 889 MB, is a release asset,
# gzipped, and its SHA-256 is the one the repo's README publishes, that of the JSON unzipped.
DZOBA = 'https://raw.githubusercontent.com/dzoba/venn17/e89d6f6f8cf17294c5b32e0406088684557fbde4/certificates/'
FETCHED = {
    17: (DZOBA + 'venn17-local-c3-s2.json', 'c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77'),
    19: (DZOBA + 'venn19-closure-s196002.json', 'ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d'),
    23: ('https://github.com/dzoba/venn17/releases/download/v1.3/venn23-c25-s230025.json.gz',
         'adc5a02eeaac6e49ac56ed9acfe6aebf5325ca13ebe070486c792b0d80eae2b1'),
}
assert sorted(ALPHA) + sorted(FETCHED) == list(DRAWN)


def cert_path(n): return HERE / 'certs' / f'venn-{n:02d}.json'


def xseq(n):
    """The crossing sequence of one 1/n sector: rho, alpha, delta, alpha^r+."""
    alpha = ALPHA[n]
    rho = [1] + [k for i in range(3, n - 1, 2) for k in (i, i - 1)]
    delta = list(range(n - 1, 1, -1))
    alpha_r = [a + 1 for a in reversed(alpha)]
    s = rho + alpha + delta + alpha_r
    assert len(s) * n == 2 ** n - 2, (n, len(s))
    return s


def cert_from_xseq(n):
    """Sweep the ray n times around, recording each crossing as the four regions around it.

    At position i (1-based) the region between curves pi[i-1] and pi[i] is inside exactly the curves
    pi[0..i-1], so a swap of a = pi[i-1] and b = pi[i] has the regions T, T+a, T+a+b, T+b around it,
    in cyclic order, where T is the set of curves outside both."""
    s = xseq(n)
    pi = list(range(n))
    faces = []
    for i in s * n:
        a, b = pi[i - 1], pi[i]
        T = set(pi[:i - 1])
        faces.append([T, T | {a}, T | {a, b}, T | {b}])
        pi[i - 1], pi[i] = b, a
    assert pi == list(range(n)), 'the sweep does not close up'
    # Rotating the diagram by one sector carries the curve at each position to the curve at the same
    # position one sector later (tau). Renumber curves along that cycle so the rotation is curve j -> j+1.
    tau = list(range(n))
    for i in s:
        tau[i - 1], tau[i] = tau[i], tau[i - 1]
    name, c = {}, 0
    for j in range(n):
        name[c] = j
        c = tau[c]
    assert c == 0 and len(name) == n, 'one sector does not rotate the curves through a single n-cycle'
    label = lambda S: ''.join(str(sum(name[c] == i for c in S)) for i in range(n))
    return {'n': n, 'faces': [[label(S) for S in f] for f in faces]}


def certs():
    (HERE / 'certs').mkdir(exist_ok=True)
    for n in ALPHA:
        cert_path(n).write_text(json.dumps(cert_from_xseq(n), separators=(',', ':')) + '\n')
    for n, (url, sha) in FETCHED.items():
        fetch(url, sha, cert_path(n))


def fetch(url, sha, path):
    """Download url to path, unzipped if its name ends .gz, asserting that what is written has SHA-256 sha (it is
    written beside path first, and moved there only then)."""
    part, h = path.with_suffix('.part'), hashlib.sha256()
    with urllib.request.urlopen(url, timeout=300) as r, open(part, 'wb') as f:
        src = gzip.GzipFile(fileobj=r) if url.endswith('.gz') else r
        while chunk := src.read(1 << 24):
            h.update(chunk)
            f.write(chunk)
    assert h.hexdigest() == sha, f'{url} does not match its published SHA-256'
    part.rename(path)


# Drawing. Each drawer gives curve 0 as cubic Beziers (control nets, in page units) and the shift s that places the
# others: curve i is curve 0 turned about the page centre by turn(s i, n) degrees. write_svg() writes curve 0 once
# and each curve as a turned copy of it (see there), with no width and height, so a browser fits it to the window,
# and it is rendered to a PNG_PX-wide PNG with lines about 18/n pixels wide. Coordinates have DECIMALS places, and
# bundles of nearly parallel curves at n = 17 sit closer together than a thousandth of a 500-unit disk, so the disk
# is 50000 units across (page 51200 with margins).
#
# Two ways to draw, picked by DRAWER below (the one branch between them): the n = 2, 3 and 5 diagrams are drawn as
# their classic congruent circles and ellipses; every other n goes through Dzoba's plotter
# (vendor/venn17/plotter_svg.py, MIT), which lays out the cert's crossing graph, and is smoothed and checked here.
# Both are checked against the certs by quals.py.
PAGE, DIAMETER, MARGIN = 51200.0, 50000.0, 600.0
PNG_PX = 1600
# vendor/venn17 holds plotter/plotter_svg.py and verify/{interval_growth,gks_scaffold,gks_chains}.py copied
# unchanged from github.com/dzoba/venn17 at commit e89d6f6f8cf17294c5b32e0406088684557fbde4 (MIT, see LICENSE).
sys.path.insert(0, str(HERE / 'vendor' / 'venn17'))
import plotter_svg  # noqa: E402
from crossings import crossings  # noqa: E402


def stroke(n): return 18.0 / n * PAGE / PNG_PX


def turn(k, n):
    """Rotation k of n, 360 k / n degrees, as the SVG writes it (to 12 significant digits), so that the smoothing
    check turns curve 0 exactly as a reader of the SVG does."""
    return float(f'{360 * k / n:.12g}')


# Congruent ellipses with semi-axes a and b, centred at distance d from the centre at angles
# phase - 2 pi j / n, each tilted psi off its radial direction. The 5-ellipse values were found by a
# grid search for a configuration with all 32 regions present and connected and the smallest region
# as large as possible; quals.py checks the result against the cert. The two circles sit side by side, each through
# the other's centre.
CONICS = {
    2: dict(a=1.0, b=1.0, d=0.5, psi=0.0, phase=math.pi),
    3: dict(a=1.0, b=1.0, d=0.6, psi=0.0, phase=-math.pi / 2),
    5: dict(a=1.0, b=0.5, d=0.35, psi=0.2, phase=-math.pi / 2),
}
KAPPA = 4 * (math.sqrt(2) - 1) / 3   # cubic Bezier handle length for a quarter circle


def draw_conics(n):
    """Ellipse 0 as control nets, and the shift 1: ellipse j, at angle phase - 2 pi j / n (the direction that matches
    the labelling of cert_from_xseq), is ellipse 0 turned by 360 j / n degrees in the SVG's coordinates, y down."""
    p = CONICS[n]
    # unit circle as four cubic spans, then the affine map of the ellipse
    c = [(1, 0), (1, KAPPA), (KAPPA, 1), (0, 1), (-KAPPA, 1), (-1, KAPPA), (-1, 0), (-1, -KAPPA),
         (-KAPPA, -1), (0, -1), (KAPPA, -1), (1, -KAPPA)]
    unit = np.array(c + c[:1], float)
    th = p['phase']
    ang = th + p['psi']
    R = np.array([[math.cos(ang), -math.sin(ang)], [math.sin(ang), math.cos(ang)]])
    e = (unit * [p['a'], p['b']]) @ R.T + p['d'] * np.array([math.cos(th), math.sin(th)])
    q = np.stack([e[:, 0], -e[:, 1]], 1) * (DIAMETER / 2 / float(np.linalg.norm(e, axis=1).max())) + PAGE / 2
    return np.stack([q[0:12:3], q[1:13:3], q[2:13:3], q[3:13:3]], 1), 1


TENSION, CAP, RIM_KNOTS, BULGE = 0.9, 0.42, 5, 1.04   # the plotter's defaults


def draw_plotter(n):
    """Lay out the cert's crossing graph with Dzoba's plotter (an exactly n-fold symmetric weighted
    Tutte embedding, then a radial warp), and smooth curve 0, and so by the symmetry every curve, with
    Catmull-Rom splines through its crossings. Smoothing can make curves cross between crossings;
    wherever it does, the tension at the crossings bounding the offending arcs is cut, by whole
    rotation orbits so the symmetry is kept, down to straight arcs if need be. (Nothing checks first that
    the drawing with every arc straight is clean: at 23 it has knots where one curve turns back in a
    hairpin a few tenths of a degree wide as another passes through, which crossings() cannot certify
    as straight corners but can once the hairpins are smoothed, and smoothing never needs them
    straight. smooth() asserts the end result.) This is the plotter's main() with its planarity sweep
    replaced by offenders(), and done for curve 0 alone."""
    knots, kvid, orb, kof, s = plotter_layout(n)
    return smooth(n, knots, kvid, orb, kof, s), s


def plotter_layout(n):
    """Curve 0's knots (m x 2, page coordinates), the crossing of each knot (-1 for the extra knots bowing the outer
    ring), and the orb, kof and shift of the crossing graph (see cert.Primal), which place every other crossing:
    crossing v of curve 0 turned by turn(k, n) degrees is crossing rho^j(v), where s j = -k mod n."""
    P = cert.Primal(cert.read(cert_path(n), n), n)
    z = plotter_svg.layout(P, iters=300, power=1.0, damp=0.5)
    # The radial warp carries the second ring of crossings out to radius `rim` (a fraction of the outer
    # ring's); it has to stay inside the n-gon of outer crossings, whose edges come within cos(pi/n)
    # of the centre. (The plotter's default, 0.95, breaks planarity for n <= 7.) Its other job,
    # spreading the crossings out radially with the slope of log g(r) against log r held to
    # [1/aniso, aniso], is turned off: where that slope varies along an arc, the straight arc between
    # the warped ends strays from the warped image of the old one, so a crossing beside it can land on
    # its other side, and with the plotter's 1.8 one did in every sector at n = 23. With aniso = 1 the
    # warp scales every crossing but the n outer ones by one factor, so the arcs among those are as
    # planar as Tutte's layout makes them, at any n; smooth() checks the rest.
    z, _ = plotter_svg.radial_warp(z, n, rim=math.cos(math.pi / n) - 0.05, aniso=1.0)
    # Knots of curve 0: its crossings in cycle order, plus RIM_KNOTS points bowing each arc of the
    # outer ring outward into a petal (as in the plotter's main()).
    outer_edges = {frozenset((P.outer[t], P.outer[(t + 1) % n])) for t in range(n)}
    cyc = P.cycle0.tolist()
    pk, vk = [], []
    for k, v in enumerate(cyc):
        pk.append(z[v])
        vk.append(v)
        w = cyc[(k + 1) % len(cyc)]
        # zero or RIM_KNOTS extra knots, depending on whether v-w is an outer-ring arc
        on_rim = frozenset((v, w)) in outer_edges
        a0 = np.angle(z[v])
        da = 2 * math.pi / n * np.sign(math.remainder(float(np.angle(z[w]) - a0), 2 * math.pi))
        for f in [(j + 1) / (RIM_KNOTS + 1) for j in range(RIM_KNOTS * on_rim)]:
            pk.append(BULGE * abs(z[v]) * np.exp(1j * (a0 + f * da)))
            vk.append(-1)
    knots = np.stack([np.real(pk), -np.imag(pk)], 1)
    probe = plotter_svg.sample_bezier(plotter_svg.bezier_controls(knots, np.full(len(knots), TENSION), CAP)[0], 8)
    scale = DIAMETER / (2.0 * float(np.linalg.norm(probe.reshape(-1, 2), axis=1).max()))
    return knots * scale + PAGE / 2, np.array(vk), P.orb, P.kof, P.shift


def smooth(n, knots, kvid, orb, kof, s):
    """Curve 0's control nets, rounded to DECIMALS places as the SVG will hold them, with the tension at its crossings
    cut, by whole orbits, wherever the drawing would cross itself between crossings (see offenders)."""
    def nets(tension):   # tension: one per orbit of crossings
        t = np.where(kvid >= 0, tension[orb[np.maximum(kvid, 0)]], TENSION)
        return np.round(plotter_svg.bezier_controls(knots, t, CAP)[0], DECIMALS)
    tension = np.full(len(orb) // n, TENSION)
    for attempt in range(8):
        ctrl = nets(tension)
        bad = offenders(n, ctrl, kvid, orb, kof, s)
        print(f'n={n} smoothing attempt {attempt}: {len(bad)} orbits of crossings bound arcs that cross', file=sys.stderr)
        if len(bad) == 0:
            break
        tension[bad] *= 0.35 * (attempt < 2)   # cut to 35%, and from the third try on to 0
    assert len(bad) == 0, 'smoothing still crosses after eight attempts'
    return ctrl


def offenders(n, ctrl, kvid, orb, kof, s):
    """The orbits of the crossings at which the drawing goes wrong: curve 0, the control nets ctrl with the crossing
    kvid of each knot, and its turned copies, turned exactly as the SVG will turn them. Every crossing must be where its
    two curves cross exactly once, and nothing else may cross. crossings() finds each orbit of the drawing's crossings
    once, exactly, as a crossing of curve 0 with a copy, at span + t along each; it is that crossing when the knots
    nearest it along both curves are the same crossing of the drawing. The offenders are the crossings bounding the
    arcs at a knot that gets other than one such crossing, and those bounding both arcs of any other crossing (curve 0
    crossing itself, too) or contact.

    The crossings of the whole drawing are told apart by naming crossing rho^j(v), v a crossing of curve 0,
    orb[v] n + (kof[v] + j) mod n, where rho^j turns curve 0 as the copy is (see plotter_layout)."""
    X, C = crossings(ctrl, PAGE, [turn(k, n) for k in range(n)])
    m, ar = len(kvid), np.arange(len(kvid))
    d = X[:, 0].astype(np.int64)
    ka, kb = (np.round(X[:, i] + X[:, i + 1]).astype(np.int64) % m for i in (1, 3))   # the knots nearest each crossing
    # the crossings bounding each span's arc: the last crossing knot at or before its start, and the first one after it
    # (wrapping round the closed curve)
    before = kvid[np.maximum.accumulate(np.where(kvid >= 0, ar, -1))]
    nxt = np.minimum.accumulate(np.where(kvid >= 0, ar, m)[::-1])[::-1]
    nxt = np.append(nxt[1:], m)
    after = kvid[np.where(nxt < m, nxt, int(np.flatnonzero(kvid >= 0)[0]))]
    arcs = np.stack([before, after], 1)

    def name(v, k):   # crossing v of curve 0 (or -1), as copy k shows it, named in the whole drawing
        j = (-k * pow(s, -1, n)) % n
        return np.where(v >= 0, orb[np.maximum(v, 0)] * n + (kof[np.maximum(v, 0)] + j) % n, -1)
    na = name(kvid[ka], 0)
    knot = (d > 0) & (na >= 0) & (na == name(kvid[kb], d))
    hit = np.bincount(orb[kvid[ka[knot]]], minlength=len(orb) // n)
    spans = np.concatenate([X[~knot][:, [1, 3]].ravel(), C[:, [1, 3]].ravel()]).astype(np.int64)
    stray = orb[arcs[spans].ravel()]
    # an orbit whose crossing is crossed other than once is fixed by straightening the arcs at it, which takes the
    # crossings at both ends of each of those arcs
    miss = np.flatnonzero(hit != 1)
    ends = np.stack([kvid, np.roll(kvid, -1)], 1)
    at_miss = arcs[np.isin(np.where(ends >= 0, orb[np.maximum(ends, 0)], -1), miss).any(1)]
    return np.unique(np.concatenate([miss, orb[at_miss.ravel()], stray]))


DRAWER = {n: (draw_conics if n in CONICS else draw_plotter) for n in DRAWN}


def draw(n):
    svg = HERE / 'img' / f'venn-{n:02d}.svg'
    write_svg(svg, n, *DRAWER[n](n))
    svg2png(svg, svg.with_suffix('.png'), PNG_PX)


# The places coordinates are given to. Three were too few once curves 1 to n - 1 became turned copies of rounded curve
# 0: turning it moves a point up to 0.0014 from where rounding that curve itself would, and at n = 19 straight arcs of
# different curves pass closer than that, so that 20 crossings stayed wrong however far smoothing was cut back.
DECIMALS = 6


def write_svg(svg, n, ctrl, s):
    """Write the drawing's SVG: curve 0, the control nets ctrl, once, as <defs><path id="curve">, and curve i as
    <use id="curve-i"> of it turned about the page centre by turn(s i, n) degrees. So it is symmetric by construction (to
    within the 12 significant digits of its angles), in 1/n of the bytes that n paths would take (62 MB down to 4.2 at
    n = 19). It has no width and height, so that a browser
    opening it fits it to the window."""
    fmt = lambda x: f'{x:.{DECIMALS}f}'.rstrip('0').rstrip('.')
    d = ' '.join([f'M{fmt(ctrl[0, 0, 0])},{fmt(ctrl[0, 0, 1])}']
                 + [f'C{fmt(x1)},{fmt(y1)} {fmt(x2)},{fmt(y2)} {fmt(x3)},{fmt(y3)}'
                    for (x1, y1), (x2, y2), (x3, y3) in ctrl[:, 1:].tolist()] + ['Z'])
    c = fmt(PAGE / 2)
    uses = ''.join(f'<use id="curve-{i}" href="#curve" fill="none" stroke="{colour}" stroke-width="{stroke(n)}" '
                   f'stroke-linecap="round" stroke-linejoin="round" '
                   f'transform="rotate({turn(s * i % n, n):.12g} {c} {c})"/>\n'
                   for i, colour in enumerate(plotter_svg.palette(n)))
    svg.write_text(f'<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" version="1.1" '
                   f'viewBox="0 0 {fmt(PAGE)} {fmt(PAGE)}">\n<defs><path id="curve" d="{d}"/></defs>\n{uses}</svg>\n')


def svg2png(svg, png, px):
    """Render an SVG to a PNG px pixels wide, with resvg."""
    subprocess.run(['node', str(HERE / 'tools' / 'svg2png.mjs'), str(svg), str(png), str(px)], check=True)


# Icons: Venn's three circles as drawn on the page (CONICS[3], in the 3-curve drawing's colours), with strokes
# ICON_STROKE radii wide, which is 1.4 pixels in a 16-pixel favicon. Browser tabs get them on nothing; home screens
# get them on white with ICON_MARGIN radii to spare all round, since iOS shows transparency as black and rounds off
# the corners.
ICON_STROKE, ICON_MARGIN = 0.3, 0.45


def icon_svg(margin, background):
    """The icon as an SVG: a square viewBox fitted round the circles' strokes plus `margin` radii all round, over a
    rectangle of colour `background` ('none' for none)."""
    p = CONICS[3]
    assert p['a'] == p['b'] == 1, 'the icon is drawn with unit circles'
    th = [p['phase'] - 2 * math.pi * j / 3 for j in range(3)]
    c = np.array([[p['d'] * math.cos(t), -p['d'] * math.sin(t)] for t in th])   # y down, as in draw_conics
    lo, hi = c.min(0) - 1 - ICON_STROKE / 2, c.max(0) + 1 + ICON_STROKE / 2
    side = float((hi - lo).max()) + 2 * margin
    x, y = (lo + hi) / 2 - side / 2
    fmt = plotter_svg.fmt
    circles = ''.join(f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="1" stroke="{colour}"/>'
                      for (cx, cy), colour in zip(c, plotter_svg.palette(3)))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{fmt(x)} {fmt(y)} {fmt(side)} {fmt(side)}">\n'
            f'<rect x="{fmt(x)}" y="{fmt(y)}" width="{fmt(side)}" height="{fmt(side)}" fill="{background}"/>\n'
            f'<g fill="none" stroke-width="{ICON_STROKE}">{circles}</g>\n</svg>\n')


def write_ico(path, pngs):
    """Write an ICO file holding the given PNGs (as bytes; square, under 256 pixels), a form every browser reads."""
    entries, offset = [], 6 + 16 * len(pngs)
    for b in pngs:
        w, h = struct.unpack('>II', b[16:24])            # from the PNG's IHDR chunk
        assert w == h < 256, (w, h)
        entries.append(struct.pack('<BBBBHHII', w, h, 0, 0, 1, 32, len(b), offset))
        offset += len(b)
    path.write_bytes(struct.pack('<HHH', 0, 1, len(pngs)) + b''.join(entries) + b''.join(pngs))


def icons():
    """img/icon.svg and favicon.ico for browser tabs; apple-touch-icon.png, img/icon-192.png and img/icon-512.png
    (the last two named in manifest.webmanifest) for home screens."""
    tab = HERE / 'img' / 'icon.svg'
    tab.write_text(icon_svg(0, 'none'))
    with tempfile.TemporaryDirectory() as tmp:
        sizes = (16, 32, 48)
        for px in sizes:
            svg2png(tab, Path(tmp) / f'{px}.png', px)
        write_ico(HERE / 'favicon.ico', [(Path(tmp) / f'{px}.png').read_bytes() for px in sizes])
        home = Path(tmp) / 'home.svg'
        home.write_text(icon_svg(ICON_MARGIN, '#ffffff'))
        for png, px in (('apple-touch-icon.png', 180), ('img/icon-192.png', 192), ('img/icon-512.png', 512)):
            svg2png(home, HERE / png, px)


# The link preview: the drawings of PREVIEW_NS in two rows of three, each PREVIEW_CELL pixels square with
# PREVIEW_GAP between, on white, in a PREVIEW_W x PREVIEW_H PNG (the size of a large link preview). Their lines are
# PREVIEW_STROKE / n pixels wide; the drawings' own, scaled down, would be too faint to see.
PREVIEW_NS = (3, 5, 7, 11, 13, 17)
PREVIEW_W, PREVIEW_H, PREVIEW_CELL, PREVIEW_GAP, PREVIEW_STROKE = 1200, 630, 286, 14, 7.5


def preview():
    """img/preview.png, the link preview, from the drawings in img/."""
    cols = 3
    rows = len(PREVIEW_NS) // cols
    assert rows * cols == len(PREVIEW_NS)
    x0 = (PREVIEW_W - cols * PREVIEW_CELL - (cols - 1) * PREVIEW_GAP) / 2
    y0 = (PREVIEW_H - rows * PREVIEW_CELL - (rows - 1) * PREVIEW_GAP) / 2
    parts = []
    for k, n in enumerate(PREVIEW_NS):
        text = (HERE / 'img' / f'venn-{n:02d}.svg').read_text()
        assert f'viewBox="0 0 {plotter_svg.fmt(PAGE)} {plotter_svg.fmt(PAGE)}"' in text, f'venn-{n:02d}.svg'
        body, count = re.subn(r'stroke-width="[\d.]+"', f'stroke-width="{PREVIEW_STROKE / n * PAGE / PREVIEW_CELL:.1f}"',
                              text[text.index('<defs>'):text.rindex('</svg>')])
        assert count == n, (n, count)
        # the six drawings each define a path with id "curve": give each its own id, so each draws its own curve
        assert body.count('id="curve"') == 1 and body.count('href="#curve"') == n, n
        body = body.replace('id="curve"', f'id="curve{n}"').replace('href="#curve"', f'href="#curve{n}"')
        x, y = x0 + k % cols * (PREVIEW_CELL + PREVIEW_GAP), y0 + k // cols * (PREVIEW_CELL + PREVIEW_GAP)
        parts.append(f'<svg x="{x:g}" y="{y:g}" width="{PREVIEW_CELL}" height="{PREVIEW_CELL}" '
                     f'viewBox="0 0 {plotter_svg.fmt(PAGE)} {plotter_svg.fmt(PAGE)}">\n{body}</svg>\n')
    with tempfile.TemporaryDirectory() as tmp:
        svg = Path(tmp) / 'preview.svg'
        svg.write_text(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {PREVIEW_W} {PREVIEW_H}">\n'
                       f'<rect width="{PREVIEW_W}" height="{PREVIEW_H}" fill="#ffffff"/>\n' + ''.join(parts) + '</svg>\n')
        svg2png(svg, HERE / 'img' / 'preview.png', PREVIEW_W)


def main():
    cmd, args = sys.argv[1], [int(a) for a in sys.argv[2:]]
    {'certs': lambda: certs(), 'draw': lambda: [draw(n) for n in (args or DRAWN)],
     'icons': lambda: icons(), 'preview': lambda: preview()}[cmd]()


if __name__ == '__main__':
    main()
