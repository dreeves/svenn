#!/usr/bin/env python3
"""Build the certificates and drawings for the svenn site.

Usage:  python3 venn.py certs          write certs/venn-NN.json for every drawn n
        python3 venn.py draw [N ...]   write img/venn-NN.svg and img/venn-NN.png

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
import hashlib
import json
import math
import multiprocessing
import subprocess
import sys
import urllib.request
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
DRAWN = (3, 5, 7, 11, 13, 17, 19)

# The alpha of each monotone diagram shown, copied from the papers named.
ALPHA = {
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

# Non-monotone diagrams: certs from github.com/dzoba/venn17 (CC BY 4.0), pinned to a commit and checked by
# SHA-256. These two are the ones formally verified in Lean 4.
DZOBA = 'https://raw.githubusercontent.com/dzoba/venn17/e89d6f6f8cf17294c5b32e0406088684557fbde4/certificates/'
FETCHED = {
    17: ('venn17-local-c3-s2.json', 'c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77'),
    19: ('venn19-closure-s196002.json', 'ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d'),
}
assert sorted(ALPHA) + sorted(FETCHED) == list(DRAWN)


def cert_path(n): return HERE / 'certs' / f'venn-{n:02d}.json'


def xseq(n):
    """The crossing sequence of one 1/n sector: rho, alpha, delta, alpha^r+."""
    alpha = ALPHA[n]
    assert len(alpha) * n == 2 ** (n - 1) - (n - 1) ** 2, (n, len(alpha))
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
    for n, (name, sha) in FETCHED.items():
        data = urllib.request.urlopen(DZOBA + name, timeout=300).read()
        assert hashlib.sha256(data).hexdigest() == sha, f'{name} does not match its published SHA-256'
        cert_path(n).write_bytes(data)


# Drawing. Every drawing is an SVG with one closed path of cubic Beziers per curve, id curve-i for the
# curve of bit i, rendered to a PNG_PX-wide PNG with lines about 18/n pixels wide. The plotter writes
# coordinates to three decimals, and bundles of nearly parallel curves at n = 17 sit closer together
# than a thousandth of a 500-unit disk, so the disk is 50000 units across (page 51200 with margins).
# The SVG's width and height attributes are then dropped so a browser fits it to the window.
#
# Two ways to draw, picked by DRAWER below (the one branch in this file): the n = 3 and n = 5 diagrams
# are drawn as their classic congruent circles and ellipses; every other n goes through Dzoba's plotter
# (vendor/venn17/plotter_svg.py, MIT), which lays out the cert's crossing graph and smooths it and
# checks its own output. Both are checked against the certs by quals.py.
PAGE, DIAMETER, MARGIN = 51200.0, 50000.0, 600.0
PNG_PX = 1600
# vendor/venn17 holds plotter/plotter_svg.py and verify/{interval_growth,gks_scaffold,gks_chains}.py copied
# unchanged from github.com/dzoba/venn17 at commit e89d6f6f8cf17294c5b32e0406088684557fbde4 (MIT, see LICENSE).
sys.path.insert(0, str(HERE / 'vendor' / 'venn17'))
import plotter_svg  # noqa: E402
from geom import intersections, sample  # noqa: E402


def stroke(n): return 18.0 / n * PAGE / PNG_PX


# Congruent ellipses with semi-axes a and b, centred at distance d from the centre at angles
# phase - 2 pi j / n, each tilted psi off its radial direction. The 5-ellipse values were found by a
# grid search for a configuration with all 32 regions present and connected and the smallest region
# as large as possible; quals.py checks the result against the cert.
CONICS = {
    3: dict(a=1.0, b=1.0, d=0.6, psi=0.0, phase=-math.pi / 2),
    5: dict(a=1.0, b=0.5, d=0.35, psi=0.2, phase=-math.pi / 2),
}
KAPPA = 4 * (math.sqrt(2) - 1) / 3   # cubic Bezier handle length for a quarter circle


def draw_conics(n, svg):
    p = CONICS[n]
    # unit circle as four cubic spans, then the affine map of each ellipse
    c = [(1, 0), (1, KAPPA), (KAPPA, 1), (0, 1), (-KAPPA, 1), (-1, KAPPA), (-1, 0), (-1, -KAPPA),
         (-KAPPA, -1), (0, -1), (KAPPA, -1), (1, -KAPPA)]
    unit = np.array(c + c[:1], float)
    ellipses = []
    for j in range(n):
        th = p['phase'] - 2 * math.pi * j / n     # this direction matches the labelling of cert_from_xseq
        ang = th + p['psi']
        R = np.array([[math.cos(ang), -math.sin(ang)], [math.sin(ang), math.cos(ang)]])
        pts = (unit * [p['a'], p['b']]) @ R.T + p['d'] * np.array([math.cos(th), math.sin(th)])
        ellipses.append(pts)
    reach = max(float(np.linalg.norm(e, axis=1).max()) for e in ellipses)
    scale = DIAMETER / 2 / reach
    fmt = plotter_svg.fmt
    paths = []
    for e in ellipses:
        q = np.stack([e[:, 0] * scale + PAGE / 2, -e[:, 1] * scale + PAGE / 2], 1)
        spans = ' '.join(f'C{fmt(q[k,0])},{fmt(q[k,1])} {fmt(q[k+1,0])},{fmt(q[k+1,1])} '
                         f'{fmt(q[k+2,0])},{fmt(q[k+2,1])}' for k in range(1, 13, 3))
        paths.append(f'M{fmt(q[0,0])},{fmt(q[0,1])} {spans} Z')
    plotter_svg.write_svg(svg, paths, plotter_svg.palette(n), PAGE, stroke(n))


TENSION, CAP, RIM_KNOTS, BULGE = 0.9, 0.42, 5, 1.04   # the plotter's defaults


def draw_plotter(n, svg):
    """Lay out the cert's crossing graph with Dzoba's plotter (an exactly n-fold symmetric weighted
    Tutte embedding, then a radial warp), and smooth each curve with Catmull-Rom splines through its
    crossings. Smoothing can make curves cross between crossings; wherever it does, the tension at the
    crossings bounding the offending arcs is cut, by whole rotation orbits so the symmetry is kept,
    down to straight arcs, which are planar because the layout is. This is the plotter's main()
    with its planarity sweep replaced by smoothing_offenders. The layout runs in a child process, so
    the 2 GB its crossing graph takes at n = 19 is given back before smoothing_offenders takes its
    own; the two at once do not fit in the 6 GB this was built in."""
    with ProcessPoolExecutor(1, mp_context=multiprocessing.get_context('spawn')) as pool:
        knots, kvid, orb = pool.submit(plotter_layout, n).result()
    smooth(n, svg, knots, kvid, orb)


def plotter_layout(n):
    """Each curve's knots (m x 2, page coordinates), the crossing id of each knot (-1 for the extra
    knots bowing the outer ring), and the rotation orbit id of each crossing."""
    P = plotter_svg.Primal(str(cert_path(n)))
    z = plotter_svg.layout(P, iters=300, power=1.0, damp=0.5)
    # The radial warp carries the second ring of crossings out to radius `rim` (a fraction of the outer
    # ring's); it has to stay inside the n-gon of outer crossings, whose edges come within cos(pi/n)
    # of the centre. (The plotter's default, 0.95, breaks planarity for n <= 7.)
    z, _ = plotter_svg.radial_warp(z, n, rim=math.cos(math.pi / n) - 0.05, aniso=1.8)
    assert plotter_svg.layout_stats(P, z)['violations'] == 0, 'straight-line layout is not planar'
    # Knots of each curve: its crossings in cycle order, plus RIM_KNOTS points bowing each arc of the
    # outer ring outward into a petal (as in the plotter's main()).
    outer_edges = {frozenset((P.outer[t], P.outer[(t + 1) % n])) for t in range(n)}
    knots, kvid = [], []
    for cyc in P.cycles:
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
        knots.append(np.stack([np.real(pk), -np.imag(pk)], 1))
        kvid.append(np.array(vk))
    probe = np.concatenate([plotter_svg.sample_bezier(
        plotter_svg.bezier_controls(k, np.full(len(k), TENSION), CAP)[0], 8).reshape(-1, 2) for k in knots])
    scale = DIAMETER / (2.0 * float(np.linalg.norm(probe, axis=1).max()))
    return [k * scale + PAGE / 2 for k in knots], kvid, P.orb


def smooth(n, svg, knots, kvid, orb):
    tens = np.full(len(orb), TENSION)
    for attempt in range(8):
        # rounded to the SVG's three decimals, so the check sees exactly what the file will hold
        ctrl = [np.round(plotter_svg.bezier_controls(k, np.where(v >= 0, tens[np.maximum(v, 0)], TENSION), CAP)[0], 3)
                for k, v in zip(knots, kvid)]
        bad = smoothing_offenders(ctrl, kvid)
        print(f'n={n} smoothing attempt {attempt}: {len(bad)} crossings bound arcs that cross', file=sys.stderr)
        if len(bad) == 0:
            break
        hot = np.isin(orb, orb[bad])
        tens[hot] = tens[hot] * 0.35 * (attempt < 2)   # cut to 35%, and from the third try on to 0
    assert len(bad) == 0, 'smoothing still crosses after eight attempts'
    fmt = plotter_svg.fmt
    paths = [' '.join([f'M{fmt(c[0, 0, 0])},{fmt(c[0, 0, 1])}']
                      + [f'C{fmt(x1)},{fmt(y1)} {fmt(x2)},{fmt(y2)} {fmt(x3)},{fmt(y3)}'
                         for (x1, y1), (x2, y2), (x3, y3) in c[:, 1:].tolist()] + ['Z'])
             for c in ctrl]
    plotter_svg.write_svg(svg, paths, plotter_svg.palette(n), PAGE, stroke(n))


def smoothing_offenders(ctrl, kvid):
    """Crossing ids at which the sampled splines go wrong, sampled exactly as quals.py samples the SVG:
    every crossing knot must be where its two curves cross exactly once, and nothing else may cross.
    An intersection is that crossing when its two segments' spans both end at the same crossing knot.
    The offenders are the crossings bounding the arcs at a knot that gets other than one such
    intersection, and those bounding both arcs of any other intersection or degenerate contact."""
    lens = np.concatenate([np.linalg.norm(c[:, 3] - c[:, 0], axis=1) for c in ctrl])
    step = float(np.median(lens)) / 6
    polys, ends, arcs = [], [], []
    for c, v in zip(ctrl, kvid):
        pts, span = sample(c, step)
        polys.append(pts)
        ends.append(np.stack([v, np.roll(v, -1)], 1).astype(np.int32)[span])   # knot ids at the span's ends
        # the crossings bounding each span's arc: the last crossing knot at or before the span's start,
        # and the first one after it (wrapping round the closed curve)
        m = len(v)
        ar = np.arange(m)
        before = v[np.maximum.accumulate(np.where(v >= 0, ar, -1))]
        nxt = np.minimum.accumulate(np.where(v >= 0, ar, m)[::-1])[::-1]
        nxt = np.append(nxt[1:], m)
        after = v[np.where(nxt < m, nxt, int(np.flatnonzero(v >= 0)[0]))]
        arcs.append(np.stack([before, after], 1).astype(np.int32)[span])
    ca, sa, _, cb, sb, _, _, touches = intersections(polys)
    first = np.cumsum([0] + [len(x) for x in polys])            # index of each curve's first segment
    ends, arcs = np.concatenate(ends), np.concatenate(arcs)
    ea, eb = ends[first[ca] + sa], ends[first[cb] + sb]
    # the knot two crossing segments share, or -1 (in a simple Venn diagram no region has only two
    # sides, so two curves never run between the same two crossings and at most one of these four
    # comparisons can hold with id >= 0)
    shared = np.max(np.stack([np.where((ea[:, x] == eb[:, y]) & (ea[:, x] >= 0), ea[:, x], -1)
                              for x in (0, 1) for y in (0, 1)]), 0)
    knot_ok = (ca != cb) & (shared >= 0)
    V = max(int(v.max()) for v in kvid) + 1
    hits = np.bincount(shared[knot_ok], minlength=V)
    stray = [arcs[first[ca[~knot_ok]] + sa[~knot_ok]], arcs[first[cb[~knot_ok]] + sb[~knot_ok]],
             arcs[first[touches[:, 0]] + touches[:, 1]], arcs[first[touches[:, 2]] + touches[:, 3]]]
    # a knot crossed other than once is fixed by straightening the arcs at it, which takes the
    # crossings at both ends of each of those arcs
    miss = np.flatnonzero(hits != 1)
    at_miss = arcs[np.isin(ends, miss).any(1)]
    return np.unique(np.concatenate([miss, at_miss.ravel()] + [x.ravel() for x in stray]))


DRAWER = {n: (draw_conics if n in CONICS else draw_plotter) for n in DRAWN}


def draw(n):
    svg = HERE / 'img' / f'venn-{n:02d}.svg'
    DRAWER[n](n, svg)
    head = f'width="{plotter_svg.fmt(PAGE)}mm" height="{plotter_svg.fmt(PAGE)}mm" '
    text = svg.read_text()
    assert text.count(head) == 1, 'unexpected SVG header'
    svg.write_text(text.replace(head, ''))
    subprocess.run(['node', str(HERE / 'tools' / 'svg2png.mjs'), str(svg), str(svg.with_suffix('.png')),
                    str(PNG_PX)], check=True)


def main():
    cmd, args = sys.argv[1], [int(a) for a in sys.argv[2:]]
    {'certs': lambda: certs(), 'draw': lambda: [draw(n) for n in (args or DRAWN)]}[cmd]()


if __name__ == '__main__':
    main()
