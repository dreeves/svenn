"""Exact crossings of a drawing's cubic Bezier curves: certified, not sampled. Used by venn.py (smoothing check) and
quals.py (drawing check).

A drawing is curve 0, a closed path of m cubic spans (nets, m x 4 x 2, in page units), and its copies: copy d is curve 0
turned d sectors about the page centre, by deg[d] degrees as the SVG states them (deg[0] = 0), d = 0 .. n - 1. A
position on curve 0 is span + t, t from 0 to 1 along that span; a copy has the same positions. An orbit is a crossing
and its n - 1 turns by whole sectors. Every orbit of crossings of two curves holds exactly one crossing of curve 0 with
a copy d, 1 <= d <= n/2, except that for d = n/2 (n even, as n = 2 is) it holds two, the turns of each other by n/2
sectors; every orbit of crossings of a curve with itself holds exactly one of curve 0 with itself (d = 0). So
crossings() finds the crossings of curve 0 with copy d for d = 0 .. n // 2, keeping one of each such pair: one per
orbit, with no sectors.

The other pairs of curves are turned copies of those only to within the SVG's angles, which have 12 significant
digits (an angle over 100 degrees is off by up to 5e-10 degrees): the difference of the angles of curves i and j can
be off from the angle of the copy d sectors on by 1e-9 degrees (as it is for some pair at every n from 7 to 23), which
moves a point at the rim, 25000 page units out, by 4.4e-7. So the crossings found are exact for curve 0 and each copy
as the file draws them, and for the other pairs of curves up to a touch or near miss closer than that.

Nothing is sampled for the count. Each crossing reported is certified to exist, and each place where none is reported
is certified free of crossings, from the convex hulls of control points, with a margin EPS above the floating-point
error. Where neither can be certified down to pieces SMALL across (a tangency, a touch, two crossings closer than about
SMALL, or a crossing within about EPS / sin(angle) of where pieces were cut, of a sample, or of a knot where both
curves turn), the place is reported as a contact; so is a loop or cusp at a knot, where refining the samples cannot
make a piece that cannot cross itself, and two curves running within EPS of each other for a stretch (over `crowd`
pairs of their pieces undecided at once).

Jargon:
  sample   a point of curve 0 at t = (j + G)/k on a span (G the golden ratio conjugate, k samples on the span, k =
           max(kmin, ceil(length estimate / step)), step the median chord / q): never a span's end, so every knot is
           inside a piece.
  piece    the arc of curve 0 from one sample to the next (cyclically), held as two cubic sub-nets joined at its
           junction, seven control points Q0..Q6 (Q3 the junction): in a piece whose samples are on spans s and s + 1,
           the junction is the knot between them; in any other, the parameter midpoint. Its params (s1, u0, u1, s2, v0,
           v1): sub-net 1 is span s1 from t = u0 to u1, sub-net 2 is span s2 from v0 to v1.
  arm      either sub-net of a piece. Cutting a piece in three (narrow) keeps its junction in the middle part, so a knot
           where the curve turns stays a corner of a piece however small, and only its arms are free of it.
  capsule  a segment and a radius: a piece lies within its radius of its chord (from its control points); a run of
           pieces lies within its radius of the chord from its first sample to its last.
  strip tree  the binary tree of runs of pieces (Ballard, CACM 24 (1981) 310-321), each run cut at the sample
           farthest from its chord within the middle half of the run, so that a hairpin is cut at its tip and its two
           legs get thin capsules.
  cone     the arc of directions of a run's tangents: the directions of its control-net differences (centre and
           half-width; half-width inf if they are in no open half-plane). An arc whose cone has finite half-width
           cannot cross itself.
  separated, certified  two nets (pieces or arms), from their control points: separated if an axis (either chord's
           direction or normal, x, y) separates their control points by over EPS, so they do not meet; certified if
           (i) every control-net difference of one turns the same strict way to every one of the other, beyond
           rounding (so they meet at most once: a chord between two meeting points would point both ways), and (ii)
           each one's two ends lie beyond the other's fat line (the band its control points span about its chord), on
           opposite sides, by over EPS (so they meet at least once: two paths across a parallelogram between opposite
           sides meet), so they cross exactly once.
  contact  a place where neither a crossing nor the absence of one could be certified: none in a good drawing.
"""
import math

import numpy as np

from geom import cross2, rotate

G = (math.sqrt(5) - 1) / 2
DELTA = 1e-10    # page units: bound on the rounding error of the control points of a piece of copy d as computed
                 # (parsed to 1.8e-12, turned to ~1.5e-11, cut relative to a span's first point and moved back
                 # ~4e-12; the curve itself is exact)
EPS = 2 * DELTA  # margin of every comparison of two computed points' projections
SMALL = 2e-9     # page units: a pair still undecided with both pieces under this size is a contact
FRAC = 0.5   # where pieces are cut in the narrow phase
SAMPLING = (2.0, 2)  # crossings()' samples, as samples()' q and kmin: a median chord / 2 apart, at least 2 a span


def lerp(a, b, u):
    """a + u (b - a): exactly a where b == a, so a zero handle stays exactly zero through every cut (its direction
    would otherwise be noise)."""
    return a + u * (b - a)


def cut(C, f):
    """de Casteljau at f (a number, or k x 1): C (k x 4 x 2) -> the two parts."""
    p01, p12, p23 = lerp(C[:, 0], C[:, 1], f), lerp(C[:, 1], C[:, 2], f), lerp(C[:, 2], C[:, 3], f)
    p012, p123 = lerp(p01, p12, f), lerp(p12, p23, f)
    p = lerp(p012, p123, f)
    return np.stack([C[:, 0], p01, p012, p], 1), np.stack([p, p123, p23, C[:, 3]], 1)


def head(P, a, b):
    """Control nets of cubics P on [a, b], cut at a and the rest at (b - a)/(1 - a), so the point at a is exactly
    the one point() gives (and with b = 1 not cut again, so a zero handle at the end stays exactly zero). The cuts are
    made relative to each net's first point, so they add rounding only on the scale of the net."""
    o = P[:, :1]
    _, R = cut(P - o, a[:, None])
    L, _ = cut(R, ((b - a) / np.where(a < 1, 1 - a, 1.0))[:, None])
    return np.where((b == 1)[:, None, None], R, L) + o


def tail(P, a, b):
    """Control nets of cubics P on [a, b], cut at b and the first part at a / b, so the point at b is exactly the one
    point() gives (and with a = 0 not cut again)."""
    o = P[:, :1]
    L, _ = cut(P - o, b[:, None])
    _, R = cut(L, (a / np.where(b > 0, b, 1.0))[:, None])
    return np.where((a == 0)[:, None, None], L, R) + o


def point(P, t):
    """The points at t of cubics P (as head() and tail() compute them)."""
    o = P[:, :1]
    return cut(P - o, t[:, None])[1][:, 0] + o[:, 0]


def segdist(X, A, B):
    """Distance of points X from segments AB."""
    ab = B - A
    t = np.clip(((X - A) * ab).sum(-1) / np.maximum((ab * ab).sum(-1), 1e-300), 0, 1)
    return np.linalg.norm(X - (A + t[..., None] * ab), axis=-1)


# ------------------------------------------------------------------ samples and pieces
def samples(nets, q, kmin):
    """Span and t of each sample, in order along curve 0."""
    chord = np.linalg.norm(nets[:, 3] - nets[:, 0], axis=1)
    step = float(np.median(chord)) / q
    est = chord + np.linalg.norm(nets[:, 1] - nets[:, 0], axis=1) + np.linalg.norm(nets[:, 2] - nets[:, 3], axis=1)
    k = np.maximum(kmin, np.ceil(est / step)).astype(np.int64)
    span = np.repeat(np.arange(len(nets), dtype=np.int32), k)
    j = np.arange(k.sum()) - np.repeat(np.cumsum(k) - k, k)
    return span, (j + G) / k[span]


def piece_params(span, t, i):
    """Params (s1, u0, u1, s2, v0, v1) of pieces i, as a k x 6 float array (spans exact as floats)."""
    i2 = (i + 1) % len(span)
    s1, s2 = span[i], span[i2]
    same = s1 == s2
    u0, v1 = t[i], t[i2]
    mid = 0.5 * (u0 + v1)
    return np.stack([s1, u0, np.where(same, mid, 1.0), s2, np.where(same, mid, 0.0), v1], 1).astype(float)


def nets7(nets, par):
    """The seven control points of the pieces with params par: Q0 and Q6 exactly the points point() gives at the two
    samples, Q3 sub-net 1's end (sub-net 2's start agrees with it to rounding)."""
    A = head(nets[par[:, 0].astype(np.int64)], par[:, 1], par[:, 2])
    B = tail(nets[par[:, 3].astype(np.int64)], par[:, 4], par[:, 5])
    return np.concatenate([A, B[:, 1:]], 1)


def cone_of(D):
    """Centre and half-width of the arc of directions of the nonzero vectors D (k x j x 2); half-width inf where they
    are in no open half-plane."""
    nz = (D != 0).any(2)
    ref = D[np.arange(len(D)), np.argmax(nz, 1)]
    phi = np.arctan2(cross2(ref[:, None], D), (ref[:, None] * D).sum(2))
    lo, hi = np.where(nz, phi, np.inf).min(1), np.where(nz, phi, -np.inf).max(1)
    ok = nz.any(1) & (hi - lo < math.pi - 1e-6)
    with np.errstate(invalid='ignore'):
        return np.where(ok, np.arctan2(ref[:, 1], ref[:, 0]) + 0.5 * (lo + hi), 0.0), \
            np.where(ok, 0.5 * (hi - lo) + 1e-6, np.inf)


def cone_union(c1, w1, c2, w2):
    """The cone covering two cones."""
    delta = np.remainder(c2 - c1 + math.pi, 2 * math.pi) - math.pi
    with np.errstate(invalid='ignore'):
        lo, hi = np.minimum(-w1, delta - w2), np.maximum(w1, delta + w2)
        ok = np.isfinite(lo) & np.isfinite(hi) & (hi - lo < math.pi - 1e-6)
        return np.where(ok, c1 + 0.5 * (lo + hi), 0.0), np.where(ok, 0.5 * (hi - lo), np.inf)


def unsimple(c0, w0):
    """Pieces whose cone, or the cone of them and a neighbour, is not finite."""
    _, wu = cone_union(c0, w0, np.roll(c0, -1), np.roll(w0, -1))
    bad = ~np.isfinite(w0) | ~np.isfinite(wu)
    return bad | np.roll(~np.isfinite(wu), 1)


def refine(span, t, bad):
    """Samples with two added inside each piece marked bad, where narrow() would cut it in three; and for each sample
    its index before, -1 if added."""
    par = piece_params(span, t, np.flatnonzero(bad))
    M = len(span)
    span = np.concatenate([span, par[:, 0].astype(np.int32), par[:, 3].astype(np.int32)])
    t = np.concatenate([t, 0.5 * (par[:, 1] + par[:, 2]), 0.5 * (par[:, 4] + par[:, 5])])
    old = np.r_[np.arange(M), np.full(2 * len(par), -1)]
    o = np.lexsort((t, span))
    span, t, old = span[o], t[o], old[o]
    assert ((span[1:] != span[:-1]) | (t[1:] != t[:-1])).all(), 'a sample added twice'
    return span, t, old


def piece_stats(nets, span, t, idx, chunk=1 << 18):
    """Capsule radius (largest distance of a piece's control points from its chord, plus EPS) and cone of pieces idx."""
    r0, c0, w0 = np.empty(len(idx)), np.empty(len(idx)), np.empty(len(idx))
    for a in range(0, len(idx), chunk):
        i = idx[a:a + chunk]
        Q = nets7(nets, piece_params(span, t, i))
        r0[a:a + len(i)] = segdist(Q, Q[:, :1], Q[:, 6:]).max(1) + EPS
        c, w = cone_of(np.diff(Q, axis=1))
        c0[a:a + len(i)], w0[a:a + len(i)] = c, np.where(np.isfinite(w), w + 1e-6, np.inf)
    return r0, c0, w0


def leaves(nets, rounds=6):
    """The samples (span, t), their points P (M x 2, from point(), so each piece's Q0 and Q6 are exactly its two
    samples), and each piece's capsule radius and cone: with pieces that could cross themselves, alone or with a
    neighbour (cone not finite), cut in three, as often as needed up to `rounds` times."""
    span, t = samples(nets, *SAMPLING)
    P = point(nets[span], t)
    r0, c0, w0 = piece_stats(nets, span, t, np.arange(len(span)))
    for _ in range(rounds):
        bad = unsimple(c0, w0)
        if not bad.any():
            break
        M = len(span)
        span, t, old = refine(span, t, bad)
        kept = old >= 0
        P2 = np.empty((len(span), 2))
        P2[kept] = P[old[kept]]
        P2[~kept] = point(nets[span[~kept]], t[~kept])
        nxt = np.roll(old, -1)
        same = kept & (nxt == (old + 1) % M)
        r1, c1, w1 = np.empty(len(span)), np.empty(len(span)), np.empty(len(span))
        r1[same], c1[same], w1[same] = r0[old[same]], c0[old[same]], w0[old[same]]
        redo = np.flatnonzero(~same)
        r1[redo], c1[redo], w1[redo] = piece_stats(nets, span, t, redo)
        P, r0, c0, w0 = P2, r1, c1, w1
    return span, t, P, r0, c0, w0


# ------------------------------------------------------------------ strip tree
def seg_d2(x, y, ax, ay, vx, vy):
    """Squared distance of points (x, y) from segments from (ax, ay) along (vx, vy)."""
    wx, wy = x - ax, y - ay
    t = np.clip((wx * vx + wy * vy) / np.maximum(vx * vx + vy * vy, 1e-300), 0, 1)
    ex, ey = wx - t * vx, wy - t * vy
    return ex * ex + ey * ey


def meets(ax, ay, bx, by, cx, cy, dx, dy, R):
    """Whether segments AB and CD (coordinates as 1-D arrays) come within R of each other."""
    R2 = R * R
    rx, ry, sx, sy = bx - ax, by - ay, dx - cx, dy - cy
    near = (seg_d2(ax, ay, cx, cy, sx, sy) <= R2) | (seg_d2(bx, by, cx, cy, sx, sy) <= R2) \
        | (seg_d2(cx, cy, ax, ay, rx, ry) <= R2) | (seg_d2(dx, dy, ax, ay, rx, ry) <= R2)
    c1, c2 = rx * (cy - ay) - ry * (cx - ax), rx * (dy - ay) - ry * (dx - ax)
    c3, c4 = sx * (ay - cy) - sy * (ax - cx), sx * (by - cy) - sy * (bx - cx)
    return near | ((c1 * c2 < 0) & (c3 * c4 < 0))


class Tree:
    """Strip tree over pieces 0 .. M-1, nodes 0 .. 2M-2: internal nodes 0 .. M-2 (0 the root, each generation after
    the one before), piece i is node M - 1 + i. Per node: s, e (samples: its run is pieces s .. e-1 cyclically, its
    chord from sample s to sample e, e < M), rad, cone (c, w), kid (two node ids, -1 for a piece)."""

    def __init__(self, P, r0, c0, w0, chunk=1 << 20):
        M = self.M = len(P)
        I = M - 1
        px, py = P[:, 0].copy(), P[:, 1].copy()
        s, e = np.empty(2 * M - 1, np.int32), np.empty(2 * M - 1, np.int32)
        rad, kid = np.empty(2 * M - 1), np.full((2 * M - 1, 2), -1, np.int32)
        s[I:], e[I:], rad[I:] = np.arange(M), (np.arange(M) + 1) % M, r0
        gens = []
        gs, ge, gid = np.array([0]), np.array([M]), np.array([0])
        nxt = 1
        while len(gs):
            r, cut = self.scan(px, py, r0, gs, ge, chunk)
            s[gid], e[gid], rad[gid] = gs, ge % M, r
            gens.append(gid)
            ls, le = np.stack([gs, cut], 1), np.stack([cut, ge], 1)          # the two children's runs
            k = np.empty((len(gs), 2), np.int64)
            inner = (le - ls) > 1
            k[~inner] = I + ls[~inner]
            k[inner] = nxt + np.arange(inner.sum())
            nxt += int(inner.sum())
            kid[gid] = k
            gs, ge, gid = ls[inner], le[inner], k[inner]
        assert nxt == I
        c, w = np.zeros(2 * M - 1), np.full(2 * M - 1, np.inf)
        c[I:], w[I:] = c0, w0
        for gid in reversed(gens):
            a, b = kid[gid, 0], kid[gid, 1]
            c[gid], w[gid] = cone_union(c[a], w[a], c[b], w[b])
        self.s, self.e, self.rad, self.kid, self.c, self.w = s, e, rad, kid, c, w

    @staticmethod
    def scan(px, py, r0, gs, ge, chunk):
        """For runs [gs, ge) of 2 or more pieces (disjoint): the radius of each run's capsule, the largest over its
        pieces of the distance of the piece's chord from the run's chord plus the piece's radius; and where to cut it,
        the sample farthest from the run's chord among those in the middle half of the run (the first if several)."""
        M = len(px)
        size = ge - gs
        cum = np.cumsum(size)
        total = int(cum[-1])
        rad = np.zeros(len(gs))
        best, arg = np.full(len(gs), -1.0), np.full(len(gs), -1, np.int64)
        lo, hi = np.maximum(1, size // 4), np.minimum(size - 1, size - size // 4)
        ex, ey = px[ge % M], py[ge % M]
        for a in range(0, total, chunk):
            b = min(a + chunk, total)
            k0, k1 = np.searchsorted(cum, [a, b - 1], side='right')
            ks = np.arange(k0, k1 + 1)
            cnt = np.minimum(cum[ks], b) - np.maximum(cum[ks] - size[ks], a)
            node = np.repeat(ks, cnt)
            off = np.arange(a, b) - (cum[node] - size[node])
            idx = gs[node] + off
            ax, ay = px[gs[node]], py[gs[node]]
            vx, vy = ex[node] - ax, ey[node] - ay
            d2 = seg_d2(px[idx], py[idx], ax, ay, vx, vy)
            nx = (idx + 1) % M
            d2n = seg_d2(px[nx], py[nx], ax, ay, vx, vy)
            val = np.sqrt(np.maximum(d2, d2n)) * (1 + 1e-15) + r0[idx]
            masked = np.where((off >= lo[node]) & (off <= hi[node]), d2, -1.0)
            runs = np.r_[0, np.cumsum(cnt)[:-1]]
            rad[ks] = np.maximum(rad[ks], np.maximum.reduceat(val, runs))
            m = np.maximum.reduceat(masked, runs)
            run_of = np.repeat(np.arange(len(ks)), cnt)
            hit = np.flatnonzero(masked == m[run_of])
            first = hit[np.r_[True, run_of[hit][1:] != run_of[hit][:-1]]]
            better = m > best[ks]
            best[ks[better]], arg[ks[better]] = m[better], idx[first][better]
        assert ((arg > gs) & (arg < ge)).all(), 'a run of two or more pieces has no cut'
        return rad, arg


def pairs(T, P, Pd, self_pairs, chunk=1 << 19, cap=1 << 22):
    """Yield (a, b, local), arrays of piece indices: pieces of curve 0 (a) and of the copy whose samples are Pd (b)
    whose capsules meet, found by descending both strip trees together, always cutting the node of a pair with the
    larger capsule. With self_pairs (Pd is P) only a <= b; and a node paired with itself or with its neighbour along
    the curve (they meet at a shared sample) is dropped where their cone is finite, and yielded as `local` where it is
    not even for single pieces. Breadth first, a frontier over `cap` pairs taken in parts."""
    I = T.M - 1
    px, py, qx, qy = P[:, 0].copy(), P[:, 1].copy(), Pd[:, 0].copy(), Pd[:, 1].copy()
    todo = [(np.zeros(1, np.int64), np.zeros(1, np.int64))]
    while todo:
        fa, fb = todo.pop()
        if len(fa) > cap:
            h = len(fa) // 2
            todo += [(fa[h:], fb[h:]), (fa[:h], fb[:h])]
            continue
        nxt_a, nxt_b, out_a, out_b, out_l = [], [], [], [], []
        for q in range(0, len(fa), chunk):
            a, b = fa[q:q + chunk], fb[q:q + chunk]
            sa, ea, sb, eb = T.s[a], T.e[a], T.s[b], T.e[b]
            keep = meets(px[sa], py[sa], px[ea], py[ea], qx[sb], qy[sb], qx[eb], qy[eb], T.rad[a] + T.rad[b] + EPS)
            local = np.zeros(len(a), bool)
            if self_pairs:
                local = (a == b) | (ea == sb) | (eb == sa)
                _, wu = cone_union(T.c[a], T.w[a], T.c[b], T.w[b])
                keep &= ~local | ~np.isfinite(wu)
            a, b, local = a[keep], b[keep], local[keep]
            la, lb = a >= I, b >= I
            done = la & lb
            out_a.append(a[done & ~local] - I)
            out_b.append(b[done & ~local] - I)
            out_l.append(a[done & local] - I)
            a, b, la, lb = a[~done], b[~done], la[~done], lb[~done]
            if self_pairs:
                same = a == b
                c1, c2 = T.kid[a[same], 0], T.kid[a[same], 1]
                nxt_a.append(np.concatenate([c1, c1, c2]))
                nxt_b.append(np.concatenate([c1, c2, c2]))
                a, b, la, lb = a[~same], b[~same], la[~same], lb[~same]
            split_a = ~la & (lb | (T.rad[a] >= T.rad[b]))
            xa, xb, ya, yb = a[split_a], b[split_a], a[~split_a], b[~split_a]
            nxt_a.append(np.concatenate([T.kid[xa, 0], T.kid[xa, 1], ya, ya]))
            nxt_b.append(np.concatenate([xb, xb, T.kid[yb, 0], T.kid[yb, 1]]))
        yield np.concatenate(out_a), np.concatenate(out_b), np.concatenate(out_l)
        na, nb = np.concatenate(nxt_a), np.concatenate(nxt_b)
        if len(na):
            todo.append((na, nb))


# ------------------------------------------------------------------ narrow phase
def separated(Qa, Qb):
    """Where an axis (either chord's direction or normal, x or y) separates the control points by over EPS."""
    out = np.zeros(len(Qa), bool)
    for Q in (Qa, Qb):
        c = Q[:, -1] - Q[:, 0]
        c = c / np.maximum(np.linalg.norm(c, axis=1), 1e-300)[:, None]
        for ax in (c, np.stack([-c[:, 1], c[:, 0]], 1)):
            pa, pb = (Qa * ax[:, None]).sum(2), (Qb * ax[:, None]).sum(2)
            out |= (pa.max(1) < pb.min(1) - EPS) | (pb.max(1) < pa.min(1) - EPS)
    for x in (0, 1):
        out |= (Qa[:, :, x].max(1) < Qb[:, :, x].min(1) - EPS) | (Qb[:, :, x].max(1) < Qa[:, :, x].min(1) - EPS)
    return out


def transversal(Qa, Qb, la, lb):
    """Where every nonzero control-net difference of one turns the same strict way to every one of the other, beyond
    the rounding of control points of pieces la, lb (fractions of a first piece, whose points are within DELTA)."""
    Da, Db = np.diff(Qa, axis=1), np.diff(Qb, axis=1)
    na, nb = np.linalg.norm(Da, axis=2), np.linalg.norm(Db, axis=2)
    c = cross2(Da[:, :, None], Db[:, None, :])
    err = 6 * DELTA * (la[:, None, None] * nb[:, None, :] + lb[:, None, None] * na[:, :, None]) \
        + 1e-12 * na[:, :, None] * nb[:, None, :]
    live = (na[:, :, None] > 0) & (nb[:, None, :] > 0)
    big = np.abs(c) > err
    pos = np.all(~live | (big & (c > 0)), (1, 2))
    neg = np.all(~live | (big & (c < 0)), (1, 2))
    return (pos | neg) & live.any((1, 2))


def straddles(Qa, Qb):
    """Where Qa's two ends lie beyond Qb's fat line, on opposite sides, by over EPS."""
    c = Qb[:, -1] - Qb[:, 0]
    nrm = np.stack([-c[:, 1], c[:, 0]], 1) / np.maximum(np.linalg.norm(c, axis=1), 1e-300)[:, None]
    db = ((Qb - Qb[:, :1]) * nrm[:, None]).sum(2)
    lo, hi = db.min(1) - EPS, db.max(1) + EPS
    e0, e1 = ((Qa[:, 0] - Qb[:, 0]) * nrm).sum(1), ((Qa[:, -1] - Qb[:, 0]) * nrm).sum(1)
    return ((e0 < lo) & (e1 > hi)) | ((e1 < lo) & (e0 > hi))


def certified(Qa, Qb, la, lb):
    """Where nets Qa and Qb (pieces or arms) are certified to cross exactly once."""
    return transversal(Qa, Qb, la, lb) & straddles(Qa, Qb) & straddles(Qb, Qa)


def split3(Q, par, f):
    """Each piece in three, cut at fraction f of each sub-net: the first part of sub-net 1 (itself cut at f), the
    middle (rest of sub-net 1 and first part of sub-net 2: the junction stays inside), the rest of sub-net 2 (cut at
    f). Returns (Q, par) of 3k pieces, in that order."""
    A1, A2 = cut(Q[:, :4], f)
    B1, B2 = cut(Q[:, 3:], f)
    L1, L2 = cut(A1, f)
    R1, R2 = cut(B2, f)
    s1, u0, u1, s2, v0, v1 = par.T
    um, vm = lerp(u0, u1, f), lerp(v0, v1, f)
    uq, vq = lerp(u0, um, f), lerp(vm, v1, f)
    return (np.concatenate([np.concatenate([L1, L2[:, 1:]], 1), np.concatenate([A2, B1[:, 1:]], 1),
                            np.concatenate([R1, R2[:, 1:]], 1)]),
            np.concatenate([np.stack([s1, u0, uq, s1, uq, um], 1), np.stack([s1, um, u1, s2, v0, vm], 1),
                            np.stack([s2, vm, vq, s2, vq, v1], 1)]))


def arm_piece(Q, par, x):
    """Arm x (0 or 1) of pieces Q, par as a piece of its own, for locate(): the sub-net cut at its parameter
    midpoint."""
    L, R = cut(Q[:, 3 * x:3 * x + 4], 0.5)
    s, u0, u1 = par[:, 3 * x:3 * x + 3].T
    um = lerp(u0, u1, 0.5)
    return np.concatenate([L, R[:, 1:]], 1), np.stack([s, u0, um, s, um, u1], 1)


def narrow(Qa, Qb, pa, pb, f, crowd=1024, maxlive=2_000_000):
    """Resolve pairs of pieces (control points Qa, Qb, params pa, pb), in coordinates re-centred on each pair at every
    step. A pair is settled when it is separated or certified, or else when each of its four pairs of arms is: then its
    crossings are its certified pairs of arms. (That is what certifies a crossing where both curves turn at knots near
    each other, as straight arcs do: no pair of pieces holding both corners can be certified, and cutting keeps both.)
    Each pair still unsettled has its larger piece cut in three (split3), and the work goes on with the parts.
    Returns (crossings, contacts): crossings as (tag, Qa, Qb, pa, pb) of pairs of pieces certified to cross exactly
    once (Q in local coordinates; an arm as a piece of its own); contacts as (tag, (span a, t a, span b, t b) of the
    two pieces' junctions) of pairs still unsettled under SMALL, and of input pairs with over `crowd` pairs unsettled at
    once (one contact each: the curves run within EPS of each other for a while); tag is the index of the input
    pair."""
    k = len(Qa)
    tag, la, lb, org = np.arange(k), np.ones(k), np.ones(k), Qa[:, 0].copy()
    Qa, Qb = Qa - org[:, None], Qb - org[:, None]
    junction = lambda p: p[:, [0, 2]]           # span and parameter of a piece's junction
    found, unres = [(tag[:0], Qa[:0], Qb[:0], pa[:0], pb[:0])], [(tag[:0], pa[:0, :4])]
    while len(Qa):
        assert len(Qa) < maxlive, len(Qa)
        sh = Qa[:, 0].copy()                      # re-centre
        Qa, Qb, org = Qa - sh[:, None], Qb - sh[:, None], org + sh
        go = ~separated(Qa, Qb)
        Qa, Qb, pa, pb, tag, la, lb, org = (x[go] for x in (Qa, Qb, pa, pb, tag, la, lb, org))
        done = certified(Qa, Qb, la, lb)
        found.append((tag[done], Qa[done], Qb[done], pa[done], pb[done]))
        i = np.flatnonzero(~done)                 # the others, arm by arm
        arm = lambda Q, x: Q[i, 3 * x:3 * x + 4]
        xy = [(x, y) for x in (0, 1) for y in (0, 1)]
        one = [certified(arm(Qa, x), arm(Qb, y), la[i], lb[i]) for x, y in xy]
        settled = np.logical_and.reduce([o | separated(arm(Qa, x), arm(Qb, y)) for o, (x, y) in zip(one, xy)])
        for o, (x, y) in zip(one, xy):
            h = i[o & settled]
            (A, ra), (B, rb) = arm_piece(Qa[h], pa[h], x), arm_piece(Qb[h], pb[h], y)
            found.append((tag[h], A, B, ra, rb))
        done[i] = settled
        ea, eb = np.ptp(Qa, 1).max(1), np.ptp(Qb, 1).max(1)
        small = ~done & (ea < SMALL) & (eb < SMALL)
        unres.append((tag[small], np.hstack([junction(pa[small]), junction(pb[small])])))
        go = ~done & ~small
        Qa, Qb, pa, pb, tag, la, lb, org, ea, eb = (x[go] for x in (Qa, Qb, pa, pb, tag, la, lb, org, ea, eb))
        sa = ea >= eb                             # cut the larger piece of each pair
        Xa, xa = split3(Qa[sa], pa[sa], f)
        Xb, xb = split3(Qb[~sa], pb[~sa], f)
        rep = lambda x, m: np.concatenate([x[m]] * 3)
        Qa, pa = np.concatenate([Xa, rep(Qa, ~sa)]), np.concatenate([xa, rep(pa, ~sa)])
        Qb, pb = np.concatenate([rep(Qb, sa), Xb]), np.concatenate([rep(pb, sa), xb])
        la = np.concatenate([rep(la, sa) * max(f, 1 - f), rep(la, ~sa)])
        lb = np.concatenate([rep(lb, sa), rep(lb, ~sa) * max(f, 1 - f)])
        tag, org = np.concatenate([rep(tag, sa), rep(tag, ~sa)]), np.concatenate([rep(org, sa), rep(org, ~sa)])
        many = np.bincount(tag, minlength=k) > crowd
        if many.any():
            first = np.unique(tag, return_index=True)[1]
            first = first[many[tag[first]]]
            unres.append((tag[first], np.hstack([junction(pa[first]), junction(pb[first])])))
            go = ~many[tag]
            Qa, Qb, pa, pb, tag, la, lb, org = (x[go] for x in (Qa, Qb, pa, pb, tag, la, lb, org))
    cat = lambda xs, j: np.concatenate([x[j] for x in xs])
    return tuple(cat(found, j) for j in range(5)), tuple(cat(unres, j) for j in range(2))


def bez(C, t):
    """The points at t of cubics C (k x 4 x 2), from the Bernstein form, for Newton's method."""
    t = t[:, None]
    return (1 - t) ** 3 * C[:, 0] + 3 * (1 - t) ** 2 * t * C[:, 1] + 3 * (1 - t) * t ** 2 * C[:, 2] + t ** 3 * C[:, 3]


def dbez(C, t):
    """The derivatives at t of cubics C."""
    t = t[:, None]
    return 3 * ((1 - t) ** 2 * (C[:, 1] - C[:, 0]) + 2 * (1 - t) * t * (C[:, 2] - C[:, 1])
                + t ** 2 * (C[:, 3] - C[:, 2]))


def locate(Qa, Qb, pa, pb, iters=60):
    """(span a, t a, span b, t b) of the one crossing of each certified pair: Newton's method on a pair of sub-nets,
    from the crossing of their chords, until the two points are within 1e-13 or a step is under 1e-15, taken where it
    lands inside both (to 1e-12) with the points within 1e-9 (local coordinates); the four pairs of sub-nets tried in
    turn, first the one where the pieces' chords cross. Every pair must be located: it is certified to cross."""
    k = len(Qa)
    out, ok = np.full((k, 4), np.nan), np.zeros(k, bool)

    def side(Q, w):                             # 1 where the chords' crossing is past the junction along Q's chord
        c = Q[:, 6] - Q[:, 0]
        return (((w - Q[:, 0]) * c).sum(1) > ((Q[:, 3] - Q[:, 0]) * c).sum(1)).astype(int)
    r, s, w = Qa[:, 6] - Qa[:, 0], Qb[:, 6] - Qb[:, 0], Qb[:, 0] - Qa[:, 0]
    with np.errstate(divide='ignore', invalid='ignore'):
        X = Qa[:, 0] + np.nan_to_num(cross2(w, s) / cross2(r, s))[:, None] * r
    xa, xb = side(Qa, X), side(Qb, X)
    for x0, y0 in ((0, 0), (0, 1), (1, 0), (1, 1)):
        i = np.flatnonzero(~ok)
        x, y = np.abs(xa[i] - x0), np.abs(xb[i] - y0)
        A = Qa[i[:, None], 3 * x[:, None] + np.arange(4)]
        B = Qb[i[:, None], 3 * y[:, None] + np.arange(4)]
        r, s, w = A[:, 3] - A[:, 0], B[:, 3] - B[:, 0], B[:, 0] - A[:, 0]
        with np.errstate(divide='ignore', invalid='ignore'):
            t = np.clip(np.nan_to_num(cross2(w, s) / cross2(r, s), nan=0.5), 0, 1)
            u = np.clip(np.nan_to_num(cross2(w, r) / cross2(r, s), nan=0.5), 0, 1)
        live = np.arange(len(i))
        for _ in range(iters):
            if not len(live):
                break
            Al, Bl, tl, ul = A[live], B[live], t[live], u[live]
            F = bez(Al, tl) - bez(Bl, ul)
            Ja, Jb = dbez(Al, tl), -dbez(Bl, ul)
            det = cross2(Ja, Jb)
            with np.errstate(divide='ignore', invalid='ignore'):
                dt, du = cross2(F, Jb) / det, cross2(Ja, F) / det
            good = np.isfinite(dt) & np.isfinite(du)
            t[live] = np.where(good, np.clip(tl - dt, -0.5, 1.5), tl)
            u[live] = np.where(good, np.clip(ul - du, -0.5, 1.5), ul)
            live = live[good & (np.abs(dt) + np.abs(du) > 1e-15) & (np.abs(F).max(1) > 1e-13)]
        res = np.linalg.norm(bez(A, t) - bez(B, u), axis=1)
        acc = (t >= -1e-12) & (t <= 1 + 1e-12) & (u >= -1e-12) & (u <= 1 + 1e-12) & (res < 1e-9)
        j, x, y = i[acc], x[acc], y[acc]
        tt, uu = np.clip(t[acc], 0, 1), np.clip(u[acc], 0, 1)
        out[j] = np.stack([pa[j, 3 * x], lerp(pa[j, 3 * x + 1], pa[j, 3 * x + 2], tt),
                           pb[j, 3 * y], lerp(pb[j, 3 * y + 1], pb[j, 3 * y + 2], uu)], 1)
        ok[j] = True
    assert ok.all(), f'{int((~ok).sum())} certified crossings not located by Newton\'s method'
    return out


# ------------------------------------------------------------------ driver
def crossings(nets, page, deg):
    """Every crossing of curve 0 (control nets `nets`) with copy d (turned deg[d] degrees), for d = 0 .. n // 2,
    n = len(deg), one per orbit. Returns (X, C): X a (K x 5) array with a row (d, span a, t a, span b, t b) per
    crossing, a on curve 0 and b on copy d (b a span of curve 0, turned), sorted; C a (J x 5) array of contacts, places
    where neither a crossing nor its absence could be certified (see the module docstring), each as the same five
    numbers for the junctions of the two pieces left undecided (for d = n/2, a contact may be listed twice, once from
    each curve)."""
    n = len(deg)
    assert deg[0] == 0, deg[0]
    assert np.array_equal(nets[:, 3], np.roll(nets[:, 0], -1, 0)), 'curve 0 is not one closed curve'
    zero = np.all(nets == nets[:, :1], axis=(1, 2))
    assert not zero.any(), f'spans {np.flatnonzero(zero)[:10].tolist()} have length zero'
    span, t, P, r0, c0, w0 = leaves(nets)
    T = Tree(P, r0, c0, w0)
    X, C = [np.zeros((0, 5))], [np.zeros((0, 5))]

    def resolve(d, a, b, f):
        pa, pb = piece_params(span, t, a), piece_params(span, t, b)
        Qa, Qb = nets7(nets, pa), rotate(nets7(nets, pb), page, deg[d])
        (tag, Xa, Xb, xa, xb), (utag, uloc) = narrow(Qa, Qb, pa, pb, f)
        return tag, locate(Xa, Xb, xa, xb), utag, uloc

    for d in range(n // 2 + 1):
        Pd = rotate(P, page, deg[d])
        buf = []

        def flush():
            a, b = np.concatenate([x[0] for x in buf]), np.concatenate([x[1] for x in buf])
            tag, loc, utag, uloc = resolve(d, a, b, FRAC)
            X.append(np.column_stack([np.full(len(loc), d), loc]))
            C.append(np.column_stack([np.full(len(uloc), d), uloc]))
            buf.clear()
        for a, b, local in pairs(T, P, Pd, d == 0):
            lp = piece_params(span, t, local)[:, [0, 2]]
            C.append(np.column_stack([np.full(len(local), d), lp, lp]))
            buf.append((a, b))
            if sum(len(x[0]) for x in buf) >= 1 << 17:   # leaf pairs resolved at a time, to bound memory
                flush()
        if buf:
            flush()
    X, C = np.concatenate(X), np.concatenate(C)
    # for d = n/2 (n even) each orbit was found twice, as a crossing at a on curve 0 and b on the copy and as the one at
    # b on curve 0 and a on the copy: keep the one with a before b
    X = X[(2 * X[:, 0] < n) | (X[:, 1] + X[:, 2] < X[:, 3] + X[:, 4])]
    return X[np.lexsort((X[:, 2], X[:, 1], X[:, 0]))], C
