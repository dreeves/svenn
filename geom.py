"""Geometry shared by venn.py (smoothing check) and quals.py (drawing check)."""
import math
import re

import numpy as np
from scipy.spatial import cKDTree


def cross2(u, v): return u[..., 0] * v[..., 1] - u[..., 1] * v[..., 0]


def nets(d):
    """The (k x 4 x 2) cubic Bezier control nets of a closed SVG path "M x,y C ... Z" made only of C commands, as the
    drawings' paths are."""
    nums = np.array(re.findall(r'-?\d+(?:\.\d+)?', d), float).reshape(-1, 2)
    assert d.startswith('M') and d.rstrip().endswith('Z') and set(re.findall(r'[A-Za-z]', d)) == {'M', 'C', 'Z'}, d[:80]
    start, rest = nums[0], nums[1:].reshape(-1, 3, 2)
    p0 = np.vstack([start, rest[:-1, 2]])
    return np.concatenate([p0[:, None], rest], 1)


def rotate(points, page, degrees):
    """Points (... x 2) rotated about the centre of a page-unit square page as SVG's rotate(degrees cx cy) does."""
    a = math.radians(degrees)
    c = page / 2
    return (points - c) @ np.array([[math.cos(a), math.sin(a)], [-math.sin(a), math.cos(a)]]) + c


def candidate_pairs(mid, r, budget=4_000_000):
    """Yield, a batch at a time, arrays (i, j) of every pair i < j of points within distance r, each
    pair once, so memory stays bounded however crowded the points are: a batch is a run of consecutive
    points, cut where the running count of their neighbours within r passes a multiple of `budget`,
    searched against all the points, so it holds fewer than `budget` pairs plus the neighbours of one
    point."""
    tree = cKDTree(mid)
    count = np.cumsum(tree.query_ball_point(mid, r, return_length=True))   # ordered pairs, self included
    cuts = np.unique(np.searchsorted(count, np.arange(budget, count[-1], budget), side='right'))
    for g0, g1 in zip(np.r_[0, cuts], np.r_[cuts, len(mid)]):
        p = cKDTree(mid[g0:g1]).sparse_distance_matrix(tree, r, output_type='ndarray')
        i, j = p['i'] + g0, p['j']
        yield i[i < j], j[i < j]


def sample(nets, step):
    """Polyline through each cubic span with ceil(chord/step) points (at least 4), and the span of each
    point. The points sit at
    t = (j + g)/k with g the golden ratio conjugate, never at the span ends and never symmetric about a
    span's middle: a drawing's crossings may be knots shared by two curves, and sampling there, or at
    mirror-image positions on straight spans through a knot, would make the two polylines touch
    instead of cross."""
    chord = np.linalg.norm(nets[:, 3] - nets[:, 0], axis=1) + np.linalg.norm(nets[:, 1] - nets[:, 0], axis=1) \
        + np.linalg.norm(nets[:, 2] - nets[:, 3], axis=1)
    k = np.maximum(4, np.ceil(chord / step)).astype(int)
    span = np.repeat(np.arange(len(nets)), k)
    t = (np.arange(k.sum()) - np.repeat(np.cumsum(k) - k, k) + (math.sqrt(5) - 1) / 2) / k[span]
    t = t[:, None]
    P = nets[span]
    return ((1 - t) ** 3 * P[:, 0] + 3 * (1 - t) ** 2 * t * P[:, 1]
            + 3 * (1 - t) * t ** 2 * P[:, 2] + t ** 3 * P[:, 3]), span


def segment_hits(A, B, cid, sid, nseg, i, j):
    """The candidate pairs (i, j) whose segments properly intersect, with the parameters t (along i)
    and u (along j) of the intersection point, and the pairs that touch degenerately. Neighbouring
    segments of one curve are skipped."""
    same = cid[i] == cid[j]
    adjacent = same & (((sid[i] - sid[j]) % nseg[i] == 1) | ((sid[j] - sid[i]) % nseg[i] == 1))
    i, j = i[~adjacent], j[~adjacent]
    p, r = A[i], B[i] - A[i]
    q, s = A[j], B[j] - A[j]
    den = cross2(r, s)
    with np.errstate(invalid='ignore'):
        t = cross2(q - p, s) / np.where(den == 0, np.nan, den)
        u = cross2(q - p, r) / np.where(den == 0, np.nan, den)
    hit = (t >= 0) & (t < 1) & (u >= 0) & (u < 1)
    # collinear segments touch if their spans along segment i's direction overlap
    rr = np.maximum((r * r).sum(1), 1e-300)
    s0, s1 = ((q - p) * r).sum(1) / rr, ((q + s - p) * r).sum(1) / rr
    overlap = np.maximum(np.minimum(s0, s1), 0) <= np.minimum(np.maximum(s0, s1), 1)
    touch = hit & ((t == 0) | (u == 0)) | ((den == 0) & (cross2(q - p, r) == 0) & overlap)
    hit &= ~touch
    return i[hit], j[hit], t[hit], u[hit], i[touch], j[touch]
