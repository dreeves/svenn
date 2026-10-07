"""Certs read straight into numpy arrays, and the crossing graph a cert describes, also held in numpy arrays, so that
both scale to n = 23 (8,388,606 crossings, an 889 MB cert), where json.loads and a Python object per crossing would
take tens of GB.

Jargon (label, face and cert are defined in quals.py):
  crossing graph  the diagram itself as a plane graph: its vertices are the crossings and its edges the arcs of the
         curves between them. The cert is its dual. Dzoba's plotter calls it the primal.
  rot    the rotation of labels that a cert is symmetric under: bit i goes to bit i - 1 and bit 0 to bit n - 1 (the
         plotter's label string l to l[1:] + l[0]).
"""
import json
import math

import numpy as np

CHUNK = 1 << 18   # faces parsed at a time, to bound memory (0.2 GB of temporaries at n = 23)


def read(path, n):
    """The faces of the cert at path, as a (2^n - 2) x 4 int64 array of labels in the order listed, read at a fixed
    stride and never parsed as a whole. Asserts that each face is written ["L","L","L","L"], each L n characters 0 or 1,
    with a comma between faces and no spaces, and that the rest of the file, with the faces taken out, is a JSON object
    whose "n" is n."""
    S = 4 * n + 14                                       # bytes per face, with the comma (or the closing ]) after it
    V = (1 << n) - 2
    cols = np.concatenate([np.arange(2 + (n + 3) * j, 2 + (n + 3) * j + n) for j in range(4)])
    punct = np.frombuffer(b'["","","",""]', np.uint8)
    w = 1 << np.arange(n, dtype=np.int64)
    out, sep = np.empty((V, 4), np.int64), np.empty(V, np.uint8)
    with open(path, 'rb') as f:
        head = f.read(4096)
        start = head.index(b'"faces":[') + len(b'"faces":[')
        f.seek(start)
        for a in range(0, V, CHUNK):
            rows = np.frombuffer(f.read(min(CHUNK, V - a) * S), np.uint8).reshape(-1, S)
            assert (np.delete(rows[:, :-1], cols, 1) == punct).all(), 'the faces are not at a fixed stride'
            bits = rows[:, cols] - ord('0')
            assert (bits <= 1).all(), 'a label is not a string of 0s and 1s'
            out[a:a + len(rows)] = (bits.reshape(-1, 4, n) * w).sum(2)
            sep[a:a + len(rows)] = rows[:, -1]
        rest = json.loads(head[:start] + b']' + f.read())
    assert (sep[:-1] == ord(',')).all() and sep[-1] == ord(']'), 'the faces are not one after another'
    assert rest['n'] == n and rest['faces'] == [], (rest['n'], n)
    return out


def rot(x, n): return (x >> 1) | ((x & 1) << (n - 1))


def low_bit(x):
    """The index of the lowest set bit of each x > 0."""
    return (np.frexp((x & -x).astype(np.float64))[1] - 1).astype(np.int64)


class Primal:
    """The crossing graph of the cert faces F (as read() returns them), with its rotational structure: every array of
    the vendored plotter_svg.Primal that plotter_svg.layout() reads, with the same meaning, plus the outer face and
    curve 0's crossings in order. Crossing v is the face F[v]. (The plotter's Primal numbers the crossings in an order
    that depends on PYTHONHASHSEED; this one keeps the cert's, so a build comes out the same every time.)

    Each face is a square of the n-cube, its labels T, T|A, T|A|B, T|B for T their AND and A and B the bits of its two
    curves (a and b their indices), so it is named by (T, A|B), and the four arcs at it are named, as the dual edges
    across them, by (x, bit), x the label on the side of the arc outside that curve: (T, a), (T, b), (T|A, b), (T|B, a).
    Two faces share an arc exactly when they share a name."""

    def __init__(self, F, n):
        self.n, self.V = n, len(F)
        assert self.V == (1 << n) - 2, (self.V, n)
        T, a, b = squares(F, n)
        self.esrc, self.edst, self.ebit, self.eorb, self.n_eorb = arcs(T, a, b, n)
        self.outer = outer_face(T, a, b, n)
        rho = rotation(T, a, b, n)
        del T, a, b
        self.orb, self.kof, self.reps = orbits(rho, self.outer[0], n)
        self.norb = len(self.reps)
        # rho moves the outer face round by s places, so positions are turned by lam = e^(2 pi i s / n)
        at = {v: t for t, v in enumerate(self.outer)}
        s = self.shift = at[int(rho[self.outer[0]])]
        assert all((at[int(rho[v])] - at[v]) % n == s for v in self.outer) and math.gcd(s, n) == 1
        self.lam = np.exp(2j * math.pi * s / n)
        # the quotient system plotter_svg.solve_symmetric solves: one row per orbit, its representative's four arcs
        self.qrow = np.repeat(np.arange(self.norb), 4)
        self.qedge = (4 * self.reps[:, None] + np.arange(4)).ravel()
        self.qcol = self.orb[self.edst[self.qedge]]
        self.qlam = self.lam ** self.kof[self.edst[self.qedge]]
        self.cycle0 = curve_cycle(self.esrc, self.edst, self.ebit == 0)


def squares(F, n):
    """T, a and b of each face, asserting that it is a square of the n-cube listed in cyclic order."""
    T = F[:, 0] & F[:, 1] & F[:, 2] & F[:, 3]
    D = (F[:, 0] | F[:, 1] | F[:, 2] | F[:, 3]) ^ T
    a = low_bit(D)
    b = low_bit(D ^ (1 << a))
    assert ((1 << a) | (1 << b) == D).all(), 'a face is not a square of the cube'
    for k in range(4):
        x = F[:, k] ^ F[:, (k + 1) % 4]
        assert ((x & (x - 1)) == 0).all() and (x != 0).all(), 'a face is not listed in cyclic order'
    return T, a, b


def arcs(T, a, b, n):
    """The crossing graph's edges, as the plotter holds them: slot 4 v + j is the j-th arc at crossing v, from esrc = v
    to edst, the crossing at its other end, along curve ebit, in rotation orbit eorb (of n_eorb orbits)."""
    V = len(T)
    name = (np.stack([T, T, T | 1 << a, T | 1 << b], 1) * n + np.stack([a, b, b, a], 1)).ravel()   # x n + bit
    o = np.argsort(name, kind='stable')
    arc = name[o[0::2]]
    assert (arc == name[o[1::2]]).all() and (arc[1:] != arc[:-1]).all(), 'an arc is not at exactly two crossings'
    edst = np.empty(4 * V, np.int32)                    # the crossing at the other end of each slot's arc
    edst[o[0::2]], edst[o[1::2]] = o[1::2] // 4, o[0::2] // 4
    # the rotation takes arc (x, bit) to (rot x, bit - 1); name each orbit by its least member
    cur, least = arc, arc
    for _ in range(n - 1):
        cur = rot(cur // n, n) * n + (cur % n - 1) % n
        least = np.minimum(least, cur)
    _, orbit = np.unique(least, return_inverse=True)
    eorb = np.empty(4 * V, np.int32)
    eorb[o[0::2]], eorb[o[1::2]] = orbit, orbit
    assert (orbit.max() + 1) * n == 2 * V, 'an arc orbit has fewer than n arcs'
    return np.repeat(np.arange(V, dtype=np.int32), 4), edst, (name % n).astype(np.int8), eorb, int(orbit.max()) + 1


def outer_face(T, a, b, n):
    """The crossings round the outer face, the region labelled 0, in order: the n with T = 0, each joined to the next
    by the arc of the one curve they share, which bounds the region inside only that curve."""
    ring = np.flatnonzero(T == 0)
    curves = {int(v): (int(a[v]), int(b[v])) for v in ring}
    assert len(ring) == n and sorted(sum(curves.values(), ())) == sorted(list(range(n)) * 2), \
        'the outer face is not an n-gon with one arc of each curve'
    outer, came = [int(ring[0])], curves[int(ring[0])][0]
    for _ in range(n):
        x, y = curves[outer[-1]]
        go = y if x == came else x                       # the curve on to the next crossing
        outer.append(next(w for w in curves if w != outer[-1] and go in curves[w]))
        came = go
    assert outer[-1] == outer[0] and len(set(outer)) == n and came == curves[outer[0]][0], 'the outer face is not a cycle'
    return outer[:-1]


def rotation(T, a, b, n):
    """rho: the face that the rotation takes each face to."""
    key = T << n | 1 << a | 1 << b
    order = np.argsort(key)
    assert (np.diff(key[order]) > 0).all(), 'a face is listed twice'
    turned = rot(T, n) << n | rot(1 << a | 1 << b, n)
    pos = np.minimum(np.searchsorted(key[order], turned), len(T) - 1)
    assert (key[order][pos] == turned).all(), 'the faces are not symmetric under the rotation'
    return order[pos]


def orbits(rho, root, n):
    """The rotation orbit of each crossing (orbit 0 being root's, the rest numbered by their least crossing), kof, and
    each orbit's representative, its least crossing: v is rho^kof[v] of its orbit's representative. Asserts that root
    is the representative of its orbit, as the least crossing on the outer face is (the outer face is one orbit)."""
    V = len(rho)
    cur, least, steps = np.arange(V), np.arange(V), np.zeros(V, np.int64)
    for j in range(1, n):
        cur = rho[cur]
        m = cur < least
        least[m], steps[m] = cur[m], j
    assert (rho[cur] == np.arange(V)).all(), 'rotating n times is not the identity'
    _, orb = np.unique(least, return_inverse=True)
    kof = (n - steps) % n
    o0 = orb[root]
    orb = np.where(orb == o0, 0, orb + (orb < o0))
    reps = np.full(V // n, -1)
    reps[orb[kof == 0]] = np.flatnonzero(kof == 0)
    assert (reps >= 0).all() and reps[0] == root and orb.max() + 1 == V // n, 'an orbit has fewer than n crossings'
    assert ((kof[rho] - kof - 1) % n == 0).all() and (orb[rho] == orb).all()
    return orb, kof, reps


def curve_cycle(esrc, edst, on):
    """The crossings of one curve in order round it, from the least, given which slots are arcs of that curve."""
    src, dst = esrc[on], edst[on]
    o = np.argsort(src, kind='stable')
    src, dst = src[o], dst[o]
    assert (src[0::2] == src[1::2]).all(), 'a crossing of the curve is not on two of its arcs'
    nb = dict(zip(src[0::2].tolist(), zip(dst[0::2].tolist(), dst[1::2].tolist())))
    start = int(src[0])
    cycle, prev, cur = [start], start, nb[start][0]
    while cur != start:
        cycle.append(cur)
        x, y = nb[cur]
        prev, cur = cur, (y if x == prev else x)
    assert len(cycle) == len(nb), 'the curve is not one cycle'
    return np.array(cycle)
