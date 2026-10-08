"""Geometry shared by crossings.py (the exact crossings behind venn.py's smoothing check and quals.py's drawing check)
and quals.py."""
import math
import re

import numpy as np


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
