#!/usr/bin/env python3
"""Independent exact review of the low-root lower-return height theorem.

No author or other review code is imported. This implementation uses
an immutable interval class, 128-bit outward radicals, monotone normal
component enclosures, and a separately checked binary coverage trie.
The full enlarged domain is the one stated in 93bb8e2d.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import hashlib
import json

BITS = 128
SCALE = 1 << BITS

@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self):
        assert self.lo <= self.hi
    def __add__(self, other):
        other = iv(other)
        return I(self.lo + other.lo, self.hi + other.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + -iv(other)
    def __rsub__(self, other):
        return iv(other) + -self
    def __mul__(self, other):
        other = iv(other)
        terms = (self.lo * other.lo, self.lo * other.hi,
                 self.hi * other.lo, self.hi * other.hi)
        return I(min(terms), max(terms))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = iv(other)
        assert other.lo > 0
        return self * I(1 / other.hi, 1 / other.lo)
    def square(self):
        lower = F(0) if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return I(lower, max(self.lo**2, self.hi**2))
    def cut(self, lower, upper):
        lower, upper = max(self.lo, lower), min(self.hi, upper)
        return None if lower > upper else I(lower, upper)
    def sqrt(self):
        assert self.hi >= 0
        low = max(self.lo, F(0))
        p = isqrt((low.numerator << (2 * BITS)) // low.denominator)
        q = isqrt((self.hi.numerator << (2 * BITS)) // self.hi.denominator)
        if F(q*q, SCALE*SCALE) < self.hi:
            q += 1
        out = I(F(p, SCALE), F(q, SCALE))
        assert out.lo**2 <= low and out.hi**2 >= self.hi
        return out

def iv(x):
    return x if isinstance(x, I) else I(F(x), F(x))

def normalized(first, second):
    """first / sqrt(first^2+second^2), for two positive intervals.

    The component increases with first and decreases with second;
    each endpoint therefore uses an actual corner of their rectangle.
    This is independently tighter than a common interval denominator.
    """
    assert first.lo > 0 and second.lo > 0
    lower_den = iv(first.lo**2 + second.hi**2).sqrt()
    upper_den = iv(first.hi**2 + second.lo**2).sqrt()
    return I(first.lo / lower_den.hi, first.hi / upper_den.lo)

ROOT = (I(F(14,15), F(1)), I(F(29,50), F(2,3)), I(F(2,25), F(5,7)))
WIDTH = tuple(x.hi-x.lo for x in ROOT)
FLOOR = F(1,25000)

def decision(box):
    d, h, t = box
    a, g = 1-d, 1-h
    b = (1-t.square()).sqrt().cut(t.lo, F(1))
    if b is None:
        return 'tilt', None
    radius2 = (d+1).square() + F(1,4)
    Y = g+b+t
    radicand = radius2-Y.square()
    if radicand.hi <= 0:
        return 'positive_x_far', None
    X = radicand.sqrt()
    x = (X-b+t).cut(max(F(3,10), t.lo), d.hi)
    if x is None:
        return 'physical_x', None
    X = X.cut((x+b-t).lo, (x+b-t).hi)
    if X is None:
        return 'far_corner_identity', None
    screen = (d-x)*t-(h-F(1,2))*b
    if screen.hi < 0:
        return 'real_leaf_screen', None
    if X.lo <= 0:
        return None, None
    w = x+a
    assert w.lo > 0 and h.lo > 0
    c, s = normalized(w,h), normalized(h,w)
    N, K = a*c+h*s, x*s
    upper_radicand = radius2-(N+1).square()
    if upper_radicand.hi < 0:
        return 'upper_circle', None
    W = upper_radicand.sqrt()
    rho = (W-K).cut(F(7,8),F(1))
    if rho is None:
        return 'upper_mean', None
    delta = 1-rho
    tau = (b*(x*Y/X-g)).cut(F(0),F(1))
    if tau is None:
        return 'lower_mean', None
    target = tau*b-delta*c
    if target.lo > FLOOR:
        return 'height', target.lo
    return None, None

def coverage(paths):
    trie = {}
    for path in paths:
        node = trie
        for char in path:
            assert '#' not in node
            node = node.setdefault(char,{})
        assert not node
        node['#'] = True
    def check(node):
        if '#' in node:
            assert set(node)=={'#'}
            return 1
        assert set(node)=={'0','1'}
        return check(node['0'])+check(node['1'])
    assert check(trie)==len(paths)

pending = [('', ROOT)]
leaves = []
nodes = 0
while pending:
    path, box = pending.pop()
    nodes += 1
    reason, margin = decision(box)
    if reason:
        leaves.append({'path':path, 'reason':reason,
                       'margin':None if margin is None else str(margin)})
        continue
    assert len(path) < 45 and nodes < 250000
    ratios = tuple((x.hi-x.lo)/w for x,w in zip(box,WIDTH))
    axis = max(range(3),key=lambda j:ratios[j])
    midpoint = (box[axis].lo+box[axis].hi)/2
    left, right = list(box), list(box)
    left[axis] = I(box[axis].lo,midpoint)
    right[axis] = I(midpoint,box[axis].hi)
    pending.append((path+'1',tuple(right)))
    pending.append((path+'0',tuple(left)))

coverage([x['path'] for x in leaves])
assert nodes==2*len(leaves)-1
assert sum((F(1,2)**len(x['path']) for x in leaves),F(0))==1
positive = [F(x['margin']) for x in leaves if x['margin'] is not None]
assert min(positive) > FLOOR
base = Path(__file__).resolve().parent.parent
pins = {
    'HOUSE_LOWER_TAC_S_ALIGNED_UPPER_A_EXCLUSION.md':'975b2ab626aa30b06decdf068fd0667c7badee83e6711ec489de0daab673c773',
    'ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md':'93bb8e2d6dc3f2965c1a1868ba4a7552f63c5326cbe05cab5381950f4db765be',
    'certificates/aligned_low_s_lower_return_height_separation.py':'bd92d1895f240805a78ea5160b0b7ed56f6948a4ec6ce88ff870bb55a6472f15',
}
for name, pin in pins.items():
    assert hashlib.sha256((base/name).read_bytes()).hexdigest()==pin,name
record = {
    'reviewer':'triangle_bridges', 'bits':BITS,
    'normal_enclosure':'independent monotone component endpoints',
    'source_pins':pins, 'uniform_strict_floor':str(FLOOR),
    'initial':[[str(x.lo),str(x.hi)] for x in ROOT],
    'nodes':nodes,'terminal_boxes':len(leaves),
    'maximum_depth':max(len(x['path']) for x in leaves),
    'terminal_reasons':dict(Counter(x['reason'] for x in leaves)),
    'minimum_lower_bound':str(min(positive)),
    'complete_binary_trie':True,'exact_kraft_sum':'1',
    'leaves':leaves,
}
output = base/'checkpoints/triangle_bridges_lower_tac_upper_a_independent_scalar_2026_10_28.json'
output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='leaves'},indent=2))
print('record_sha256',hashlib.sha256(output.read_bytes()).hexdigest())
