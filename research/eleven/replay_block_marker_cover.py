"""Independent exact replay; does not import the certificate generator."""
from fractions import Fraction
from pathlib import Path
from collections import Counter
import hashlib
import json

F = Fraction

class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    def __add__(self, other):
        if not isinstance(other, Interval): other = Interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        if not isinstance(other, Interval): other = Interval(other)
        return self + -other

    def __mul__(self, other):
        if not isinstance(other, Interval): other = Interval(other)
        values = (self.lo*other.lo, self.lo*other.hi,
                  self.hi*other.lo, self.hi*other.hi)
        return Interval(min(values), max(values))

    def minimum_abs(self):
        return F(0) if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))


def required(condition, message):
    if not condition:
        raise ValueError(message)


def verify_leaf(box, kind, axis, sign, reason):
    a,b,t = box
    c = Interval((1-t.hi**2)/(1+t.hi**2), (1-t.lo**2)/(1+t.lo**2))
    s = Interval(2*t.lo/(1+t.lo**2), 2*t.hi/(1+t.hi**2))
    if reason == 'frame-chart':
        return t.lo**2+2*t.lo > 1
    if reason == 'corner-radius':
        x,y = a.minimum_abs(), b.minimum_abs()
        return x*x+y*y+x+y+F(1,2) > F(4999,1000)
    if reason == 'block-separator':
        if kind == 'own':
            bound = a-c-s-F(1,2)
        else:
            bound = c*a-s*b-1-(c+s)*F(1,2)
        return bound.hi < 0
    if reason == 'marker-outside':
        displacement = a-c*F(3,2) if axis == 0 else b+s*F(3,2)
        return (displacement*sign).hi < F(1,2)
    raise ValueError('unknown leaf reason')


def verify_branch(branch):
    required(set(branch) == {'kind','axis','sign','stats','tree'}, 'branch keys')
    kind,axis,sign = (branch[k] for k in ('kind','axis','sign'))
    required(kind in ('own','core') and axis in (0,1) and sign in (-1,1), 'branch type')
    stats = {'nodes':0,'leaves':0,'max_depth':0}
    reasons = Counter()
    def recurse(node, box, depth):
        stats['nodes'] += 1
        stats['max_depth'] = max(stats['max_depth'],depth)
        if 'excluded' in node:
            required(set(node) == {'excluded'}, 'leaf keys')
            required(verify_leaf(box,kind,axis,sign,node['excluded']), 'invalid leaf')
            stats['leaves'] += 1
            reasons[node['excluded']] += 1
            return
        required(set(node) == {'split','left','right'}, 'split keys')
        k = node['split']
        required(type(k) is int and 0 <= k < 3, 'split coordinate')
        midpoint = (box[k].lo+box[k].hi)/2
        required(box[k].lo < midpoint < box[k].hi, 'nontrivial split')
        left,right = list(box),list(box)
        left[k],right[k] = Interval(box[k].lo,midpoint),Interval(midpoint,box[k].hi)
        recurse(node['left'],left,depth+1)
        recurse(node['right'],right,depth+1)
    recurse(branch['tree'],[Interval(-F(7,4),F(7,4)),Interval(-F(7,4),F(7,4)),Interval(0,F(5,12))],0)
    required(stats == branch['stats'], 'wrong branch statistics')
    return (kind,axis,sign),stats,reasons


def main():
    path=Path(__file__).with_name('BLOCK_MARKER_COVER.json')
    data=json.loads(path.read_text())
    required(set(data) == {'schema','q','branches'}, 'top-level keys')
    required(data['schema'] == 'centered-block-marker-v1' and data['q'] == '4999/1000', 'schema or radius')
    expected = {(k,a,s) for k in ('own','core') for a in (0,1) for s in (-1,1)}
    seen=set();nodes=leaves=depth=0;reasons=Counter()
    for branch in data['branches']:
        key,stats,counts=verify_branch(branch)
        required(key not in seen, 'duplicate branch')
        seen.add(key);nodes+=stats['nodes'];leaves+=stats['leaves'];depth=max(depth,stats['max_depth']);reasons.update(counts)
        print('PASS',key,stats)
    required(seen == expected, 'incomplete branch cover')
    print('PASS TOTAL',{'nodes':nodes,'leaves':leaves,'max_depth':depth,'reasons':dict(reasons)})
    print('SHA256',hashlib.sha256(path.read_bytes()).hexdigest())


if __name__ == '__main__':main()
