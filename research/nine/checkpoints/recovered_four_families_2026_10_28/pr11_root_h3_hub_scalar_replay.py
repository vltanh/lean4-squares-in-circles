#!/usr/bin/env python3
"""Root's independent Fraction replay of the complete H3 scalar cover.

No author modules are imported. Leaves are checked independently, and
their bit paths are rebuilt into the entire binary subdivision tree.
Only square roots are rounded, on a separate 2**80 denominator lattice.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json

RADICAL_SCALE = 1 << 80

class BoxValue:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def promote(x):
        return x if isinstance(x, BoxValue) else BoxValue(x)

    def __add__(self, y):
        y = self.promote(y)
        return BoxValue(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__

    def __neg__(self):
        return BoxValue(-self.hi, -self.lo)

    def __sub__(self, y):
        return self + (-self.promote(y))

    def __rsub__(self, y):
        return self.promote(y) + (-self)

    def __mul__(self, y):
        y = self.promote(y)
        products = [a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return BoxValue(min(products),max(products))
    __rmul__ = __mul__

    def __truediv__(self, y):
        y = self.promote(y)
        assert y.lo > 0
        return self * BoxValue(1/y.hi,1/y.lo)

    def squared(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2,self.hi**2)
        return BoxValue(low,max(self.lo**2,self.hi**2))

    def radical(self):
        assert self.lo >= 0
        def floor_root(q):
            result = isqrt((q.numerator*RADICAL_SCALE**2)//q.denominator)
            assert result**2*q.denominator <= q.numerator*RADICAL_SCALE**2
            assert (result+1)**2*q.denominator > q.numerator*RADICAL_SCALE**2
            return result
        low = floor_root(self.lo)
        high = floor_root(self.hi)
        if Q(high,RADICAL_SCALE)**2 < self.hi:
            high += 1
        return BoxValue(Q(low,RADICAL_SCALE),Q(high,RADICAL_SCALE))

    def meet(self, other):
        return BoxValue(max(self.lo,other.lo),min(self.hi,other.hi))


def check_leaf(leaf, scale):
    zl,zh,pl,ph = leaf['box']
    z=BoxValue(Q(zl,scale),Q(zh,scale))
    p=BoxValue(Q(pl,scale),Q(ph,scale))
    z2=z.squared()
    a=(1-z2)/(1+z2)
    b=2*z/(1+z2)
    guards={'a_gt_b':a-b}
    guards['p_gt_p0']=p-(a-b)/(a+b)
    guards['p_lt_b_a']=b/a-p
    H=b+a*p
    t=1-H
    guards['t_positive']=t
    x=1-(b/a)*(1+p)
    guards['x_positive']=x
    den=1-p*H
    guards['denv_positive']=den
    if leaf['kind']=='empty' and leaf['reason'] in guards:
        assert guards[leaf['reason']].hi <= 0,leaf
        return None
    assert den.lo > 0,leaf
    # Restrict only quantities already strictly positive on actual inputs.
    assert t.hi > 0 and x.hi > 0,leaf
    t=BoxValue(max(t.lo,0),t.hi)
    x=BoxValue(max(x.lo,0),x.hi)
    v=t/den
    y=a-t
    E=(1+x.squared()).radical()
    L=(1+v.squared()).radical()
    g=(x+v)/(E*L)
    h=(1-x*v)/(E*L)
    A=(1+b+x*y)/E
    B=(x*(1+b)-y)/E
    k1=1-A+g
    if leaf['kind']=='empty':
        assert leaf['reason']=='k1_positive'
        assert k1.hi <= 0,leaf
        return None
    assert leaf['kind']=='pass' and leaf['reason']=='all'
    f1=g.squared()-g+B*g+h*(A-1)
    f2=(1+b-v*y)/L-h-g+g.squared()
    f3=(1+b-v*y)/L-h-g+1-h.squared()
    F=f1.meet(f2).meet(f3)
    margins=[1-B-h-Q(1,3), Q(1,8)-k1, h-Q(3,5), F]
    assert all(x.lo>0 for x in margins),leaf
    return [x.lo for x in margins]


def verify_tree(leaf_map, root):
    visited=[]
    zw=root[1]-root[0]
    pw=root[3]-root[2]
    def visit(path,box):
        visited.append(path)
        if path in leaf_map:
            assert tuple(leaf_map[path]['box'])==tuple(box)
            return
        assert any(q.startswith(path+'0') for q in leaf_map)
        assert any(q.startswith(path+'1') for q in leaf_map)
        zl,zh,pl,ph=box
        if (zh-zl)*pw >= (ph-pl)*zw:
            mid=(zl+zh)//2
            assert zl<mid<zh
            children=((zl,mid,pl,ph),(mid,zh,pl,ph))
        else:
            mid=(pl+ph)//2
            assert pl<mid<ph
            children=((zl,zh,pl,mid),(zl,zh,mid,ph))
        visit(path+'0',children[0])
        visit(path+'1',children[1])
    visit('',root)
    assert set(leaf_map).issubset(set(visited))
    assert len(visited)==2*len(leaf_map)-1
    return len(visited)


def main():
    source=Path('/tmp/pr11_root_h3_hub_scalar_author_leaves.json')
    record=json.loads(source.read_text())
    cert=record['certificate']
    leaves=record['leaves']
    scale=cert['scale']
    assert scale==1<<48
    root=cert['root']
    assert Q(root[0],scale)<=Q(19,100)<Q(root[1],scale)
    assert Q(root[1],scale)>=Q(5,12)
    assert root[2]==0 and root[3]==scale
    leaf_map={leaf['path']:leaf for leaf in leaves}
    assert len(leaf_map)==len(leaves)==475
    visits=verify_tree(leaf_map,root)
    count=Counter()
    floors=[None]*4
    # A compact rational lower bound is sufficient for the replay record.
    for leaf in leaves:
        margins=check_leaf(leaf,scale)
        count[leaf['kind']+':'+leaf['reason']]+=1
        if margins is not None:
            for i,q in enumerate(margins):
                floor=Q((q*(10**12)).numerator//(q*(10**12)).denominator,10**12)
                floors[i]=floor if floors[i] is None else min(floors[i],floor)
    assert count['pass:all']==219
    assert max(map(len,leaf_map))==20
    assert all(q>0 for q in floors)
    result={'method':'Independent exact Fraction operations; only radicals outward rounded on 2^80 lattice; complete binary prefix-tree replay; no author imports',
            'leaf_sha256':sha256(source.read_bytes()).hexdigest(),
            'root':root,'complete_visits':visits,'terminal_boxes':len(leaves),
            'decisions':dict(count),'max_depth':20,
            'independent_positive_rational_margin_floors':[str(q) for q in floors]}
    out=Path('/tmp/pr11_root_h3_hub_scalar_replay.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
