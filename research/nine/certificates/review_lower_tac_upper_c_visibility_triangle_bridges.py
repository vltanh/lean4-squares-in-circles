#!/usr/bin/env python3
"""Independent 128-bit exact verification of the upper-C visibility cover.

The author proof data supply only terminal paths and claimed margins.
No author arithmetic, source module or peer review implementation is imported.
The original initial box, both actual return targets, every guard, and
all normalized midpoint splits are reconstructed below.
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
        return I(self.lo+other.lo,self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi,-self.lo)
    def __sub__(self,other):
        return self+-iv(other)
    def __rsub__(self,other):
        return iv(other)+-self
    def __mul__(self,other):
        other = iv(other)
        values = (self.lo*other.lo,self.lo*other.hi,
                  self.hi*other.lo,self.hi*other.hi)
        return I(min(values),max(values))
    __rmul__ = __mul__
    def __truediv__(self,other):
        other = iv(other)
        assert other.lo > 0
        return self*I(1/other.hi,1/other.lo)
    def square(self):
        low = F(0) if self.lo <= 0 <= self.hi else min(self.lo**2,self.hi**2)
        return I(low,max(self.lo**2,self.hi**2))
    def cut(self,lower,upper):
        low,high=max(self.lo,lower),min(self.hi,upper)
        return None if low>high else I(low,high)
    def sqrt(self):
        assert self.hi >= 0
        lo=max(self.lo,F(0))
        low=isqrt((lo.numerator << (2*BITS))//lo.denominator)
        high=isqrt((self.hi.numerator << (2*BITS))//self.hi.denominator)
        if F(high*high,SCALE*SCALE)<self.hi:
            high+=1
        value=I(F(low,SCALE),F(high,SCALE))
        assert value.lo**2<=lo and value.hi**2>=self.hi
        return value

def iv(x):
    return x if isinstance(x,I) else I(F(x),F(x))

def component(first,second):
    assert first.lo>0 and second.lo>0
    lower_norm=iv(first.lo**2+second.hi**2).sqrt()
    upper_norm=iv(first.hi**2+second.lo**2).sqrt()
    return I(first.lo/lower_norm.hi,first.hi/upper_norm.lo)

INITIAL=(I(F(14,15),F(1)),I(F(29,50),F(2,3)),I(F(2,25),F(1)))
WIDTH=tuple(x.hi-x.lo for x in INITIAL)
FLOOR=F(1,1000000)
LAM_MAX=F(197,925)
ROOT2_UPPER=F(99,70)

def certify(box):
    d,h,t=box
    a,g=1-d,1-h
    b=(1-t.square()).sqrt()
    R2=(d+1).square()+F(1,4)
    if R2.hi<=4:
        return 'radius',None
    Y=g+b+t
    X2=R2-Y.square()
    if X2.hi<=0:
        return 'positive_X',None
    X=X2.sqrt()
    x=(X-b+t).cut(F(3,10),d.hi)
    if x is None:
        return 'x_interval',None
    x=x.cut(t.lo,x.hi)
    if x is None:
        return 'x_above_t',None
    original_X=x+b-t
    X=X.cut(original_X.lo,original_X.hi)
    if X is None:
        return 'X_identity',None
    if ((d-x)*t-(h-F(1,2))*b).hi<0:
        return 'leaf_screen',None
    w=x+a
    if w.lo<=0 or X.lo<=0:
        return None,None
    c,s=component(w,h),component(h,w)
    N,K=a*c+h*s,x*s
    W2=R2-(N+1).square()
    if W2.hi<0:
        return 'upper_circle',None
    W=W2.sqrt()
    rho=(W-K).cut(F(7,8),F(1))
    if rho is None:
        return 'upper_mean',None
    if W.lo<=0:
        return None,None
    delta=1-rho
    lam=((K-N*rho)/W).cut(F(0),LAM_MAX)
    if lam is None:
        return 'proper_concurrence',None
    A0=a+x-t
    L0,H0=delta*s,1-delta*c
    L1,H1=lam*c+delta*s,1+lam*s-delta*c
    direct0=(A0+L0)*H0-ROOT2_UPPER*L0
    direct1=(A0+L1)*H1-ROOT2_UPPER*L1
    factor0=A0*H0+L0*(H0-ROOT2_UPPER)
    factor1=A0*H1+L1*(H1-ROOT2_UPPER)
    const=max(direct0.lo,factor0.lo)
    linear=s*A0+(1-ROOT2_UPPER)*c+delta*(s.square()-c.square())
    quadratic=(c*s).lo
    assert quadratic>0 and lam.lo>=0
    # This minimizes a lower quadratic for every actual u in [lam.lo,lam.hi].
    vertex=-linear.lo/(2*quadratic)
    arg=min(lam.hi,max(lam.lo,vertex))
    parabola=const+linear.lo*arg+quadratic*arg*arg
    second=max(direct1.lo,factor1.lo,parabola)
    lower=min(const,second)
    return ('targets',lower) if lower>FLOOR else (None,lower)

author_path=Path('/tmp/aligned_low_s_upper_c_visibility_certificate.json')
author=json.loads(author_path.read_text())
author_leaves=author['leaves']
canonical=json.dumps(author_leaves,sort_keys=True,separators=(',',':')).encode()
assert hashlib.sha256(canonical).hexdigest()=='c8abdb83f97e69fd9445b3733df9fd2fcd77eaf357a69eea23fe63d3800397ad'
assert len(author_leaves)==19351
tree={}
for row in author_leaves:
    node=tree
    for bit in row['path']:
        assert '#' not in node
        node=node.setdefault(bit,{})
    assert not node
    node['#']=row

pending=[('',INITIAL,tree)]
leaves=[]
nodes=0
while pending:
    path,box,node=pending.pop()
    nodes+=1
    if '#' in node:
        assert set(node)=={'#'} and node['#']['path']==path
        reason,margin=certify(box)
        assert reason is not None,(path,margin)
        old=node['#']
        if old['reserve'] is not None:
            assert reason=='targets' and margin>=F(old['reserve'])
        leaves.append({'path':path,'reason':reason,
                       'margin':None if margin is None else str(margin)})
        continue
    assert set(node)=={'0','1'}
    normalized=tuple((v.hi-v.lo)/w for v,w in zip(box,WIDTH))
    axis=max(range(3),key=lambda j:normalized[j])
    midpoint=(box[axis].lo+box[axis].hi)/2
    left,right=list(box),list(box)
    left[axis]=I(box[axis].lo,midpoint)
    right[axis]=I(midpoint,box[axis].hi)
    assert left[axis].lo==box[axis].lo and right[axis].hi==box[axis].hi
    assert left[axis].hi==right[axis].lo
    pending.append((path+'1',tuple(right),node['1']))
    pending.append((path+'0',tuple(left),node['0']))

assert nodes==38701==2*len(leaves)-1
assert sum((F(1,2)**len(x['path']) for x in leaves),F(0))==1
margins=[F(x['margin']) for x in leaves if x['margin'] is not None]
assert min(margins)>FLOOR
base=Path(__file__).resolve().parent.parent
pins={
 'HOUSE_LOWER_TAC_S_ALIGNED_UPPER_C_EXCLUSION.md':'b773da381ac721c0f3c06083c9da6258ea1142353fd4a6e000edaff1d8398125',
 'certificates/aligned_low_s_upper_c_visibility_separation.py':'d57e7506d4f6e1dd92c991c8579fcfcd03377703863b0d42d50f417267fe2c4c',
}
for name,pin in pins.items():
    assert hashlib.sha256((base/name).read_bytes()).hexdigest()==pin,name
record={
 'reviewer':'triangle_bridges','bits':BITS,'source_pins':pins,
 'independent_normal_enclosure':'monotone component endpoints',
 'author_leaf_digest':hashlib.sha256(canonical).hexdigest(),
 'nodes':nodes,'terminal_boxes':len(leaves),
 'maximum_depth':max(len(x['path']) for x in leaves),
 'reason_counts':dict(Counter(x['reason'] for x in leaves)),
 'full_binary_trie':True,'exact_kraft_sum':'1',
 'all_author_target_margins_weakly_improved':True,
 'minimum_lower_bound':str(min(margins)),
 'uniform_strict_floor':str(FLOOR),'leaves':leaves,
}
output=base/'checkpoints/triangle_bridges_lower_tac_upper_c_independent_scalar_2026_10_28.json'
output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='leaves'},indent=2))
print('record_sha256',hashlib.sha256(output.read_bytes()).hexdigest())
