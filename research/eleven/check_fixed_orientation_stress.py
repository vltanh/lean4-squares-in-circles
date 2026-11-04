#!/usr/bin/env python3
"""Exact positive stress for the fixed orientations of the contact family.

The claimed conditional global bound is proved in FIXED_ORIENTATION_STRESS.md.
All numerical verification uses rational interval arithmetic.
"""
from fractions import Fraction as F
from contact_family import family
from isolate_contact_root import I, certificate

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')

class R:
    """Outward intervals rounded to a fixed rational grid after every operation."""
    scale = 10**30
    def __init__(self, lo, hi=None):
        if isinstance(lo, (I,R)):
            lo,hi=lo.lo,lo.hi
        lo,hi=F(lo),F(lo if hi is None else hi)
        self.lo=F((lo*self.scale).__floor__(), self.scale)
        self.hi=F((hi*self.scale).__ceil__(), self.scale)
        assert self.lo<=self.hi
    def __add__(self, other):
        other=R(other);return R(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return R(-self.hi,-self.lo)
    def __sub__(self, other):return self+-R(other)
    def __rsub__(self, other):return R(other)+-self
    def __mul__(self,other):
        other=R(other);p=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return R(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,other):
        other=R(other);assert other.lo*other.hi>0
        return self*R(1/other.hi,1/other.lo)
    def abs_lower(self):
        return min(abs(self.lo),abs(self.hi)) if self.lo*self.hi>0 else F(0)


def solve_intervals(matrix, rhs):
    """Gaussian elimination enclosing the solution of every matrix in the box."""
    n=len(rhs)
    matrix=[[R(x) for x in row] for row in matrix]
    rhs=[R(x) for x in rhs]
    for k in range(n):
        pivot=max(range(k,n),key=lambda i:matrix[i][k].abs_lower())
        matrix[k],matrix[pivot]=matrix[pivot],matrix[k]
        rhs[k],rhs[pivot]=rhs[pivot],rhs[k]
        divisor=matrix[k][k]
        assert divisor.abs_lower()>0, ('zero pivot',k)
        for j in range(k+1,n):matrix[k][j]=matrix[k][j]/divisor
        rhs[k]=rhs[k]/divisor
        matrix[k][k]=R(1)
        for i in range(k+1,n):
            multiplier=matrix[i][k]
            for j in range(k+1,n):matrix[i][j]=matrix[i][j]-multiplier*matrix[k][j]
            rhs[i]=rhs[i]-multiplier*rhs[k]
            matrix[i][k]=R(0)
    answer=[R(0)]*n
    for i in reversed(range(n)):
        answer[i]=rhs[i]-sum(matrix[i][j]*answer[j] for j in range(i+1,n))
    return answer


def stress_certificate():
    box=certificate()
    _,points,angles,_=family(box[0],box[1],lambda x:x.sqrt())
    (ca,sa),(cb,sb)=angles
    ta,tb=box[1],sb/(1+cb)
    dca=-4*ta/(1+ta*ta)**2;dsa=2*(1-ta*ta)/(1+ta*ta)**2
    dcb=-4*tb/(1+tb*tb)**2;dsb=2*(1-tb*tb)/(1+tb*tb)**2
    ua,va=(ca,sa),(-sa,ca);ub,vb=(cb,sb),(-sb,cb)
    dua,dva=(dca,dsa),(-dsa,dca);dub,dvb=(dcb,dsb),(-dsb,dcb)
    zero=(I(0),I(0));ex,ey=(I(1),I(0)),(I(0),I(1))
    frames=[(ex,ey)]*7+[(ua,va)]*2+[(ub,vb)]*2
    derivatives=[(zero,zero)]*7+[(dua,dva)]*2+[(dub,dvb)]*2
    coordinate_slots=[(i,k) for i in range(11) for k in range(2) if (i,k)!=(1,0)]
    slot={key:index for index,key in enumerate(coordinate_slots)}
    def dot(x,y):return sum(a*b for a,b in zip(x,y))
    rows=[];labels=[]
    disks=[(0,1,1),(2,1,1),(3,1,-1),(5,1,-1),(6,-1,-1),(7,-1,-1),(7,-1,1),(9,-1,1),(10,-1,1),(10,1,1)]
    for i,eps,eta in disks:
        u,v=frames[i];du,dv=derivatives[i]
        vertex=tuple(points[i][k]+(eps*u[k]+eta*v[k])/2 for k in range(2))
        row=[I(0) for _ in range(24)]
        for k in range(2):row[slot[i,k]]=-2*vertex[k]
        if i>=7:
            change=tuple((eps*du[k]+eta*dv[k])/2 for k in range(2))
            row[21 if i<9 else 22]=-2*dot(vertex,change)
        row[23]=I(1)
        rows.append(row);labels.append(f'disk {i} {eps:+d} {eta:+d}')
    dk_a=(dca+dsa)/2;dk_b=(dcb+dsb)/2
    dk_d_a=(dca*cb+dsa*sb+dca*sb-dsa*cb)/2
    dk_d_b=(ca*dcb+sa*dsb+ca*dsb-sa*dcb)/2
    def neg(v):return tuple(-z for z in v)
    # i,j,normal,dnormal/dta,dnormal/dtb,dwidth/dta,dwidth/dtb
    edges=[(0,1,neg(ey),zero,zero,0,0),(0,2,ex,zero,zero,0,0),
           (0,10,neg(ex),zero,zero,0,dk_b),(1,4,neg(ey),zero,zero,0,0),
           (2,3,neg(ey),zero,zero,0,0),(3,4,neg(ex),zero,zero,0,0),
           (4,5,neg(ey),zero,zero,0,0),(4,8,neg(ex),zero,zero,dk_a,0),
           (5,6,neg(ex),zero,zero,0,0),(6,7,va,dva,zero,dk_a,0),
           (7,8,ua,dua,zero,0,0),(7,9,va,dva,zero,dk_d_a,dk_d_b),
           (8,9,vb,zero,dvb,dk_d_a,dk_d_b),(9,10,ub,zero,dub,0,0)]
    for i,j,n,dna,dnb,dwa,dwb in edges:
        row=[I(0) for _ in range(24)]
        delta=tuple(points[j][k]-points[i][k] for k in range(2))
        for k in range(2):
            if (i,k) in slot:row[slot[i,k]]=-n[k]
            if (j,k) in slot:row[slot[j,k]]=n[k]
        row[21]=dot(dna,delta)-dwa;row[22]=dot(dnb,delta)-dwb
        rows.append(row);labels.append(f'pair {i} {j}')
    matrix=[[rows[col][row] for col in range(24)] for row in range(24)]
    weights=solve_intervals(matrix,[0]*23+[1])
    for label,weight in zip(labels,weights):
        assert weight.lo>F(1,100), (label,str(weight.lo),str(weight.hi))
    assert len(weights)==24
    # Equality reconstruction leaves only square 1's horizontal coordinate.
    # Disk containment gives |h| < 7/4; pair (1,2) then forces h <= a.
    a,b=points[0]; _,d=points[2]
    assert box[0].hi < F(81,16) and a.lo > 0
    assert (d-(b-1)).abs_upper() < 1
    h=I(F(-7,4),a.hi)
    displacement=(h-points[8][0], b-1-points[8][1])
    k=(1+ca+sa)/2
    U=dot(ua,displacement);V=dot(va,displacement)
    assert displacement[0].abs_upper() < k.lo
    assert displacement[1].abs_upper() < k.lo
    assert V.abs_upper() < k.lo and U.lo > -k.lo
    # Among all four physical axes only positive u can separate pair (8,1).
    print('PASS: full physical separation of the remaining slider forces H <= h <= a.')
    print('PASS: the 24 by 24 active-gradient matrix is invertible throughout the root box.')
    print('PASS: every disk and separator stress weight is > 1/100.')
    print('All following endpoints are rational outward bounds with denominator 1000000:')
    for label,weight in zip(labels,weights):
        lo=F((weight.lo*10**6).__floor__(),10**6)
        hi=F((weight.hi*10**6).__ceil__(),10**6)
        print(label,str(lo),str(hi))
    return weights

if __name__=='__main__':stress_certificate()
