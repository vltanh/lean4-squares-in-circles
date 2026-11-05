"""Exact all-original square-area inertia rows.

For k physical disjoint unit squares and any rational2x2 matrix B,
  sum_{i<j} ||B(c_j-c_i)||² >= 7*k³*abs(detB)/44 - k²*||B||_F²/12.
This follows from area rearrangement, unit-square inertia=(1/12)I,
the centroid pair identity, and pi<22/7. All original orientations and
weak physical contacts are retained. The bound needs no disk containment.
"""
from fractions import Fraction as F
from itertools import combinations

IDENTITY=((F(1),F(0)),(F(0),F(1)))

def lower_bound(k,B=IDENTITY):
    a,b=B[0];c,d=B[1]
    return F(7*k**3,44)*abs(a*d-b*c)-F(k*k,12)*(a*a+b*b+c*c+d*d)

def name(S,B,prefix):
    return prefix+'_'+'-'.join(map(str,S))+'_'+'_'.join(str(v)for row in B for v in row)

def linear_row(S,diffs,B=IDENTITY):
    co={};rhs=-lower_bound(len(S),B)
    for i,j in combinations(S,2):
        for p,q in B:
            lo=sum(min(v*l,v*u)for v,(l,u)in zip((p,q),diffs[i,j]))
            hi=sum(max(v*l,v*u)for v,(l,u)in zip((p,q),diffs[i,j]))
            for ax,v in enumerate((p,q)):
                a=(lo+hi)*v
                co[2*i+ax]=co.get(2*i+ax,F(0))+a
                co[2*j+ax]=co.get(2*j+ax,F(0))-a
            rhs-=lo*hi
    return tuple((k,v)for k,v in sorted(co.items())if v),rhs,name(S,B,'square_area_moment_secant')

def quadratic_row(S,L,B=IDENTITY):
    co={}
    for i,j in combinations(S,2):
        for p,q in B:
            z={2*j:p,2*i:-p,2*j+1:q,2*i+1:-q}
            L.multiply(co,z,z,-1)
    return L.clean(co,-lower_bound(len(S),B),name(S,B,'square_area_moment_quadratic'))

def axes_matrices():
    return tuple(((F(a),F(0)),(F(0),F(b)))for a,b in [(1,1),(1,2),(2,1),(2,3),(3,2),(1,3),(3,1)])

def generate_linear(diffs,counts=(5,6,7,8,9),matrices=None):
    out=[]
    for k in counts:
        for B in (axes_matrices()if matrices is None else matrices):
            if lower_bound(k,B)<=0:continue
            for S in combinations(range(9),k):out.append(linear_row(S,diffs,B))
    return out

def generate_quadratic(L,counts=(5,6,7,8,9),matrices=None):
    out=[]
    for k in counts:
        for B in (axes_matrices()if matrices is None else matrices):
            if lower_bound(k,B)<=0:continue
            for S in combinations(range(9),k):out.append(quadratic_row(S,L,B))
    return out
