#!/usr/bin/env python3
"""EXACT rational directed SAT owner cycle rejection in the n8 disk search.

A certificate lists TRUE unit-square frames as exact rational
half-angle tangents z=tan(theta/2), a directed simple cycle of
genuine pair SAT-owner axes, and conservative rational upper
bounds for the cycle's center-coefficient Euclidean norms.

PASS certifies that NO square center placement in squared disk
radius <= 9789/2500 can realize all those directed actual
separators simultaneously. It proves nothing for other owner
choices, angular boxes, or the unrestricted global optimum.

Usage:
  python verify_global_sat_owner_cycle.py \
       global_sat_triangle_cycle_example.json
"""
import json,sys
from fractions import Fraction as F

qplus=F(9789,2500)
r0=F(283,200)
assert r0*r0+r0+F(1,2)-qplus==F(13,8000)>0

def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(k,a):return (k*a[0],k*a[1])

def check(cert):
    ef=[]
    for z in cert["frame_half_tangents"]:
        t=F(z)
        c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
        e=(c,s);f=(-s,c)
        assert dot(e,e)==dot(f,f)==1 and dot(e,f)==0
        ef.append((e,f))
    n=len(ef)
    cyc=cert["cycle"];k=len(cyc)
    assert k>=3
    assert len(set(entry[0] for entry in cyc))==k
    assert all(cyc[i][1]==cyc[(i+1)%k][0] for i in range(k))
    normals=[];supports=[]
    for a,b,owner,axis,sgn in cyc:
        assert a!=b and 0<=a<n and 0<=b<n
        assert owner in (a,b) and axis in ("e","f") and sgn in (-1,1)
        normal=mul(sgn,ef[owner][0 if axis=="e" else 1])
        assert dot(normal,normal)==1
        H=lambda i:(abs(dot(normal,ef[i][0]))+
                    abs(dot(normal,ef[i][1])))/2
        normals.append(normal)
        supports.append(H(a)+H(b))
    assert all(w>=1 for w in supports)
    upper=[F(x) for x in cert["coefficient_norm_upper_bounds"]]
    assert len(upper)==k and all(x>=0 for x in upper)
    for i in range(k):
        v=sub(normals[(i-1)%k],normals[i])
        assert upper[i]**2>=dot(v,v),(
            "invalid Euclidean coefficient bound",i,v,upper[i])
    W=sum(supports)
    RHS=r0*sum(upper)
    assert W>RHS,("NO CONTRADICTION CERTIFIED",W,RHS)
    print("PASS exact TRUE SAT owner directed-cycle obstruction")
    print("cycle length",k,"directed support sum",W,
          "center bound",RHS)
    print("strict rational contradiction margin",W-RHS)
    print("SCOPE: THIS rational frame and signed owner cycle ONLY")

if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))
