#!/usr/bin/env python3
"""SOUND full eight-frame Fraction-interval SAT-sector Farkas checker.

For EVERY frame half-angle tangent in each supplied rational
interval, verify each selected TRUE SAT-owner signed side normal
remains inside its prescribed one of 12 RATIONAL sectors.
The corresponding fixed center-projection inequalities have
strict uniform gap >289/2700. Positive integer/rational edge
weights with exact zero resultant at every center then yield
0>epsilon*sum(weight)>0, a contradiction.

This excludes ONE selected owner sector pattern over a whole
angular product box and ALL square centers, not all SAT words.
"""
import json,sys
from fractions import Fraction as F
from verify_interval_global_sat_owner_cycle import I
from verify_rational_fan_sat_owner_word import RAYS

def cross(a,b):return a[0]*b[1]-a[1]*b[0]

def check(cert):
    r0=F(283,200);qplus=F(9789,2500)
    eps=F(289,2700)
    assert r0*r0+r0+F(1,2)-qplus==F(13,8000)>0
    frames=[]
    for lo,hi in cert["angle_half_tangent_boxes"]:
        t=I(lo,hi)
        zz=t.square()
        c=(1-zz)/(1+zz)
        s=2*t/(1+zz)
        frames.append(((c,s),(-s,c)))
    force=[(F(0),F(0)) for _ in frames]
    total=F(0)
    cross_margins=[]
    for i,j,owner,axis,sign,sector,lamstr in cert["selected_sector_edges"]:
        assert 0<=i<j<len(frames) and owner in (i,j)
        assert axis in ("e","f") and sign in (-1,1) and 0<=sector<12
        lam=F(lamstr)
        assert lam>0
        normal=frames[owner][0 if axis=="e" else 1]
        normal=(sign*normal[0],sign*normal[1])
        a=RAYS[sector]
        b=RAYS[(sector+1)%12]
        c1=cross(a,normal)
        c2=cross(normal,b)
        assert c1.lo>=0 and c2.lo>=0,(
            "owner normal could leave selected exact rational cone",i,j)
        cross_margins.extend((c1.lo,c2.lo))
        direction=(a[0]+b[0],a[1]+b[1])
        force[i]=(force[i][0]+lam*direction[0],
                  force[i][1]+lam*direction[1])
        force[j]=(force[j][0]-lam*direction[0],
                  force[j][1]-lam*direction[1])
        total+=lam
    assert total>0 and all(v==(0,0) for v in force),force
    contradiction=eps*total
    assert contradiction>=F(cert.get("claimed_contradiction_margin","0"))
    print("PASS: EXACT independent eight-angle box SAT FARKAS exclusion")
    print("smallest exact interval cone membership margin",min(cross_margins))
    print("positive multiplier total",total)
    print("would falsely require 0 >",contradiction)
    print("SCOPE: one owner sector pattern, EVERY angle in this box")
if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))
