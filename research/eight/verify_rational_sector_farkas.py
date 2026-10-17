#!/usr/bin/env python3
"""EXACT rational Farkas contradiction for TRUE SAT-owner sector patterns.

Every actual SAT owner normal n in one of twelve rational sectors
forces (r_k+r_{k+1})·(p_j-p_i) > 289/2700
for any q<=9789/2500 genuine unit-square packing.

A strictly positive rational weighted subset of such inequalities
with exactly zero center-coordinate coefficient proves that an
entire signed SAT-owner word is IMPOSSIBLE.

This verifies also that the supplied full rational 28-edge word
PASSES the earlier 60-degree-triangle and 12-cone DAG screens:
the new Farkas test is genuinely stronger.

A PASS does NOT imply exhaustive owner-word coverage or global R8
optimality.
"""
import json,sys
from fractions import Fraction as F
from verify_rational_fan_sat_owner_word import (
    frames,RAYS,cross,neg,check as old_cycle_check
)

def check(cert):
    r0=F(283,200)
    qplus=F(9789,2500)
    eps=F(289,2700)
    assert r0*r0+r0+F(1,2)-qplus==F(13,8000)>0
    assert r0*F(2,3)==F(283,300)<1
    assert F(62,81)-F(3,4)==F(5,324)>0

    # Each rational sector's tangent angular width is <=3/4.
    for j in range(12):
        a,b=RAYS[j],RAYS[(j+1)%12]
        cr=cross(a,b)
        dp=a[0]*b[0]+a[1]*b[1]
        assert cr>0 and dp>0 and 4*cr<=3*dp

    ef=frames(cert["frame_half_tangents"])
    n=len(ef)
    word={(i,j):(owner,axis,sgn)
          for i,j,owner,axis,sgn in cert["owner_word"]}
    assert len(word)==len(cert["owner_word"])
    assert len(word)==n*(n-1)//2

    if cert.get("expect_old_filters_to_pass",False):
        previous={
            "frame_half_tangents":cert["frame_half_tangents"],
            "owner_word":cert["owner_word"],
            "expect_impossible":False,
        }
        assert not old_cycle_check(previous)

    forces=[(F(0),F(0)) for _ in range(n)]
    total=F(0)
    for i,j,owner,axis,sgn,sector,weight in cert["selected_sector_edges"]:
        assert 0<=i<j<n and word[(i,j)]==(owner,axis,sgn)
        assert 0<=sector<12
        lam=F(weight)
        assert lam>0
        normal=ef[owner][0 if axis=="e" else 1]
        if sgn<0:normal=neg(normal)
        left=RAYS[sector]
        right=RAYS[(sector+1)%12]
        assert cross(left,normal)>=0
        assert cross(normal,right)>=0
        bis=(left[0]+right[0],left[1]+right[1])
        forces[i]=(forces[i][0]+lam*bis[0],forces[i][1]+lam*bis[1])
        forces[j]=(forces[j][0]-lam*bis[0],forces[j][1]-lam*bis[1])
        total+=lam
    assert total>0
    assert all(v==(0,0) for v in forces),(
        "nonzero center-force residual",forces
    )
    lower=eps*total
    assert lower>0
    print("PASS: EXACT rational cross-sector SAT-owner Farkas contradiction")
    print("positive selected edges",len(cert["selected_sector_edges"]))
    print("sum of rational multipliers",total)
    print("all",2*n,"center coefficient coordinates cancel EXACTLY")
    print("selected owners would falsely require 0 >",lower)
    print("FULL OWNER WORD IS IMPOSSIBLE at q<=9789/2500")
if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))
