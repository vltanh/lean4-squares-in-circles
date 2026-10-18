#!/usr/bin/env python3
"""Exact-fraction audit for HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md.

Does NOT enumerate square configurations; checks rational strict margins.
The written concavity and center-angle arguments are the actual proof.
"""
from fractions import Fraction as F

r0=F(283,200)
assert r0*r0+r0+F(1,2)-F(9789,2500)==F(65,40000)>0
x=F(12,25)
assert 1-x*x/2+x**4/24-x**6/720>F(177,200)
def corners(rmin,cos_lower):
    return [r*r+s*s-2*cos_lower*r*s
            for r in [rmin,F(1)] for s in [F(1),r0]]
assert corners(F(1,2),F(177,200))==[
 F(73,200),F(19999,20000),F(23,100),F(19907,40000)]
assert max(corners(F(1,2),F(177,200)))<1
x=F(33,50)
assert 1-x*x/2+x**4/24-x**6/720>F(789,1000)
assert corners(F(5,8),F(789,1000))==[
 F(647,1600),F(159569,160000),F(211,500),F(153871,200000)]
assert max(corners(F(5,8),F(789,1000)))<1
x=F(13,20)
assert 1-x*x/2+x**4/24<F(4,5)
assert F(157,900)+F(239,500)-F(13,20)==F(11,4500)>0
assert F(13,36)*F(22,7)-F(119,250)==F(5189,7875)
assert F(33,50)-F(5189,7875)==F(17,15750)>0
assert F(239,250)-F(11,21)==F(2269,5250)
assert F(2269,5250)-F(43,100)==F(23,10500)>0
assert F(31,50)**2 > 1-F(79,100)**2
assert F(47,50)**2 > 1-F(9,25)**2
assert F(11,18)<F(31,50)
for z,cmin,smin in [
 (F(43,100),F(907,1000),F(416,1000)),
 (F(31,50),F(807,1000),F(58,100))]:
    assert 1-z*z/2>cmin
    assert z-z**3/6>smin
mx=F(0)
for y,expected in [
 (F(79,100),[F(22169,50000),F(4509111,5000000)]),
 (F(47,50),[F(3613,6250),F(4923651,5000000)])]:
    fy=F(9,25)*F(907,1000)+y*F(416,1000)
    assert F(9,25)*F(807,1000)+y*F(58,100)>fy
    vals=[s*s+F(9,25)**2+y*y-2*s*fy for s in [F(1),r0]]
    assert vals==expected,(y,vals,expected)
    mx=max(mx,*vals)
assert mx==F(4923651,5000000)
assert 1-mx==F(76349,5000000)>0
print("PASS: full S2 nearer-inner exclusion strict rational margins")
