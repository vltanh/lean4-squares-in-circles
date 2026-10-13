#!/usr/bin/env python3
"""Exact arithmetic for the five-square inner/outer angular fan obstruction.

All assertions are rational endpoints of the written hand proof.
This is NOT a continuous classifier, proof oracle, Lean formalization,
or a full eight-square optimality proof.
"""
from fractions import Fraction as Q

r0=Q(283,200)
qplus=Q(9789,2500)
assert r0*r0+r0+Q(1,2)-qplus == Q(65,40000)
assert Q(71,100)**2>Q(1,2)
assert Q(117,283)>Q(2,5)
# cos(2pi/9) > 1-(44/63)^2/2
assert 1-Q(44,63)**2/2==Q(3001,3969)
assert Q(3001,3969)>Q(3,4)
# cos(7pi/36)>1-(11/18)^2/2>13/16
assert 1-Q(11,18)**2/2==Q(527,648)
assert Q(527,648)-Q(13,16)==Q(1,1296)
# cos(3pi/8)<2/5 follows sqrt(2)>34/25
assert 2>Q(34,25)**2
# Universal mixed-center angular gap endpoint audits
def corners(rmin, cos_lower):
    return [r*r+s*s-2*cos_lower*r*s
            for r in (rmin,Q(1)) for s in (Q(1),r0)]

wide=corners(Q(7,10),Q(3001,3969))
assert wide==[Q(24463,56700),Q(22552343,22680000),
              Q(1936,3969),Q(136920041,158760000)]
assert max(wide)==1-Q(127657,22680000)<1

narrow=corners(Q(117,200),Q(13,16))
assert narrow==[Q(979,2500),Q(319781,320000),
                Q(3,8),Q(14057,20000)]
assert max(narrow)==1-Q(219,320000)<1

# Smaller-offset S3/k3 corollary: far L and D singleton lanes
assert qplus-Q(187,100)**2==Q(4187,10000)
assert Q(13,20)**2-Q(4187,10000)==Q(19,5000)
assert qplus-Q(179,100)**2==Q(1423,2000)
assert Q(27,32)**2-Q(1423,2000)==Q(53,128000)
assert 1789**2-3*1032**2==5449
assert Q(15,137)<Q(1,9)

print("PASS: five-square angular fan and far-singleton rational margins")
