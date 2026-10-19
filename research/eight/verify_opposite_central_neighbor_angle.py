#!/usr/bin/env python3
"""Exact arithmetic certificate for HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md.

The all-frame proof uses the previously hand-proved sharp one-square
cap envelope ONLY for offsets >=2/5; for smaller offsets on one
side it uses the universal radial center bound. This checker
replays all rational endpoints of the four-interval argument.
"""
from fractions import Fraction as F
q=F(9789,2500)
r0=F(283,200)
r2=r0*r0
assert r2==F(80089,40000)
assert r2+r0+F(1,2)-q==F(65,40000)>0

checks={
    'large h>=1/2, yA<4/5':
        (F(13,10)**2-(q-F(3,2)**2),F(61,2500)),
    'small k>=2/5, yB<9/10':
        (F(7,5)**2-(q-F(7,5)**2),F(11,2500)),
    'large h>=3/5, yA<2/3':
        (F(7,6)**2-(q-F(8,5)**2),F(31,5625)),
    'small k>=3/10, yB<6/5':
        (F(6,5)**2-(r2-F(4,5)**2),F(3111,40000)),
    'large h>=7/10, yA<13/25':
        (F(51,50)**2-(q-F(17,10)**2),F(37,2500)),
    'small k>=1/5, yB<5/4':
        (F(5,4)**2-(r2-F(7,10)**2),F(2011,40000)),
    'large h>=4/5, yA<1/3':
        (F(5,6)**2-(q-F(9,5)**2),F(106,5625)),
}
for name,(actual,expected) in checks.items():
    assert actual==expected>0,(name,actual,expected)

reserves=[
  F(99,100)-F(4,5)*F(9,10),
  F(24,25)-F(2,3)*F(6,5),
  F(91,100)-F(13,25)*F(5,4),
  F(3,4)-F(1,3)*r0,
]
assert reserves==[F(27,100),F(4,25),F(13,50),F(167,600)]
assert min(reserves)==F(4,25)
assert F(4,25)/r2==F(6400,80089)
assert F(6400,80089)-F(1,13)==F(3111,1041157)>0
print("PASS: opposite central cap center dot<-4/25, angle>pi/2+1/13")
