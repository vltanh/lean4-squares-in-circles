#!/usr/bin/env python3
"""Exact arithmetic checks for S3/k3 ray tightening (not proof oracle)."""
from fractions import Fraction as F
z=F(31,50)
ss=z-z**3/6+z**5/120
assert F(117,200)-ss==F(148420849,37500000000)>0
assert 100*117**2-49*26311==79661>0
assert F(22,21)-F(31,50)-F(311,500)==F(-2041,10500)
assert F(44,21)-F(31,50)-F(311,500)==F(8959,10500)
assert F(117,283)>F(2,5)
assert F(5,24)<F(2,9)
print('PASS: improved S3/k3 exact angular-sector margins')
