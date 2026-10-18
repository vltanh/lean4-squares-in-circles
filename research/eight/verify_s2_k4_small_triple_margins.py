#!/usr/bin/env python3
"""Exact arithmetic audit for HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md.

Checks only the displayed rational endpoints. The analytic angular
argument lives in the Markdown proof, not in this diagnostic script.
No numerical mesh, generated case cover, or global n=8 proof.
"""
from fractions import Fraction as Q

qplus=Q(9789,2500)
r0=Q(283,200)
assert r0*r0+r0+Q(1,2)-qplus==Q(65,40000)

# Inner radius >=3/5, outer <=283/200:
# mixed separation must exceed delta*=631/1000 radians.
x=Q(631,1000)
taylor=1-x*x/2+x**4/24-x**6/720
assert taylor-Q(803,1000)==Q(3194884125544152719,
                            720000000000000000000)>0

values=[r*r+s*s-2*Q(803,1000)*r*s
        for r in [Q(3,5),Q(1)]
        for s in [Q(1),r0]]
assert values==[
    Q(991,2500),Q(998731,1000000),
    Q(197,500),Q(145947,200000)
]
assert max(values)==1-Q(1269,1000000)<1

# Two consecutive outer-center angular gaps each have width < W.
# W=4pi/9-17/125, with pi<22/7.
W_upper=Q(4,9)*Q(22,7)-Q(17,125)
assert W_upper==Q(9929,7875)
assert 2*x-W_upper==Q(37,31500)>0

# Above-upper-outer sector is separated from U+ by <pi/3.
# Since theta_R>765/1000, theta_U+<5pi/12,
# upper-minus-lower<pi/3 iff theta_R>pi/12.
assert Q(765,1000)>Q(22,7)/12

print("PASS: S2/k4 near-inner h_R<1/10 rational margins")
