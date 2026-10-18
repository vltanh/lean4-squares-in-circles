# Independent audit: the whole high/high frame proof

**Result: PASS.** Reviewed versions:
- HIGH_HIGH_WHOLE_PAIR_HAND_PROOF.md SHA-256 c77a2d82c8d459d6138b74f3a05faa9e0d0e154c0ec708e84209e9542445b149.
- verify_high_high_whole_pair_hand.py SHA-256 25d36a437cb65cbbae58e44af059597d9aa907ae7763067df557c99405d25cd5.

The geometry and calculus were independently rederived. The supplied checker
passed all 83 fixed strict comparisons. A separate dictionary-polynomial
implementation, not importing the supplied checker, rebuilt the degree-14
polynomial, substituted x=.6+.35y, converted to Bernstein form, and matched
all 15 printed rational coefficient bounds.

The fold (a,b)=(a_o+b_o,a_o-b_o), sign -sigma_o and frame rotation
-sigma_o*pi/4 give centre (a,-sigma*b)/sqrt(2). The new label
L=pi/4-L_H preserves the exact frame residual. The folded radial square
Q-a-1/2 and incircle separation imply delta>2 atan(2/5), hence folded phi>0.

The two extra diagonal source directions are excluded by the stated cap
bounds. The remaining margin is exactly
M=a+sigma*b+D*A-tau*C*B-1-C, where C=sin(phi)+cos(phi) and D=sin(phi)-cos(phi).
Reflected reversal sends (sigma,tau) to (-tau,-sigma), preserves the cost,
and swaps source and target axes. The four sign cases therefore cover all
retained axes.

Every endpoint, monotone-arc and circle support choice, its coefficient
sign conditions, and every interval junction were checked. The varying
multiplier negative/negative branch has the stated target coefficient
signs; the late negative/positive branch retains its full cut-endpoint term.

The norm identity
N''+N/4=(u^2+v^2-2*lambda^2)^2/(4*N^3)
was independently derived. Its positive denominator, the concavity estimates,
and endpoint derivative tests have the required signs.

Before the varying-multiplier polynomial is squared, its lower trigonometric
polynomial T is positive. The cosine lower polynomial is positive, and the
sine upper polynomial is at most one. Thus every coefficient replacement
and squaring step preserves the claimed inequality.

The independently reconstructed Bernstein lower numerators, denominator
10^8, are:
6008661, 4521736, 3269000, 2241201, 1427808, 817238, 397075, 154297,
75489, 147054, 355411, 687182, 1129359, 1669462, 2295674.
They match the entire printed list and are all positive.

Scope is the physical seven-ring after the preceding global elimination of
backward axes. No isolated-pair theorem allowing those discarded axes is
inferred. No geometry, sign, support-coverage or arithmetic gap was found.

