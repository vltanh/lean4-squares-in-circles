# Independent audit of the whole middle/middle hand entry

**Verdict: PASS.** The complete entry is strictly greater than
\(557/625=.8912\), with all eight source-axis/sign branches and their
reflected target images covered. The proof does not use the frame
concentration conclusion it is intended to establish.

Reviewed files:

* `MID_MID_WHOLE_PAIR_HAND_PROOF.md`, SHA256
  `a084fa1c08af25dc18ff80f06ff19de39576009ec958f285fc6f27a61febeaab`.
* `verify_mid_mid_whole_pair_hand.js`, SHA256
  `688a6114311d51e18d44ba07ec49dc8327e4491f045f7c34b1ce3475e346965c`.

The author's standalone replay passes all **111** strict comparisons.
The separate Fraction implementation
`audit_mid_mid_polynomial_rows.py` reconstructs both polynomials directly
from the displayed formulas, without importing the author's polynomial
generator. It independently verifies all **36** printed lower bounds for
the squared comparison polynomials and all **19** positive-factor bounds.

## 1. Continuous geometry and the delicate contact regime

The source/target coordinates and signs agree with the actual own-frame
centers \((a,-\sigma b),(A,-\tau B)\). Both retained source margins
are correct. Reflection followed by reversal interchanges the states
and sends signs to \((-\tau,-\sigma)\); both the cost and the relative
frame angle are preserved. This accounts for every retained target axis.

For the positive/negative transverse regime, the necessary initial angle
range is \(-.05<\phi\le.32\). The source projection increases with
both transverse coordinates because \(D=\cos\phi-r(B)\sin\phi>.75\).
The lower/lower endpoint pair is infeasible throughout that interval.
Thus a feasible pair can be moved to contact while decreasing its two
increasing labels. The deformed contact point need not retain the
original center-angle constraint: the subsequent inequality is proved
on the larger contact domain at fixed \(\phi\), so no such assumption
is made or needed.

At contact, independent differentiation gives

\[
b_B=-D,\quad b_{BB}=r'(B)\sin\phi,
\quad
\mathcal C_{BB}=-p r'(b)D^2+r'(B)(M'(b)\sin\phi-p)<0.
\]

The feasible contact parameter set is an interval since \(b_B<0\).
Its minimum is at a state endpoint. At zero angle, the contact is
\(b+B=1\); both feasible endpoint minima equal
\(2c_M+q+p(a_h+a(1-b_h))>.891245701181112\).
The stated lower radical comparison has the correct adverse direction:
using the lower bound for \(b_h\) makes \(3/2-b_h\) larger and the
corresponding radical smaller.

For negative angles, contact forces \(b+B>1\), so neither state can
be the lower endpoint. Every endpoint branch therefore fixes an upper
endpoint, and the other coordinate decreases to \(1-b_h\) as the
angle approaches zero. Both displayed derivatives are strictly negative;
the denominator bounds for \(D\) have the correct directions.

For positive angles, the fixed-target derivative is strictly positive.
For a fixed source, the quotient

\[
J(B)=\frac{A-1/2+(1/2-B)\tan\phi}{1-r(B)\tan\phi}
\]

is positive and decreasing. Its derivative numerator is
\((-r-t)D_0+N_0r't\), and the printed estimates make it negative.
Since \(M'(B)\) is also positive and decreasing, the endpoint bound
for their product is valid. This proves the fixed-source derivative
positive as well.

The boundary continuation argument is complete. Following a fixed
lower endpoint backward can only stop when the other coordinate first
reaches the upper endpoint. At that point one switches to the upper
endpoint branch, which reaches the parallel contact without leaving the
middle arc. The two derivative estimates apply on both sides. No
contact boundary component is omitted.

## 2. Remaining source branches and angle tails

For a negative transverse source, both remaining sign cases before
their tails lie in \(0<\phi<\pi\). The margin is bounded by
\(-.8246+.799\sin\phi+.014|\cos\phi|<0\); the squared-amplitude
test is sufficient on this entire interval. Positive/positive
transverse separation uses a valid positive multiplier and the upper
endpoint minimum of a concave source functional.

The primary margin is independent of the source sign, so replacing a
positive source label by its negative proves a stronger inequality for
both signs. For a negative target, negative angles and the interval
through 1.05 are ruled out by the stated projection barriers. The two
target endpoint estimates then cover [1.05,1.09], including the possible
change of sign of \(.41-b_j\). For a positive target, the entire first
quadrant is impossible; the norm polynomial covers [1.57,1.85], including
the quarter-turn endpoint. The direct tails cover all larger angles
without any further separator assumption.

All starting angle bounds follow from \(\delta>.76\) and the full
middle arc: the same-sign difference is less than .16, and each
individual angle lies strictly between .24 and .405. There are no
gaps between the contact, barrier, polynomial or direct-tail domains.

## 3. Independent polynomial reconstruction

The proof's whole-circle support bound is valid on the restricted arc.
Its two norm expressions and trigonometric coefficients were separately
rederived from the relevant source margin. The alternating Taylor
choices lower the positive comparison factor and upper-bound the
squared norm on both closed intervals.

| Row | Interval | Degree of \(P\) | Independently checked \(P\) bounds | Degree of \(T\) | Independently checked \(T\) bounds |
|---|---|---:|---:|---:|---:|
| transverse positive/positive | [.6,1.09] | 16 | 17 | 8 | 9, each greater than 4 |
| primary positive target | [1.57,1.85] | 18 | 19 | 9 | 10, each greater than 3 |

Every comparison passes with a strictly positive exact rational reserve.
Thus both \(T\) and \(T^2-QV\) are positive throughout the specified
intervals, proving the strict square-root inequalities.

This audit closes the M/M entry as a whole-domain hand theorem. It does
not substitute for the two wrong-word exclusions or candidate capture,
which remain separate global obligations.
