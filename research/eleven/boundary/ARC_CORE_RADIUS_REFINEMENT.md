# The three inner centers lie inside radius 1.116

The arc argument in [the initial theorem](ANNULAR_ARC_THREE_INNER.md) admits a
stronger center threshold. Define

\[
r_1=\frac{\sqrt7+1}{2}-\frac1{\sqrt2}
\quad(\text{approximately }1.115769),\qquad
\rho=\sqrt2,\quad \gamma=2\arcsin\frac1{2\sqrt2}.
\]

**Refined arc lemma.** Every unit square in the radius-`sqrt(5)` disk whose
center has norm at least `r_1` intersects the circle of radius `rho` in one
connected arc of angular length at least `gamma`.

**Unrestricted consequence.** Every packing of eleven unit squares in a disk
of squared radius at most five has at least three square centers of norm
strictly less than `r_1`. It therefore has at most eight centers at or outside
that radius. No common frame, disk-center occupancy, or contact hypothesis is
assumed.

## 1. The only new geometric branch

Use own-frame center coordinates `a>=b>=0` and put `r=sqrt(a^2+b^2)`,
`x=a-1/2`, `y=b-1/2`, `A=a+1/2`, `B=b+1/2`. As before,

\[
A^2+B^2\le5,\qquad x^2+y^2\le6-\sqrt{19}<2.       \tag{1}
\]

The near-corner estimate applies because `r>=r_1>1>1/2`. Also
`a>=r_1/sqrt(2)>1/2`, so `x>0` and the circle intersection lies in its right
semicircle. The coordinate circle parameters and all arcsines below have
their principal values in `[-pi/2,pi/2]`.

If `A>=rho`, the proof and exact arc formula in Sections 1–3 of the initial
theorem apply unchanged: they only used the earlier threshold to infer
`A>=rho`, `x>0`, and the near-corner estimate. They give arc length at least
`gamma`.

Suppose now `A<rho`. Then `b>1/2`. To check this without a numerical bound,
observe

\[
r_1^2-\bigl((\sqrt2-1/2)^2+1/4\bigr)
=\frac{\sqrt7+\sqrt2-\sqrt{14}}2>0.                \tag{2}
\]

For the final sign, `(sqrt(7)+sqrt(2))^2=9+2sqrt(14)>14`, since `sqrt(14)>5/2`.
Thus `a<rho-1/2` and `r>=r_1` imply `b^2>1/4`. In particular `y>0`.
Since `b<=a`, both `A` and `B` are strictly below `rho` in this branch.

The lower secondary side therefore confines the intersection to positive
circle angles. The far primary side cannot create a second component. The
complete allowed interval has endpoints

\[
L=\max\{\arcsin(y/\rho),\arccos(A/\rho)\},\qquad
U=\min\{\arccos(x/\rho),\arcsin(B/\rho)\}.        \tag{3}
\]

Its length `U-L` is the minimum of the four upper-minus-lower differences.
The three differences other than

\[
L_f=\arcsin(A/\rho)+\arcsin(B/\rho)-\pi/2        \tag{4}
\]

already have bounds at least `gamma` from the initial proof. They are the
near-perpendicular-side difference and the two parallel-side differences.
For the primary parallel sides use
`arccos(x/rho)-arccos(A/rho)=arcsin(A/rho)-arcsin(x/rho)` and the same
nonnegative-derivative argument as for the secondary sides.

It remains to bound (4). This also proves `U>L` and hence existence of the
stated connected arc without presupposing that the square meets the circle.

## 2. The two far sides are worst at the diagonal center

Fix `r>=r_1` and write `a=r cos(theta)`, `b=r sin(theta)`, with
`0<theta<=pi/4`. On the range `A<rho`, increasing `theta` toward `pi/4`
keeps both `A,B` below `rho`: `a` decreases and `b` never exceeds the initial
larger coordinate `a`. Define

\[
F(\theta)=\arcsin\frac{a+1/2}{\rho}
          +\arcsin\frac{b+1/2}{\rho},\qquad
K(z)=z\sqrt{2-(z+1/2)^2}.
\]

Then

\[
F'(\theta)=
\frac{K(a)-K(b)}{
\sqrt{2-(a+1/2)^2}\sqrt{2-(b+1/2)^2}}.            \tag{5}
\]

Writing `s=a+b` and using `a^2+b^2=r^2`, exact expansion gives

\[
K(a)^2-K(b)^2
=(a-b)\left[(7/4-r^2)s-\frac{s^2+r^2}{2}\right]. \tag{6}
\]

Because `(s^2+r^2)/2>=sr` and `r>=r_1>1`, the bracket is at most
`(7/4-r^2-r)s<0`. Both `K(a),K(b)` are nonnegative. Thus `F'(theta)<=0`,
with strict inequality when `a>b`. Its minimum is at `a=b=r/sqrt(2)`.
Consequently

\[
L_f\ge2\arcsin\left(\frac r2+\frac1{2\sqrt2}\right)-\frac\pi2
\ge2\arcsin\frac{\sqrt7+1}{4}-\frac\pi2=\gamma.  \tag{7}
\]

The second inequality is monotonicity in `r`. For the final equality,
`(sqrt(7)+1)/4=sin(pi/4+arcsin(1/(2sqrt(2))))`, with the angle strictly
between zero and `pi/2`. Equations (3)–(7) prove the refined arc lemma.

For completeness, `r_1>1` follows from `sqrt(7)>1+sqrt(2)`, since
`7>3+2sqrt(2)`. The estimate `x>0` follows already from `r_1>1` and
`a>=r/sqrt(2)`.

## 3. The unrestricted count

Each qualifying square contributes angular measure at least `gamma` on the
circle of radius `sqrt(2)`. Open-square interiors have the same measure as
closed squares because their boundaries meet the circle in finitely many
points. The open-square intersections are pairwise disjoint.

As in the initial theorem, `9gamma>63/10>44/7>2pi`. There are at most eight
qualifying squares, so at least three of eleven centers satisfy `||p||<r_1`.

The result remains a necessary radial classification, with all 55 pair
constraints retained. It does not show there are exactly three inner centers,
force any center into the origin-containing square, or supply a sharp lower
bound. Those further geometric obligations remain open.
