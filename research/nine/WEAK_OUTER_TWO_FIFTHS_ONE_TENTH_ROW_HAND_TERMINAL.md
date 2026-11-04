# A wider asymmetric replacement row, with every original angle retained

November 4, 2026 (UTC). A conditional strengthening of
`WEAK_OUTER_LARGE_GAP_ASYMMETRIC_REPLACEMENT_ROW_HAND_TERMINAL.md`.
It changes neither the fixed frontier nor a whole-mask ledger. Its hypotheses
must be established on an unchanged original caller before use. No Lean,
Lake or CI. The arithmetic script checks rational identities and constants;
the continuous geometric proof below is also required.

## 1. Statement and physical scope

Retain three distinct original physical unit squares B,X,D and their
independent signed canonical angles in `[-pi/4,pi/4]`. Suppose

\[
x_B\le x_X\le x_D,\qquad
0\le v_1=y_X-y_B\le2/5,\qquad
|v_2=y_D-y_X|\le1/10.                                      \tag{1}
\]

For folded slope `t=|tan(theta)|` define

\[
r(t)=\sqrt{1+t^2},\quad h(t)=(1+t)/(2r(t)),\quad
j(t)=(1-t)/(2r(t)),
\]

\[
T(t)=\max\{2t/(23r(t)),[9t-41(r(t)-1)]/(32r(t))\},
\qquad \sigma(t)=[1+(23/32)t-r(t)]/r(t).
\]

Let `mathcal T_D=T(t_D)` when D tilts nonpositively and
`mathcal T_D=sigma(t_D)` when D tilts nonnegatively. At zero they agree.
Then

\[
x_D-x_B+h_B-h_D+\mathcal T_D\ge2.                         \tag{2}
\]

Equality forces all B,X,D frames aligned and both horizontal gaps one.
Under the full normalized strict original-nine `001/00` caller, (1)
is therefore impossible, including at closed `Q=1105/256`.
The first vertical allowance increases from `1/3` to `2/5`; the last
absolute allowance increases from `1/16` to `1/10`. Every chirality and
physical separator owner remains present.

The horizontal-order equality faces are impossible: the corresponding
vertical gap is less than one, contradicting the unit lower bound on the
distance between centers of two physical original squares. Hence both
horizontal gaps in the proof are positive.

## 2. Accepted physical inputs

The complete original owned-support inequality is

\[
R=H_L(n)+H_R(n)\ge1+\alpha_o|h_L-h_R|,                     \tag{3}
\]

where `alpha_o` is the larger absolute component of the original owner's
folded frame. For `d>0`, `|v|<=u<1/sqrt(2)`, the original incircles give
`d>=sqrt(1-u^2)>|v|`. The steep-axis projection is bounded by the shallow
one after quarter-turning the same owner's support. Thus

\[
d\ge1+|h_L-h_R|+q_u(s_o),\qquad q_u(s)=r(s)-1-us.           \tag{4}
\]

These are Sections 1 and 2 of the preceding asymmetric manuscript, with
no alteration to an owner or physical frame. Its accepted scalar payment
also gives, for `|v|<=1/8`,

\[
d+h_L-h_R+T(t_R)/2\ge1.                                   \tag{5}
\]

If R is aligned, equality in (5) forces L aligned. The original proof
of these two universal inputs is retained unchanged.

## 3. A wider signed upward-pair theorem

If `d>0`, `0<=v<=2/5`, and the right original tilts nonpositively, then

\[
d+h_L-h_R\ge1.                                           \tag{6}
\]

Set `Delta=h_L-h_R` and keep an actual owned separator. An axis with
nonpositive horizontal component projects at most `|v|<1`, so cannot
separate. A shallow axis `(c,s)` with `s<=0` has projection at most `cd`;
(3) directly gives `d+Delta>=1/c+|Delta|+Delta>=1`.

For a shallow axis with `s>0`, the owner is the positively tilted L.
For opposite physical chiralities its exact support sum is
`R=1/2+c h_R+s j_R`. The desired inequality follows if

\[
R+c\Delta-c-sv=(1-c)^2/2+s(c/2+j_R-v)\ge0.                 \tag{7}
\]

Here `j_R>=0`. Put `t=s/c`, `r=sqrt(1+t^2)`, so `0<t<=1`.
Twice the lower bound in (7), multiplied by `r^2`, is

\[
N=2+t+t^2-(2+4t/5)r.
\]

Both quantities being compared are positive, and their squared difference
is exactly

\[
(2+t+t^2)^2-(2+4t/5)^2(1+t^2)
=\frac{t}{25}(9t^3-30t^2+9t+20)>0.                       \tag{8}
\]

The cubic is concave on `[0,1]`, because its second derivative is
`54t-60<0`; its endpoint values are 20 and 8. This proves strict positivity
in (8) for `t>0` and hence (7).

For a steep axis, write its horizontal component as `c` and its vertical
absolute component as `alpha`, with `0<c<=alpha`. If `d+Delta<1`, the
support minus its possible projection is strictly larger than

\[
1-c-(2/5)\alpha+\alpha|\Delta|+c\Delta
\ge1-c-(2/5)\alpha
\ge1-7/(5\sqrt2)>0.
\]

The maximum of `c+(2/5)alpha` on this quarter-circle portion is at
`c=alpha=1/sqrt2`. The final strict comparison has squared reserve
`2-49/25=1/25`. This contradicts separation and finishes (6).

If X and D both tilt nonpositively, use (6) for B,X and (5) for X,D.
Since `1/10<1/8`, their row surplus after the full endpoint toll is at
least `T(t_D)/2`. The equality implication follows exactly as in the
preceding theorem: T vanishes only at zero, (5) then aligns X, and
Section 4 below aligns B.

## 4. First-link deficit when X tilts positively

Set

\[
u=2/5,\quad \delta=1/10,\quad
w=\sqrt{1-u^2}=\sqrt{21}/5,\quad k=u/w=2/\sqrt{21}<1/2,
\]

\[
P(t)=\begin{cases}1-r(t)+ut,&0\le t\le k,\\
                  1-w,&k\le t\le1.\end{cases}
\]

Then the original B,X link obeys

\[
x_X-x_B+h_B-h_X\ge1-P(t_X).                               \tag{9}
\]

Indeed its chosen owner has slope s and (4), after adding the width
adjustment, has surplus at least
`q_u(s)+2(h(s)-h(t_X))_+` over one. The derivative of `q_u+2h` is

\[
(1+s^3)/(1+s^2)^{3/2}-u\ge1/\sqrt2-u>0.
\]

The derivative of q_u vanishes at k. Splitting at `s=t_X` gives the
complete minimum `q_u(min(t_X,k))=-P(t_X)`. No slope subdivision is
omitted. In particular `0<=P<=1-w<1/10`, since `w>9/10`.
When X is aligned, equality in (9) forces B aligned: a nonzero owner
slope gives strict inequality, and an aligned X owner leaves the
nonnegative term `2(h_B-1/2)`.

## 5. The opposite-chirality last link pays the deficit

Suppose X tilts nonnegatively and D nonpositively. Write `t=t_X`,
`z=t_D`. We prove

\[
x_D-x_X+h_X-h_D+T(z)\ge1+P(t),                            \tag{10}
\]

with equality only at `t=z=0`.

A steep original owner gives adjusted gap at least `sqrt2-delta`,
by (3) and the same monotone steep-axis estimate as in the preceding
manuscript. Its surplus in (10) exceeds
`7/5-1-1/10-1/10=1/5>0`.

For a shallow owner X, exact opposite-chirality support gives the lower
bound

\[
r(t)/2+h(t)+t(j_D-\delta)\ge A(t)-\delta t,
\qquad A(t)=r(t)/2+h(t).
\]

For `t<=k`, its surplus over `1+P(t)` is at least
`A(t)+r(t)-2-(u+delta)t`. Since `u+delta=1/2`, this is nonnegative,
and strictly positive for `t>0`. To verify strictness, use

\[
(A+r)'=(1+2t+3t^3)/(2r^3)>1/2\quad(t>0):
\]

`r^3<=(1+t)(1+t^2)`, and the difference of the numerator and this
upper bound is `t(1-t+2t^2)>0`. At `t>=k`, P is constant and
`A'(t)=(1+t^3)/(2r^3)>=1/(2sqrt2)>delta`, so the surplus continues
to increase. If t=0 but z>0, T(z)>0 supplies strictness.

For a shallow owner D, its exact opposite-chirality support gives
surplus in (10) at least

\[
G(t,z)=r(z)/2-h(z)+z(j(t)-\delta)+2h(t)+T(z)-1-P(t).         \tag{11}
\]

For fixed z, its minimum is at `t=0,k,1`. On `[0,k]`, the second
 derivative of the t-dependent part has numerator

`3t(t-1)+z(t^2+3t/2-1/2)`

over the positive denominator `r(t)^5`. For z=0 it is nonpositive;
for z=1 the convex quadratic `4t^2-3t/2-1/2` is negative at both
endpoints of `[0,1/2]`, so it is negative throughout. Its dependence
on z is affine, and `k<1/2`; hence G is concave on the first interval.
On `[k,1]`, use `theta=atan(t)`:
`2h(t)+zj(t)=(1+z/2)cos(theta)+(1-z/2)sin(theta)` is positive and
concave. This proves the complete three-endpoint reduction.

At t=0, the accepted scalar payment (5) gives

\[
G(0,z)\ge q_\delta(z)+T(z)
=q_{1/8}(z)+T(z)+(1/8-\delta)z
\ge T(z)/2+z/40,
\]

strict for z>0. The first inequality follows by squaring
`(2+z)r(z)>=2+z+z^2`; the squared difference is `2z^3`.
At t=k, `h(k)=(w+u)/2` and `j(k)=(w-u)/2>delta`.
Using `r(z)/2-h(z)=(z^2-z)/(2r(z))>=-1/8` and `T>=0`,

\[
G(k,z)\ge 2w+u-2-1/8>2(9/10)+2/5-2-1/8=3/40>0.
\]

At t=1 the same estimates give

\[
G(1,z)\ge\sqrt2+w-2-1/8-\delta
>7/5+9/10-2-1/8-1/10=3/40>0.
\]

Thus (10) holds on every slope and owner alternative. Concavity and
the strict positive nonzero endpoints make equality possible only at
t=z=0. Combining with (9) aligns B as well and proves (2) for D<=0.
For D>=0, the accepted positive-D total-variation theorem applies
because `|v1|+|v2|<=1/2`; it has the same equality characterization.

## 6. Original caller, equality face, and the fixed complement

Retain the complete original-nine strict `001/00` predicate, including
`y_D-y_C>=2/3`, actual AB,BC,EF,FG, all five cones, every corner and
pair, and the strictly weak CD bit. The accepted original D/G order
and horizontal bounds give the upward owned separator required when
using the positive-D cap. The ordinary A/E cap and the appropriate D/G
cap, together with actual AB and EFG and (2), force equality, as in
Section 7 of the preceding asymmetric manuscript. Consequently

`D=(3/2,-1/16)`, `G=(1,15/16)`, `x_B=-1/2`, `x_X=1/2`,

and B,X,D are aligned. Because `|v2|<=1/10<1`, X/G nonoverlap gives
`y_X<=y_D`. Also `y_X>=y_D-1/10>y_C`.
Actual BC gives `x_C>=h_C>=1/2`, and the original CD cone gives
`x_C<=5/6`. With `p=x_C-1/2 in [0,1/3]`,

`1 <= |c_C-c_X|^2 <= p^2+(1-p)^2`.

This forces p=0, then `h_C=1/2`. Hence CD has horizontal gap exactly
one, equal to its two halfwidths, contradicting its retained strict bit.
This is a closed-Q exclusion of the full guarded region.

For either fixed original extra X, every failure of (1) is in one of
six closed domains:

- `x_X<=x_B`;
- `x_D<=x_X`;
- `y_X-y_B<=0`;
- `y_X-y_B>=2/5`;
- `y_D-y_X<=-1/10`;
- `y_D-y_X>=1/10`.

This is an exhaustive complementary cover, with all common faces kept.
A later proof must retain every member until a complete proof discharges
it. This conditional strengthening closes zero original cells and masks
on its own. It introduces no new mandatory gate or original path.
