# An asymmetric replacement row closes the near-central height range

November 3, 2026. Complete hand argument after computer-assisted
discovery of the signed physical gate. The original two replacement
links may both be weak. No small-angle or common-frame assumption is
made. No Lean, Lake, or CI.

## 1. The original row region

Let B,X,D be three distinct unchanged original physical unit squares.
Assume

\[
 x_B<x_X<x_D,\qquad
 0\le y_X-y_B\le\frac13,\qquad
 |y_D-y_X|\le\frac1{16}.                              \tag{1}
\]

These asymmetric bounds include the continuous aligned boundary
family in which B moves below the middle row while X stays at the
height of D. The proof covers every original chirality and every
physically possible separating owner of either link.

Write a signed canonical frame angle as `theta in [-pi/4,pi/4]`.
For its folded slope `t=|tan(theta)| in [0,1]`, put

\[
 r(t)=\sqrt{1+t^2},\quad
 \alpha(t)=1/r(t),\quad \beta(t)=t/r(t),\quad
 h(t)=\frac{1+t}{2r(t)},\quad j(t)=\frac{1-t}{2r(t)}.
\]

The folded endpoint toll already accepted in
`WEAK_OUTER_NUMERIC_NEAR_HORIZONTAL_REPLACEMENT_ROW_HAND_TERMINAL.md`
is

\[
 T(t)=\max\left\{\frac{2\beta(t)}{23},\;
       \frac{9\beta(t)-41(1-\alpha(t))}{32}\right\}.   \tag{2}
\]

For nonnegative signed D tilt, the accepted upward-separator signed
cap instead supplies

\[
 \sigma(t)=\alpha(t)-1+\frac{23}{32}\beta(t).           \tag{3}
\]

Set `mathcal T_D=sigma(t_D)` for nonnegative D tilt and
`mathcal T_D=T(t_D)` for nonpositive D tilt. Both definitions agree
at zero. The row theorem is

\[
 \boxed{x_D-x_B+h_B-h_D+\mathcal T_D\ge2.}             \tag{4}
\]

Equality in (4) forces B,X,D all aligned and both original horizontal
gaps equal to one. Sections 2--5 prove the complete nonpositive-D
part. The completed positive-D total-variation theorem proves
the other part, as recorded in Section 6.

## 2. Two general physical pair estimates

### 2.1. The same original owned support retains width differences

For an owned physical separating axis, let `alpha>=beta>=0` be the
folded components of its owner. The accepted all-owner support lemma
gives

\[
             R=H_L(n)+H_R(n)\ge1+\alpha|h_L-h_R|.    \tag{5}
\]

Its proof is included in the earlier near-horizontal manuscript.
Centered square support is invariant under a quarter turn, so (5)
also applies to a steep owned axis, with alpha still its larger
folded component. The original owner is retained.

If the original center difference is `(d,v)`, `d>0`, `|v|<=U<1/sqrt(2)`,
then the contained open radius-1/2 disks give `d>=sqrt(1-U^2)>U`.
Any steep projection is therefore no larger than
`alpha*d+beta*U`, and the same bound holds for a shallow projection.
Equation (5) yields

\[
 d\ge1+|h_L-h_R|+q_U(s),\qquad
 q_U(s)=\sqrt{1+s^2}-1-Us,\quad s=\beta/\alpha.       \tag{6}
\]

All owners, axes, and signs are covered. A normal with nonpositive
horizontal component cannot separate, because its projection is at
most `|v|<1`, below the support sum.

### 2.2. A last link of height at most 1/8 costs only half a toll

The previously proved complete scalar payment is

\[
 q_{1/8}(s)+(h(s)-h(t))_++T(t)/2\ge0,                 \tag{7}
\]

with equality only at `s=t=0`. Apply (6) to a physical L,R link of
height at most 1/8. Its adjusted horizontal gap obeys

\[
 d+h_L-h_R\ge1+q_{1/8}(s)+2(h_L-h_R)_+.
\]

The chosen owner is L or R, so the last width term is at least
`(h(s)-h_R)_+`. Hence (7) proves the one-link consequence

\[
                   d+h_L-h_R+T(t_R)/2\ge1.           \tag{8}
\]

When `t_R=0`, equality in (8) forces L aligned too: (7) forces the
chosen owner aligned, and the remaining nonnegative width variation
forces `h_L=1/2`.

## 3. An upward link whose right original tilts nonpositively

We first prove a signed pair lemma. If

\[
 d>0,\qquad 0\le v\le1/3,\qquad\theta_R\le0,
\]

then

\[
                         d+h_L-h_R\ge1.              \tag{9}
\]

Keep an actual owned separator and put `Delta=h_L-h_R`.

For a shallow owned normal `(c,s)` with `c>=|s|` and `s<=0`, its
projection is at most `c*d`. Equation (5) therefore gives
`d+Delta>=1/c+|Delta|+Delta>=1`.

For a canonical horizontal owned axis with positive vertical component,
the owner must be the positively tilted left square L. The nonpositive
right frame's other forward axis is its canonical vertical axis and is
treated in the steep case below, including its diagonal boundary.
Write the shallow normal's components
as `(c,s)`, with `c>=s>0`, and put `j_R=(alpha_R-beta_R)/2>=0`.
The opposite physical chiralities give the exact owned support sum

\[
                         R=1/2+c h_R+s j_R.
\]

The desired adjusted gap follows because

\[
 R+c\Delta-c-sv
 =\frac{(1-c)^2}{2}
       +s\left(\frac c2+j_R-v\right)\ge0,
\]

using `c/2>=1/(2sqrt(2))>1/3>=v`. A diagonal canonical horizontal
axis is included in this calculation; canonical vertical axes are
covered by the following steep calculation.

Finally suppose the owned axis is steep, with positive horizontal
component c and vertical absolute component alpha, where
`0<c<=alpha`, `c^2+alpha^2=1`. If `d+Delta<1`, then (5) minus its
possible center projection is strictly greater than

\[
 1-c-\alpha/3+\alpha|\Delta|+c\Delta
 \ge1-c-\alpha/3
 \ge1-\frac4{3\sqrt2}>0.
\]

The last maximum occurs at `c=alpha=1/sqrt(2)`. This contradicts
physical separation. It proves (9) for every steep owner as well.

If D and X both tilt nonpositively, apply (9) to B,X and (8) to X,D.
The two adjusted gaps plus the full endpoint T then have surplus at
least `T(t_D)/2` over two. This already proves (4) in this case.
If equality holds, `T(t_D)=0` forces D aligned, (8) forces X aligned,
and the equality discussion in Section 4 below forces B aligned.

## 4. The exact first-link deficit for a positive X tilt

For the remaining case write `t=t_X>=0` and define

\[
 U=1/3,\quad \delta=1/16,\quad k=1/\sqrt8,
 \qquad
 P(t)=\begin{cases}
 1-r(t)+t/3,&0\le t\le k,\\
 1-2\sqrt2/3,&k\le t\le1.
 \end{cases}                                         \tag{10}
\]

The first original link, regardless of B's chirality, satisfies

\[
                    x_X-x_B+h_B-h_X\ge1-P(t).        \tag{11}
\]

Indeed (6) gives, for its chosen owner's folded slope s, a lower
bound of one plus

\[
                   q_U(s)+2(h(s)-h(t))_+.
\]

For `s>=t`, its derivative in s is

\[
 (q_U+2h)'(s)=\frac{1+s^3}{(1+s^2)^{3/2}}-\frac13
       \ge\frac1{\sqrt2}-\frac13>0.                 \tag{12}
\]

The fraction decreases on `[0,1]`, since its derivative is
`3s(s-1)/(1+s^2)^(5/2)`. For `s<=t`, the minimum of q_U occurs at
`s=min(t,k)`, because `q_U'(s)=s/r(s)-1/3`. The complete minimum is
therefore `-P(t)`, proving (11).

If X is aligned, P(0)=0. Equality in (11) forces B aligned: an owner
with nonzero slope makes (12) strict; if the chosen owner is aligned
X, the unused width variation is `2(h_B-1/2)`, which must vanish.

We will use the exact global bounds

\[
          0\le P(t)\le1-2\sqrt2/3<1/16.             \tag{13}
\]

The final comparison follows from `sqrt(2)>45/32`, whose squared
reserve is `23/1024`.

## 5. The opposite-chirality last link repays the first deficit

Suppose X tilts nonnegatively and D nonpositively. Let `t=t_X` and
`z=t_D` be their folded slopes. We prove

\[
 x_D-x_X+h_X-h_D+T(z)\ge1+P(t),                      \tag{14}
\]

with equality possible only if `t=z=0`. Combined with (11), this
proves the remaining nonpositive-D part of (4).

### 5.1. Every steep owner has ample positive reserve

Let a steep owned normal have horizontal component beta>0 and vertical
absolute component alpha>=beta. Put `Delta=h_X-h_D`. From (5),

\[
 d+\Delta\ge
 \frac{1-\alpha\delta+\alpha|\Delta|+\beta\Delta}{\beta}
 \ge\frac{1-\alpha\delta}{\beta}
 \ge\sqrt2-\delta.                                   \tag{15}
\]

The last function decreases as beta increases to `1/sqrt(2)`: its
derivative is `(delta/alpha-1)/beta^2<0`. By (13),
`sqrt(2)>7/5`, and `T>=0`, its surplus in (14) exceeds `11/40`.
Thus a steep owner cannot be an equality case.

### 5.2. A shallow owner X

Write the shallow X normal as `(alpha_X,beta_X)`. The exact support
sum for these opposite chiralities is
`1/2+alpha_X*h_D+beta_X*j_D`. Taking the worst allowed vertical gap
therefore gives

\[
 d+h_X-h_D\ge r(t)/2+h(t)+t(j_D-\delta)
             \ge A(t)-\delta t,
 \qquad A(t)=r(t)/2+h(t).                             \tag{16}
\]

For `t<=k`, subtracting `1+P(t)` from the last expression gives

\[
 A(t)+r(t)-2-(U+\delta)t\ge(1/2-U-\delta)t
                           =5t/48.                   \tag{17}
\]

To justify the derivative used here,

\[
 (A+r)'(t)=\frac{1+2t+3t^3}{2(1+t^2)^{3/2}}\ge1/2.
\]

Indeed `r^3<= (1+t)(1+t^2)` and the remaining numerator difference
is `t(1-t+2t^2)>=0`. Both sides of the integrated comparison equal
two at t=0. For `t>=k`, P is constant and
`A'(t)=(1+t^3)/(2r^3)>=1/(2sqrt(2))>delta`, so the lower surplus
continues to increase. This proves (14) for this owner, strictly
when `t>0` or when `z>0` contributes its positive endpoint toll.

### 5.3. A shallow owner D: only three exact X slopes remain

The D normal is `(alpha_D,-beta_D)`. Its exact support sum is
`1/2+alpha_D*h_X+beta_D*j_X`. After taking the worst allowed vertical
gap, its surplus in (14) is bounded below by

\[
 G(t,z)=\frac{r(z)}2-h(z)+z(j(t)-\delta)
            +2h(t)+T(z)-1-P(t).                     \tag{18}
\]

For fixed z, this has its minimum at one of

\[
                            t=0,\quad k,\quad1.      \tag{19}
\]

On `[0,k]`, the second derivative of the t-dependent part has numerator

\[
 3t(t-1)+z(t^2+3t/2-1/2)
\]

over the positive denominator `r(t)^5`. It is nonpositive throughout
`0<=t<=k<1/2`: at z=0 it is `3t(t-1)<=0`, while at z=1 it is
`4t^2-3t/2-1/2`, whose maximum on `[0,1/2]` is at an endpoint and
is at most `-1/4`. The numerator is affine in z, so this covers
every z in `[0,1]`. Hence G is concave on the first interval.

On `[k,1]`, P is constant. In the angle `theta=atan(t)`, the remaining
t-dependence is

\[
 2h(t)+zj(t)=(1+z/2)\cos\theta+(1-z/2)\sin\theta,
\]

a positive, concave function. Its minimum is again at an endpoint.
This proves the complete reduction (19).

At t=0, the support-width inequality or direct squaring gives

\[
 G(0,z)\ge q_\delta(z)+T(z)
 =q_{1/8}(z)+T(z)+z/16\ge T(z)/2+z/16.              \tag{20}
\]

For a direct check of the first step, its remainder is
`1-r(z)/2-h(z)+z/2>=0`; after multiplying by `2r(z)`, this is
`(2+z)r(z)>=2+z+z^2`. The exact difference of their squares is
`2z^3>=0`. The final step is the old scalar payment (7) with s=z.
Thus (20) is strict whenever z>0.

At `k=1/sqrt(8)`,

\[
 h(k)=(2\sqrt2+1)/6,\qquad j(k)=(2\sqrt2-1)/6.
\]

Also

\[
 r(z)/2-h(z)=\frac{z^2-z}{2r(z)}\ge-1/8.
\]

Since `j(k)>delta` and `T>=0`, equation (18) gives

\[
 G(k,z)\ge\frac{4\sqrt2-5}{3}-\frac18
          >\frac15-\frac18=\frac3{40}>0,             \tag{21}
\]

using `sqrt(2)>7/5`. At t=1, j(1)=0, and the same crude lower bound
gives

\[
 G(1,z)\ge\frac{5\sqrt2}{3}-2-\frac18-\frac1{16}
           >\frac13-\frac3{16}=\frac7{48}>0.         \tag{22}
\]

The three endpoint checks prove (14) for this final owner. If z>0,
all three endpoint bounds are strictly positive. If z=0, only the
t=0 endpoint can have equality; concavity together with the positive
other endpoint gives strict positivity for every t>0 in either
interval. Thus equality in (14) requires X,D both aligned.

This exhausts every owned axis and physical chirality in the remaining
case. Equation (11) then forces B aligned too when the total row
inequality has equality.

## 6. Positive D and the complete equality statement

For nonnegative signed D tilt,
`WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md`
proves the same row inequality with sigma whenever

\[
 |y_X-y_B|+|y_D-y_X|\le1/2.
\]

The rectangle (1) has total variation at most
`1/3+1/16=19/48<1/2`. That complete hand proof retains all physical
owners and has equality only when B,X,D are aligned. Together with
Sections 3--5, it proves (4) for both signs of the original D frame.

Once the three originals are aligned, both vertical gaps in (1) are
strictly below one. Original physical nonoverlap therefore gives each
horizontal gap at least one. Equality in (4), where the toll and width
difference vanish, forces both gaps exactly one. No equality of their
heights is claimed or needed.

## 7. Strict closed-Q terminal in the unchanged 001/00 caller

Retain all nine originals of the strict caller at
`Q=1105/256`, normalized by `y_D-y_C>=2/3`. Let X be either unchanged
extra original satisfying (1). The original A/B actual comparison and
(4) give

\[
 x_D-x_A-h_A-h_D+\mathcal T_D\ge2.
\]

The two actual original short links have adjusted span at least one.
Add the ordinary A/E cap to the D/G cap with the valid toll chosen
in (2)--(3). The signed positive-D cap has the required upward owned
D/G separator from the accepted G-order and horizontal-gap theorems.
The total weighted cap is at most `211/2` and the preceding spans
make it at least `2*46+27/2=211/2`. Thus equality holds everywhere,
including (4), and B,X,D are aligned.

The unchanged physical endpoint-cap equality theorem gives

\[
              D=(3/2,-1/16),\qquad G=(1,15/16),
 \qquad x_B=-1/2,\quad x_X=1/2.
\]

The original G-order supplies the stated sign of the endpoint heights.
X and G are aligned and have horizontal gap one half. Since
`y_X<=y_D+1/16<y_G`, their physical nonoverlap forces `y_X<=y_D`.
Also `y_X>=y_D-1/16>y_C` by the unchanged C/D transverse lower bound.

The original B/C actual comparison gives `x_C>=h_C>=1/2`, while
the original C/D cone gives `x_C<=5/6`. Put `p=x_C-1/2`, so
`0<=p<=1/3`. Then the unchanged C,X centers satisfy

\[
 0<y_X-y_C\le y_D-y_C\le x_D-x_C=1-p,
 \qquad 1\le|c_C-c_X|^2\le p^2+(1-p)^2.
\]

The last upper bound is strictly below one for `0<p<=1/3`, so p=0.
Now `1/2=x_C>=h_C>=1/2` makes C aligned. Its original horizontal
gap to D is exactly one, equal to `h_C+h_D`, contradicting the
unchanged **strict** C/D weak bit.

The horizontal-order boundary faces are also impossible in the
stated vertical rectangle: if `x_X=x_B`, their vertical gap is at most
1/3; if `x_X=x_D`, it is at most 1/16. Either case contradicts the
unit lower bound on the distance between original centers. Thus the
full closed asymmetric row region is excluded from the strict original
caller. Its complement is covered by the closed alternatives

\[
\begin{array}{ll}
 x_X\le x_B,&x_X\ge x_D,\\
 y_X-y_B\le0,&y_X-y_B\ge1/3,\\
 y_D-y_X\le-1/16,&y_D-y_X\ge1/16.
\end{array}
\]

Shared boundary faces are retained. The theorem does not assert that
every original configuration lies in this row region. It is a complete
analytic terminal for later exhaustive original-nine routing, and by
itself changes no whole-mask coverage count.

## 8. Exact scalar checks and review boundary

`computer_assisted/weak_outer_hand_asymmetric_row_arithmetic.py`
checks the rational constants, squared comparisons, coefficient
identities, and concavity endpoint reserves used above. The continuous
physical support, derivative, owner, and equality arguments are given
in the manuscript, rather than inferred from a numerical grid.

The root proof integrator, the numerical-discovery reviewer, and the
global-extraction reviewer each independently read the complete
physical, scalar, equality, and strict-caller argument and accepted it.
The separate complete review is
`GLOBAL_OUTER_LINK_EXTRACTION_ASYMMETRIC_ROW_INDEPENDENT_REVIEW.md`.
The positive-D companion and its independent review are bound in the
same component manifest. The exact shared-face audit
`computer_assisted/weak_outer_numeric_strict_bulk_v3_boundary_coverage.py`
checks the whole closed canonical middle-B interval, including the
intersection of the old symmetric and new asymmetric escape branches.
Its saved PASS report is bound too. These component acceptances do not
assert completion of the remaining original-nine routing forest.
