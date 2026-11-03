# A uniform nonlinear lift of the deep-B boundary tangent system

November 3, 2026. Complete hand estimates for the necessary inequalities.
The final neighborhood radius is supplied by a separate exact rational
dual table. No linearized numerical optimization alone is a packing
proof. No Lean, Lake, or CI.

## 1. Fixed original boundary configuration and local variables

The base centers, in the order A,B,C,D,E,F,G,H,I, are

\[
\begin{array}{c|rrrrrrrrr}
&A&B&C&D&E&F&G&H&I\\\hline
x&-3/2&-1/2&1/2&3/2&-1&0&1&-1/2&1/2\\
y&-1/16&-17/16&-17/16&-1/16&15/16&15/16&15/16&-1/16&-1/16.
\end{array}
\]

Every original is aligned at the base. For an actual nearby physical
packing write its unchanged center as `c_i=c_i^0+e_i` and its signed
canonical angle as `theta_i`. Angles are measured in radians, with the
same horizontal and vertical axes as the fixed marked caller. Define

\[
 z_i=|\theta_i|,\qquad
 \eta=\max_i\{|e_{ix}|,|e_{iy}|,|\theta_i|\},\qquad
 \Theta=\sum_i|\theta_i|,
 \qquad 0\le\eta\le1/8.                              \tag{1}
\]

The first-order variables are the 18 center shifts, the nine signed
angles, and the nine values z_i. They are values attached to the same
original physical squares; no new replacement configuration is chosen.

We give necessary upper bounds for every homogeneous linear row reconstructed
in `computer_assisted/weak_outer_deep_boundary_verify.py`. The original
floating first-order exploration is not a proof input. In the convention `L_j(w)<=0`
used by that tangent system, the nonlinear packing satisfies

\[
\begin{array}{c|c}
\text{row type}&\text{necessary nonlinear upper bound for }L_j\\\hline
\text{original active circle corner at }i&(3/2)\eta|\theta_i|\\
\text{marked actual horizontal link }i,j&(1/2)\eta(|\theta_i|+|\theta_j|)\\
\text{physical contact of }i,j&3\eta(|\theta_i|+|\theta_j|)\\
\text{absolute values, signs, marked cones, closed weak row}&0.
\end{array}                                                        \tag{2}
\]

In particular every row has upper bound `3*eta*Theta`. The absence of
any error depending only on the center shifts is essential: several
aligned center motions can survive in the tangent system.

## 2. Frame and owned-pair estimates

For `|s|<=1/4`, elementary integral or Taylor remainder bounds give

\[
\begin{gathered}
 \cos s\ge1-s^2/2,\qquad |\sin s|\ge|s|-|s|^3/6,\\
 |\sin s-s|\le|s|^3/6,\qquad |\sin s|\le|s|.
\end{gathered}                                                       \tag{3}
\]

The exact coordinate halfwidth of original i is

\[
 h_i=\frac{\cos\theta_i+|\sin\theta_i|}{2},
\]

so

\[
 \frac12+\frac{z_i}{2}-\frac{\theta_i^2}{4}
       -\frac{z_i^3}{12}
 \le h_i\le\frac12+\frac{z_i}{2}.                   \tag{4}
\]

For a physical separating axis owned by either original i or j, the
exact support sum is

\[
 R_{ij}=\frac{1+\cos\Delta+|\sin\Delta|}{2},
 \qquad \Delta=\theta_j-\theta_i.
\]

Here `|Delta|<=2eta<=1/4`, so the cosine has the displayed positive
sign, and the value is unchanged when the owned axis is turned through
a right angle. Put `U=|theta_i|+|theta_j|`. Equation (3) gives

\[
\begin{aligned}
 R_{ij}
 &\ge1+|\Delta|/2-\Delta^2/4-|\Delta|^3/12\\
 &\ge1+|\Delta|/2-
       \left(\frac12+\frac\eta3\right)\eta U\\
 &\ge1+|\Delta|/2-\frac{13}{24}\eta U.              \tag{5}
\end{aligned}
\]

All owned-axis choices and original chiralities are retained in this
estimate.

## 3. Which owned axes can separate each nearby contact

Every component of a center-difference change has magnitude at most
`2eta`. A pair with base difference `(1,0)` can only separate on a
positive shallow owned axis: projection on any steep axis has absolute
value at most

\[
 2\eta+\eta(1+2\eta)=3\eta+2\eta^2\le13/32<1.
\]

The support sum is always at least one. Negative shallow axes also
cannot separate, since their projection is negative for `eta<=1/8`.
The same argument with the coordinates interchanged applies to a pair
with base difference `(0,1)`.

For the six upper contacts with base difference `(sigma/2,1)`, where
`sigma=+1` or `-1`, any shallow projection is at most

\[
 1/2+2\eta+\eta(1+2\eta)
 =1/2+3\eta+2\eta^2\le29/32<1.                     \tag{6}
\]

Hence only a positive upward steep axis is possible. For the diagonal
C/D base difference `(1,1)`, only the positive shallow or the positive
upward steep alternatives remain. The negative signs have negative
projection because each positive difference component is at least
`3/4` while its absolute tilt is at most `1/8`.

These strict bounds justify the local separator union. They do not
infer a fixed owner: either original continues to be available.

## 4. Nonlinear errors for the physical contact rows

Let `(dx,dy)` denote the center-difference increment, rather than the
full difference, so `|dx|,|dy|<=2eta`.

### 4.1. Horizontal and zero-offset vertical contacts

For a horizontal base difference `(1,0)` and shallow owned angle
theta, the physical projection is

\[
 \cos\theta(1+dx)+\sin\theta\,dy
 \le1+dx+2\eta|\theta|.                              \tag{7}
\]

We used `1+dx>0` to discard the favorable cosine loss. Combining
(5) and (7) proves

\[
 -dx+|\theta_j-\theta_i|/2
 \le(2+13/24)\eta U\le3\eta U.
\]

Consequently each of the two linear rows obtained by replacing the
absolute value by either signed difference has the upper bound in
(2). The identical argument after a coordinate swap proves the rows
of a vertical base contact `(0,1)`.

### 4.2. Upper contacts at horizontal offset one half

For the upward owned normal `(-sin theta,cos theta)` and base
difference `(sigma/2,1)`, the projection is at most

\[
 1+dy-\sigma\theta/2+2\eta|\theta|+|\theta|^3/12.
\]

Together with (5), this yields

\[
 -dy+\sigma\theta_{\rm owner}/2+
       |\theta_j-\theta_i|/2\le3\eta U.                \tag{8}
\]

For `sigma=+1`, the minimum of the last two angle terms over the two
owners is `max(theta_i,theta_j)/2`. For `sigma=-1`, it is
`-min(theta_i,theta_j)/2`. Thus (8) implies *both* linear owner rows
of the tangent system, each with upper bound `3eta U`. This is the
exact reason that those two rows may be imposed simultaneously even
though physical separation initially chooses only one owner.

### 4.3. The two diagonal C/D alternatives

For base difference `(1,1)`, the positive shallow owned projection is
at most

\[
 1+dx+\theta+2\eta|\theta|+|\theta|^3/6.
\]

Since `eta<=1/8`, the combined error with (5) is at most

\[
 \left(2+\frac\eta6+\frac{13}{24}\right)\eta U
 \le\frac{41}{16}\eta U\le3\eta U.                   \tag{9}
\]

Minimizing `|theta_C-theta_D|/2-theta_owner` over the two owners gives
`-(theta_C+theta_D)/2`. Hence the horizontal separator alternative
implies the necessary row

\[
                    -dx-(\theta_C+\theta_D)/2
                      \le3\eta U.                   \tag{10}
\]

The positive upward steep alternative gives in exactly the same way

\[
                    -dy+(\theta_C+\theta_D)/2
                      \le3\eta U.                   \tag{11}
\]

Keeping both alternatives as separate exhaustive cases is sufficient.
No choice between their possible owners is omitted.

## 5. Actual links, exact cones, and the exact weak row

Each of the four marked actual horizontal comparisons has base gap
one. Equation (4) therefore gives

\[
 -dx+(z_i+z_j)/2
 \le\left(\frac14+\frac\eta{12}\right)\eta U
 \le\frac12\eta U.                                    \tag{12}
\]

The original marked A/B and C/D cone faces are exact linear
inequalities in the center shifts. The sign cases for theta_C and
theta_D, their corresponding equalities `z=+theta` or `z=-theta`,
and the inequalities `+theta_i-z_i<=0`, `-theta_i-z_i<=0` are also
exact.

Finally the original strict C/D weak comparison and the upper bound
in (4) imply

\[
 1+dx<h_C+h_D\le1+(z_C+z_D)/2,
 \qquad dx-(z_C+z_D)/2<0.                            \tag{13}
\]

In particular its closed tangent row is valid with **zero** nonlinear
error. No Taylor estimate is needed for this decisive row.

## 6. Active original circle corners

The four active original corners belong to A,D,E,G, with respective
base offsets `(-1/2,-1/2)`, `(1/2,-1/2)`, `(-1/2,1/2)`, and
`(1/2,1/2)`. Let p be the corresponding base corner, w its offset,
and J the quarter-turn matrix. Then `|p|^2=Q=1105/256` and
`|w|=1/sqrt(2)`.

Write

\[
 R_\theta w=w+\theta Jw+E,
 \qquad |E|\le\theta^2|w|/2=\theta^2/(2\sqrt2).
\]

This integral remainder bound follows because the second derivative
of a rotating vector has constant norm `|w|`. The unchanged original
corner is `p+e+theta Jw+E`. Its containment gives

\[
\begin{aligned}
0&\ge|p+e+\theta Jw+E|^2-Q\\
 &=2p\cdot e+2p\cdot Jw\,\theta
   +2p\cdot E+|e+\theta Jw+E|^2.
\end{aligned}
\]

The final squared term is nonnegative and may be dropped in the
favorable direction. Therefore the tangent circle row satisfies

\[
 2p\cdot e+2p\cdot Jw\,\theta
 \le2|p||E|
 \le\sqrt{Q/2}\,\theta^2
 \le\frac32\eta|\theta|,                              \tag{14}
\]

because `Q/2=1105/512<9/4`. This proves the circle part of (2) without
introducing any error in the center shifts alone.

## 7. How exact tangent duals yield an explicit nonlinear terminal

Fix one of the eight cases consisting of the two C and D angle signs
and the horizontal or vertical C/D physical alternative. Suppose a
separate exact finite table gives, for each original i and each sign
epsilon, nonnegative rational multipliers satisfying the exact row
identity

\[
 \epsilon\theta_i=\sum_j\lambda_{i,\epsilon,j}L_j(w).
                                                               \tag{15}
\]

This identity must hold in all center, angle, and z variables; floating
cancellation or a bounded optimization outcome is insufficient.
Bounds belonging only to a numerical LP box cannot be used unless
separately derived as homogeneous physical rows.

Let `W_i=max_epsilon sum_j lambda_{i,epsilon,j}` for this case and
`K=3*sum_i W_i`. Equations (2) and (15) then imply

\[
 |\theta_i|\le3W_i\eta\Theta,\qquad
                         \Theta\le K\eta\Theta.      \tag{16}
\]

The row-specific constants in (2) may reduce K, but the displayed
uniform choice is already rigorous. Choose a rational radius delta
strictly below both `1/8` and `1/K` for every case. Any original
packing in the closed delta neighborhood must have `Theta=0`.

The final contradiction uses only the same original C/D pair. If C
and D are aligned, their physical nonoverlap requires `d>=1` or
`|v|>=1`. The original marked cone requires `d>=|v|`, whereas the
original strict weak bit requires `d<h_C+h_D=1`. These three
conditions are incompatible. Thus exact duals (15) and a finite
explicit delta complete an isolated-neighborhood terminal of the
strict original caller, even when aligned center motions remain
possible in the tangent relaxation.

This document proves the nonlinear lift. Acceptance of a particular
numerical radius still requires the separately complete exact
multiplier table and its exhaustive eight-case replay.

## 8. A sharper maximum-angle lift

There is a useful alternative to summing all nine angle bounds. Put
`Z=max_i|theta_i|`, so `0<=Z<=eta`. Every signed-angle dual can be
estimated directly in terms of `eta*Z`. The necessary row bounds are

\[
\begin{array}{c|c}
\text{row type}&\text{upper bound}\\\hline
\text{circle}&(3/2)\eta Z\\
\text{actual horizontal link}&(25/48)\eta Z\\
\text{physical contact}&(25/8)\eta Z\\
\text{absolute values, signs, cones, closed weak row}&0.
\end{array}                                                        \tag{17}
\]

To check the improved contact coefficient directly, the owned support
loss in (5) satisfies

\[
 \frac{\Delta^2}{4}+\frac{|\Delta|^3}{12}
 \le\left(1+\frac{2\eta}{3}\right)\eta Z,
\]

using both `|Delta|<=2eta` and `|Delta|<=2Z`. The largest owned
projection error among all contact types is the diagonal error,
bounded by `(2+eta/6)*eta*Z`. Therefore their combined error is at
most

\[
 \left(3+\frac{5\eta}{6}\right)\eta Z
 \le\frac{149}{48}\eta Z\le\frac{25}{8}\eta Z.       \tag{18}
\]

All zero-angle faces are included. The actual-link error in (12) is
at most

\[
 2\left(\frac14+\frac\eta{12}\right)\eta Z
 \le\frac{25}{48}\eta Z.                             \tag{19}
\]

The circle and exact rows already have the required bounds. Thus
(17) follows without any sum over unrelated original tilts.

Let `r_j` be the corresponding rational coefficient from (17), and
let the exact signed-angle duals include any needed rows `-z_i<=0`
explicitly, with zero error coefficient. If

\[
 K=\max_{\text{all eight cases},\ i,\ \epsilon}
             \sum_j\lambda_{i,\epsilon,j}r_j,
\]

then the dual for an original and sign attaining Z gives
`Z<=K*eta*Z`. Any rational delta strictly below both `1/8` and `1/K`
therefore forces every original angle to vanish. The direct original
C/D contradiction at the end of Section 7 applies unchanged. This
uses a maximum over the signed-angle dual costs, instead of their
sum, and can supply a substantially larger explicit neighborhood.

## 9. Both coordinates of the actual short middle original may be free

The same nonlinear terminal covers the continuous upward motion of
the aligned short middle original F. In fact neither center coordinate
of F needs to enter the local neighborhood norm. Redefine

\[
 \eta=\max\left\{
 |e_{ix}|,|e_{iy}|\ (i\ne F),\quad |\theta_i|\ (\text{all }i)
 \right\}\le1/8.                                     \tag{20}
\]

Retain both original actual E/F and F/G comparisons and the original
F/G cone. The actual comparisons and `h_i>=1/2` give

\[
 x_F\ge x_E+h_E+h_F\ge-\eta,
 \qquad
 x_F\le x_G-h_G-h_F\le\eta.                          \tag{21}
\]

Thus F's horizontal center shift has the same required bound,
derived from the original chains rather than assumed in the cylinder.
The marked F/G cone gives

\[
 y_F\ge y_G-(x_G-x_F)
       \ge-1/16-3\eta.                               \tag{22}
\]

Suppose `y_F<=y_H`. Then the original center differences satisfy

\[
 |x_F-x_H|\le1/2+2\eta,
 \qquad 0\le y_H-y_F\le4\eta.
\]

Their squared center distance would be at most

\[
 (1/2+2\eta)^2+(4\eta)^2
 \le(3/4)^2+(1/2)^2=13/16<1,
\]

contrary to the disjoint open radius-1/2 disks contained in the two
originals. Hence `y_F>y_H`. The identical argument gives `y_F>y_I`.
Containment of F gives `y_F<rho=91/60`, so both full upper-contact
vertical gaps obey

\[
 0<y_F-y_H<\rho+1/16+\eta<2,
 \qquad 0<y_F-y_I<2.                                 \tag{23}
\]

For either of these contacts, every shallow owned normal has
projection strictly below

\[
 1/2+2\eta+2\eta=1/2+4\eta\le1.
\]

The strict inequality follows from (23), including when `eta=1/8`.
The downward steep sign also cannot attain the support sum one:
its projection is at most `|sin(theta)|*|dx|<1`. Thus an upward steep
normal still owns the physical separation. In its projection formula
the entire full vertical gap multiplies `cos(theta)`. Because that
gap is positive, the cosine loss can again be discarded in the
favorable direction. The remaining errors involve only the bounded
horizontal difference increment and the original angle. They are
exactly the upper-contact estimates in Sections 4 and 8.

All other contact rows involve centers already controlled by (20).
The actual E/F and F/G rows involve only horizontal centers and angles;
(21) supplies their required horizontal bounds. No active circle row
uses F. Therefore every row estimate, and every exact signed-angle
dual identity, remains valid in this larger cylinder. The tangent
identities must cancel the two F center columns exactly, as they do
all center columns; no artificial numerical bound on F may be used.

The resulting neighborhood terminal constrains the eight centers
other than F and all nine original angles. It covers the entire
permitted F-height family and requires no additional F/C order
theorem or assumed F placement. The final aligned C/D contradiction
is unchanged.

## 10. The exact table gives the closed radius 1/64

The complete sharp tangent table supplies all 144 signed-angle
identities: two signs for each of nine original angles, in every one
of the eight C-sign/D-sign/diagonal-separator cases. Using exactly the
row error coefficients in (17), its largest dual cost is

\[
                         K=\frac{4234}{69}<64.         \tag{24}
\]

An independent Fraction audit reconstructed the 56 original homogeneous
rows directly from the base physical corners, contacts, actual links,
and cone faces, then checked all 144 identities including the
nonnegative multipliers of the exact rows `-z_i<=0`. It obtained the
same maximum (24), with no floating arithmetic and no numerical center
box row used in any identity. The stored discovery sign labels target
the negative signed angle; both signs are present, so this convention
does not change the maximum-angle argument.

For every original configuration in the closed cylinder

\[
 |e_{ix}|,|e_{iy}|\le1/64\quad(i\ne F),
 \qquad |\theta_i|\le1/64\quad(\text{all nine }i),    \tag{25}
\]

Sections 8--9 and the appropriate exact dual identity give

\[
 Z\le\frac{4234}{69}\frac1{64}Z
   =\frac{2117}{2208}Z,
 \qquad 1-\frac{2117}{2208}=\frac{91}{2208}>0.
\]

Thus Z=0 and in particular C,D are aligned. Their original strict
weak comparison, original marked cone, and original physical
nonoverlap contradict one another as proved in Section 7.

Consequently the full closed cylinder (25), with F's actual center
unrestricted except for the original packing and marked-chain
conditions, is excluded from the strict `001/00` caller. This includes
every zero-angle face and the continuous aligned F-height family.
The ordinary all-aligned packing remains a valid closed-weak control;
it is excluded here only by the unchanged original strict weak bit.

The separate final exact replayer, certificate, and independent review
bind the complete 144-identity table and its eight-case coverage.
The tangent optimization itself is not a premise of this nonlinear
conclusion.

### 10.1. Complete exact artifacts and independent acceptance

The final certificate is
`computer_assisted/weak_outer_deep_boundary_angle_certificate.json`.
The independent exact source
`computer_assisted/weak_outer_deep_boundary_verify.py` reconstructs
all 56 physical rows and appends the nine exact nonnegativity rows
`-z_i<=0`, giving 65 homogeneous rows in every case. It checks every
nonnegative rational multiplier, all 36 coefficients of each of the
144 identities, the complete eight-case and signed-target coverage,
the row-specific error cost, and the strict contraction (24).

The certificate SHA-256 is
`0a64c08f0e7845a4bf6aa5d5ce43bcb80167a847101b36f903d10554e53a290c`.
The exact replayer SHA-256 is
`08d913b7e9adc174e66e2225fe0a05e732cd6fa6fbacb794f39b23f61c6e2aef`.

The complete original replay is
`computer_assisted/weak_outer_deep_boundary_exact_replay.json`.
Fresh independent replays are
`computer_assisted/weak_outer_deep_boundary_global_independent_replay.json`
and `computer_assisted/weak_outer_hand_deep_boundary_independent_replay.json`.
All passed the same 144 exact identities and returned (24), radius
`1/64`, and contraction gap `91/2208`. The global reviewer also read
the entire nonlinear argument and the free-F-center cylinder extension;
its acceptance is recorded in
`GLOBAL_OUTER_LINK_EXTRACTION_DEEP_BOUNDARY_INDEPENDENT_REVIEW.md`.

All six damaged controls were rejected: a missing sign/separator
case, a missing signed angle, a repeated angle target, a negative
multiplier, a false exact identity, and a false nonlinear error cost.
Their source and report are
`computer_assisted/weak_outer_deep_boundary_controls.py` and
`computer_assisted/weak_outer_deep_boundary_rejection_controls.json`.

This is a complete local terminal of the unchanged strict original
caller. It does not assert that every original configuration is in
the cylinder or close an entire fixed mask by itself.
