# An explicit sharpness tube around the full two-slider comparison family

This makes the neighborhood in
[HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md](HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md)
quantitative. It gives a precise terminal condition for a global cover.
The conclusion uses the seven adjacent true SAT disjunctions and the
actual disk constraints; it allows every square frame to vary independently.

**Status:** the terminal theorem below is proved. A complete global capture
into its hypotheses remains a separate open gate. The finite rational
coefficient audit is explicit; it uses the existing exact candidate root
enclosure, rather than proving that enclosure afresh.

## 1. Exact reference chart and terminal hypotheses

Let \((q_*,y_*,t_*)\) be the unique stationary solution selected by
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md). Use the exact decimal
rationals

\[
q_c=3.91553413751747532652,\quad
y_c=-0.92065667800760613175,\quad
z_c=0.06189741100766035970.
\]

The existing candidate enclosure gives
\(|q_*-q_c|,|y_*-y_c|,|\tan(t_*/2)-z_c|\le10^{-16}\).
In this note the comparison tilt ranges over the whole closed interval

\[
\boxed{|z-z_c|\le1/2000,\qquad z=\tan(t/2).}
\tag{1}
\]

There is a unique real analytic stationary position \(y(t)\) in
\([y_c-1/500,y_c+1/500]\) satisfying
\(F_y(q_*,y(t),t)=0\). Section 2 verifies its existence on the entire
chart, including both endpoints. Define the five pseudo-centers
\(p_A^0,p_B^0,p_D^0,p_E^0,p_H^0\) and the positive normalized adaptive
weights \(\mu_i(t),\lambda_e(t)\) exactly as in
[HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md](HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md).
The other two comparison centers are

\[
p_T^0=(x_2-3/2,z_T),\qquad
p_G^0=p_H^0+e_t+\eta f_t,
\]

where \(e_t=(\cos t,\sin t)\), \(f_t=(-\sin t,\cos t)\), and

\[
\boxed{7/12\le z_T\le11/8,\qquad -9/20\le\eta\le7/20.}
\tag{2}
\]

These are comparison centers. They need not themselves constitute a
feasible packing at every parameter in (1)--(2).

**Quantitative terminal theorem.** Let seven actual unit squares
\(A,B,T,D,E,H,G\) have disjoint open interiors on the seven pairs

\[
AB,\ TB,\ DT,\ ED,\ GA,\ HG,\ HE
\tag{3}
\]

and have all vertices in a disk centered at the origin, of radius \(R\).
After a simultaneous rotation, choose continuous square-frame
representatives with \(\theta_A=0\), \(\theta_G=t\), and (1). Define

\[
\begin{aligned}
\Delta_{AB}&=\theta_A-\theta_B,&
\Delta_{TB}&=\theta_T-\theta_B,&
\Delta_{DT}&=\theta_D-\theta_T,\\
\Delta_{ED}&=\theta_E-\theta_D,&
\Delta_{HG}&=\theta_H-\theta_G,&
S&=\sum_{\sigma\in\{AB,TB,DT,ED,HG\}}|\Delta_\sigma|.
\end{aligned}
\]

Suppose that for some comparison sliders in (2),

\[
\boxed{S\le1/10000,\qquad
|p_i-p_i^0(t;z_T,\eta)|\le1/1000\quad\hbox{for every label }i.}
\tag{4}
\]

Then, writing \(d_i=p_i-p_i^0\),

\[
\boxed{
R^2\ge q_*+\mu_H(t)F(q_*,y(t),t)
+\frac12\sum_{i=A,B,D,E,H}\mu_i(t)|d_i|^2
+\frac7{2500}S\ge q_*.
}
\tag{5}
\]

All quantities in the hypotheses are explicit. The center bound is a
Euclidean bound relative to the same comparison pose; it is not seven
independent choices of common tilt or skeleton position. No condition is
imposed on nonneighbor pairs. Those pairs may overlap in this relaxation.

## 2. The complete finite arithmetic premises

The checker
[verify_quantitative_slider_tube.py](verify_quantitative_slider_tube.py)
uses outward rational interval arithmetic from the existing adaptive
audit, on the single product box

\[
q\in[q_c-10^{-16},q_c+10^{-16}],\quad
y\in[y_c-1/500,y_c+1/500],\quad
z\in[z_c-1/2000,z_c+1/2000].
\tag{6}
\]

Here \(c=(1-z^2)/(1+z^2)\), \(s=2z/(1+z^2)\), so no trigonometric
rounding enters the coefficient audit. All nested radicals have positive
arguments. The following strict bounds pass on their whole stated domains.

| Quantity | Exact proved bound |
|---|---|
| \(F_y\) at \(y=y_c-1/500\), for the whole q,z box | \(<-3/500\) |
| \(F_y\) at \(y=y_c+1/500\), for the whole q,z box | \(>3/500\) |
| \(F_{yy}\), throughout (6) | \(>7\) |
| \(|F_{yt}|\), throughout (6) | \(<5\) |
| Tilt throughout (1) | \(1/10<t<\arctan(1/5)\) |
| Every distinct wrong reference SAT gap, throughout (2),(6) | \(<-1/400\) |
| Every aligned-edge angular reserve, for every true owner assignment | \(\lambda_\sigma/2-|C_{\sigma,\mathrm{owner}}|>9/500\) |
| The five normalized circle weights | \(\mu_i>1/50\), with \(\sum\mu_i=1\) identically |
| The seven contact weights | \(0<\lambda_e<1\), \(\sum\lambda_e<6\) |
| Every one of the seven reference neighbor distances | \(|p_j^0-p_i^0|<2\) |
| All five reference selected-vertex norms | \(|P_i^0|<2\) |
| Anchored-center Young coefficient, defined in section 5 | \(\sum_i b_i^2/(2\mu_i)<100\) |

The endpoint signs and \(F_{yy}>7\) give a unique zero of \(F_y\) for
each tilt, by the intermediate-value theorem and strict monotonicity.
The implicit-function theorem gives the analytic function \(y(t)\),
and \(|y'(t)|<5/7\). The chart lies inside the strip of the hand family
theorem. Its position is the unique position minimum there, so that

\[
F(q_*,y(t),t)\ge0,
\tag{7}
\]

with equality only at \(t=t_*\).

The gap and angular bounds are continuous-slider statements, not sampled
claims. At fixed q,y,z, each wrong unsigned gap is convex in the two
sliders, and each reserve is concave in them. Their respective maxima
and minima are therefore bounded at the four corners of (2). The audit
checks all 44 distinct wrong-gap corner comparisons and all
\(32\cdot4\cdot5=640\) angular-reserve comparisons, with (6) retained as
an interval. These are exactly the owner formulas in the uniform-slider
note. The weakest resulting reserve is greater than 0.0182100, and the
largest wrong-gap upper bound is less than -0.0029063; these decimals
describe the output, while the fractions in the table are the proof inputs.

The separate uniform-slider audit proves that the full candidate-compatible
radial endpoint intervals at \(t_*\) lie inside (2). The present theorem
does not assert that every unrelated pseudo-chain throughout the enlarged
product box (6) has those same radial endpoint ranges.

## 3. All actual owner alternatives are covered at the stated tolerance

Put \(a_i=\theta_i\) for A,B,T,D,E, and
\(a_H=\theta_H-t\), \(a_G=\theta_G-t=0\). The two rooted angle trees
A--B--T--D--E and G--H give \(|a_i|\le S\) for every label.

For any actual SAT axis, its owner's half-width is exactly 1/2. The
other half-width is
\((|\cos u|+|\sin u|)/2\), a globally 1/2-Lipschitz function of the
relative frame angle u. Rotating the owner by at most S changes the
projection of a reference neighbor vector of norm less than 2 by at
most \(2S\). Moving both centers by at most P changes the same projection
by at most \(2P\). The relative angle changes by at most \(2S\).
Consequently every wrong unsigned gap increases by at most

\[
2P+3S\le2/1000+3/10000=23/10000<1/400.
\tag{8}
\]

The 11 distinct reference wrong-axis formulas include coincident axes
of both owners on aligned edges. Bound (8) applies separately to each
actual owner as those axes split. Thus all 16 actual wrong axes remain
strictly infeasible. The reference positive projection on every correct
axis is at least 1; its actual value stays at least
\(1-2P-2S>0\). Reversing that direction cannot give a separator.

Nonoverlap and the true square SAT therefore force the five aligned
pairs AB,TB,DT,ED,HG to choose their positively directed correct axis
from either endpoint. GA must choose G's positive e-axis, and HE must
choose H's positive f-axis. These are all \(2^5=32\) owner branches.

## 4. The exact dual and its first-order terms

For the selected actual owner normals \(n_e\), write

\[
g_e=n_e\cdot(p_j-p_i)-h_i(n_e)-h_j(n_e)\ge0.
\]

Use the five actual vertices corresponding to the reference corners
of A,B,D,E,H, with their offsets rotated by the actual owner frame.
Positive weights and \(\sum\mu_i=1\) give

\[
R^2\ge\mathcal D
:=\sum_{i=A,B,D,E,H}\mu_i|p_i+o_i(\theta_i)|^2
-\sum_e\lambda_e g_e.
\tag{9}
\]

Every reference gap vanishes. Its reference dual value is
\(\mathcal D^0=q_*+\mu_HF\). All center-linear terms cancel exactly:
the adaptive five-center force equations use \(F_y=0\), while
\(\lambda_{TB}=\lambda_{DT}\) and
\(\lambda_{GA}=\lambda_{HG}\) cancel the slider forces.

For any owner choice, the first-order angular part is

\[
\sum_{\sigma\in\{AB,TB,DT,ED,HG\}}
\left(\frac{\lambda_\sigma}{2}|\Delta_\sigma|
+C_{\sigma,\mathrm{owner}}\Delta_\sigma\right)
\ge\frac9{500}S.
\tag{10}
\]

The coefficients are obtained by differentiating (9) and substituting
the two rooted angle trees, exactly as in the genuine SAT-local proof.
The audit evaluates every coefficient on every branch. Fixing the
actual G frame as t is essential: no uncontrolled common tilt remains
among the five mismatch variables.

## 5. Explicit nonlinear remainder

Let P bound every \(|d_i|\). The elementary rotation estimates

\[
|R(a)v-v|\le|v||a|,\qquad
|R(a)v-v-aJv|\le |v|a^2/2
\tag{11}
\]

give the following bounds after the center-linear and angular-linear
terms have been removed. All square corner offsets have norm less than 1.

**Pure angular remainder.** The five disk terms lose at most \(2S^2\):
use \(|P_i^0|<2\), (11), and \(\sum\mu_i=1\); the additional squared
offset-change term is nonnegative. The seven separator-normal terms
lose at most \(6S^2\), since each reference edge has norm less than 2
and \(\sum\lambda_e<6\).

For an aligned edge, the true total support width is
\((1+\cos\Delta+|\sin\Delta|)/2\). Its error after the constant and
\(|\Delta|/2\) terms is at most \(\Delta^2/3\) for \(|\Delta|\le1\).
All five such remainders together are bounded by \(2S^2\). The mixed
GA support width is constant, since A and G define the comparison
frames. For HE the angle stays in the same open quadrant by (1),(4).
The absolute second derivative of its total width is less than 1,
and its relative-angle deviation is at most \(2S\); its remainder is
at most \(2S^2\). The complete pure angular loss is therefore at most

\[
12S^2.
\tag{12}
\]

**Center-angle remainder.** The disk cross term at an anchored center
is at most \(2\mu_i|d_i|S\). A separator contributes at most
\(\lambda_e S(|d_i|+|d_j|)\). Set

\[
b_i=2\mu_i+\sum_{e\text{ incident to }i}\lambda_e,
\quad i\in\{A,B,D,E,H\}.
\]

Young's inequality and the audited coefficient sum yield

\[
\sum_i b_i|d_i|S
\le\frac12\sum_i\mu_i|d_i|^2
+\left(\sum_i\frac{b_i^2}{2\mu_i}\right)S^2
\le\frac12\sum_i\mu_i|d_i|^2+100S^2.
\tag{13}
\]

Each slider has two incident weights less than 1. Their remaining
cross terms are at most \(4PS\). No square-center penalty is claimed
for T or G.

Combining (9)--(13) proves the explicit bound

\[
\mathcal D\ge q_*+\mu_HF
+\frac12\sum_i\mu_i|d_i|^2
+\left(\frac9{500}-112S-4P\right)S.
\tag{14}
\]

At the terminal tolerances,

\[
\frac9{500}-\frac{112}{10000}-\frac4{1000}
=\frac7{2500}>0.
\]

Equations (7),(9),(14) prove (5). The estimates cover weak contacts,
zero mismatch, shared owner ties, and every endpoint of (1),(2),(4).

## 6. Equality and the remaining global interface

Within this tube, equality in the radius bound forces \(S=0\), all
five anchored center deviations to vanish, and \(F=0\). The family
theorem then forces \(t=t_*\). The two sliders retain their actual
geometric freedoms. This is a local equality statement for the seven
selected pairs; it does not classify all eight-square equality packings.

A global capture must prove the labeling, the chart (1), the mismatch
bound, the common five-center comparison, and the slider components.
For capture performed at a rational ceiling just above \(q_*\), use
[OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md](OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md)
to transfer back to the hypothetical smaller disk. For example, a
captured center error at most 0.00099 leaves sufficient reserve for that
transfer into the present 0.001 tube.

As an optional capture aid, the checker also verifies that every
pseudo-center derivative with respect to t has norm less than 8 on
(1), at fixed comparison sliders. This permits explicit transfer
between nearby comparison tilts; it does not itself prove capture.

Run the exact arithmetic premises from this directory:

```sh
python3 verify_quantitative_slider_tube.py
```

The proof of (5) is the analytic estimate above together with the stated
finite arithmetic premises and existing family/root theorems. A
successful checker invocation alone is not a proof of global optimality.
