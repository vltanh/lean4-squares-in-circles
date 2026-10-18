# Independent audit of the broad center-free sharpness theorem

All analytic and finite arithmetic premises of the broad terminal theorem
have now been checked. Together with the completed domain covers, they
supply the sharp contradiction for a seven-exterior representative of any
alleged eight-square packing below the exact candidate radius.

This audit uses the already established exact candidate root
(q*,y*,t*) and its isolating interval. It does not replace the independent
construction showing that eight squares attain q*.

## 1. Precise terminal hypotheses

Use the named order A,B,T,D,E,H,G. Normalize A's actual frame to zero and
take G's actual frame to be t, where

\[
1/10\le t\le4/25.
\]

Choose continuous representatives for the remaining frames. Set

\[
S=|\theta_A-\theta_B|+|\theta_T-\theta_B|
 +|\theta_D-\theta_T|+|\theta_E-\theta_D|
 +|\theta_H-\theta_G|\le1/10000.
\]

The seven directed actual SAT gaps are AB,TB,DT,ED,GA,HG,HE. Their
comparison normals are respectively f0,e0,e0,f0,e_t,e_t,f_t. On each of
the five aligned pairs, either endpoint may own the actual normal. G owns
GA and H owns HE. The normal on an actual pair is the indicated direction
rotated with its actual owner frame. Every one of the32 owner choices is
allowed and has been checked.

Choose the comparison sliders from actual transverse projections:

\[
z_T=(p_T)_y,\qquad
\eta=(p_G-p_H^0-e_t)\cdot f_t.
\]

The captured states satisfy

\[
z_T\in[29/50,7/5],\qquad \eta\in[-1/2,37/100].
\]

No proximity assumption on any of the seven centers is used. If the
container has squared radius at least4, the desired lower bound is already
immediate; in proving the nontrivial case assume R²<4.

## 2. The broad stationary comparison is rigorously defined

Put z=tan(t/2). The captured tilt interval lies strictly inside
z in[1/20,81/1000]. The512 closed interval cells in
`global_attack/verify_broad_stationary_h2.py` prove opposite signs of Fy on
the two sides of the affine corridor

\[
\left|y-y_c-\frac54(z-z_c)\right|\le1/2000,
\]

and Fyy>7 throughout. Therefore each vertical section contains one
stationary point, and the implicit-function theorem gives a real analytic
stationary graph. Adjacent cells share closed endpoints and the same
corridor, so their unique roots agree. The isolating box of the exact
candidate lies strictly within the corridor at z*; this identifies the
graph with the candidate branch.

The same exact computation proves

\[
-29/20<h_2<-7/5.
\]

The independent full replay is
`broad_stationary_h2_independent_replay.json`. This discharges the
previously external h2 premise in all three word-specific slider audits.

There is also a direct broad-chart proof of the reference defect. Since
h1tt=−h1−2 and h2tt=−h2−1,

\[
F_{tt}=2\bigl(h_{1t}^2+h_{2t}^2-h_1(h_1+2)-h_2(h_2+1)\bigr).
\]

On Fy=0, the reduced function M(t)=F(q*,y(t),t) satisfies

\[
M''=F_{tt}-F_{yt}^2/F_{yy}>1.
\]

All512 exact curvature rows were independently recomputed and agree with
`global_attack/broad_reduced_curvature_audit.json`. The report is
`broad_stationary_curvature_independent_audit.json`. Since the exact root
has M(t*)=M'(t*)=0, integration gives

\[
M(t)\ge\tfrac12(t-t_*)^2\ge0.
\tag{1}
\]

This proves both broad reference nonnegativity and uniqueness of its zero,
without relying on numerical convexity evidence.

## 3. Complete dual coefficient and norm audit

`verify_broad_dual_coefficients_independently.py` uses the same512 proved
stationary-corridor cells, the full q* isolating interval, four corners of
the expanded slider rectangle, and all32 owner assignments. The angular
coefficients are affine in the two sliders. Thus their absolute values
are convex, and the four corner comparisons suffice on the whole
rectangle. Neighbor and slider squared norms are convex for the same
reason. All remaining variables are enclosed throughout each full cell.

Its exact report is `broad_dual_coefficients_independent_audit.json`.
The327680 owner coefficient comparisons prove

\[
\lambda_e/2-|C_e|>9/500
\]

for every aligned edge, owner assignment and admissible comparison.
The smallest outward lower bound exceeds0.02021162098. The following
additional strict inequalities hold throughout the chart:

| Quantity | Proved bound |
|---|---|
| Five vertex weights |1/50<mu_i<1, with exact sum1|
| Seven separator weights |0<lambda_e<1, with sum<6|
| Young coefficient sum |sum b_i²/(2mu_i)<100|
| Each reference neighbor displacement |norm<2|
| Both reference slider centers |norm<2|
| All five selected reference vertices |norm<2|
| Common tilt |0<tan(t)<1/5|

The outward upper bound for the Young sum is below93.580020735.
The exact identities defining the positive weights and their force balance
are the previously audited adaptive-dual formulas, evaluated on Fy=0.

## 4. Weighted expression and the full nonlinear remainder

Let v_i be the selected actual vertex of anchored square i and let g_e be
the nonnegative actual signed gap on a selected pair. Define

\[
\mathcal D=\sum_{i=A,B,D,E,H}\mu_i|v_i|^2
           -\sum_e\lambda_e g_e.
\]

True containment and the positive weights give D<=R². Write
d_i=p_i−p_i^0 and let epsilon_i be each frame error from its comparison
frame. The two rooted frame trees imply |epsilon_i|<=S. Reference force
balance cancels every linear center term, including those at the two
zero-weight sliders. The constant term is q*+mu_H M(t).

For a rotation, use

\[
\|R_\epsilon-I\|\le|\epsilon|,\qquad
\|R_\epsilon-I-\epsilon J\|\le\epsilon^2/2.
\]

The pure angular loss is bounded by12S²:2S² from the five disk vertices,
6S² from the seven reference normal projections,2S² from the five
aligned widths, and2S² from the smooth HE width. GA has no angular
variation because A and G define the comparison frames. The aligned
estimate follows directly from

\[
\frac{\cos d+\sin|d|-1}{2}
\ge\frac{|d|}{2}-\frac{d^2}{3},\qquad |d|\le1.
\]

The smooth HE width stays in one open quadrant throughout the chart;
its absolute second derivative is below1. Its relative frame perturbation
is bounded by2S, which suffices for the stated loss.

At each anchored center, the disk/angle and separator/angle cross terms
are bounded by b_i|d_i|S, where

\[
b_i=2\mu_i+\sum_{e\ni i}\lambda_e.
\]

Young's inequality absorbs these terms into

\[
\frac12\sum_i\mu_i|d_i|^2+100S^2.
\]

The crucial slider terms are also quadratic. By the definition of the
comparison sliders, d_T is parallel to e0 and d_G is parallel to e_t.
Each incident reference normal has that same parallel direction. Hence

\[
d_i\cdot(R_\epsilon n^0-n^0)
=(d_i\cdot n^0)(\cos\epsilon-1).
\]

There is no term linear in epsilon here. Both actual and comparison slider
centers have norm below2, so |d_T|,|d_G|<4; even the weaker bound8 gives
at most16S² across all four incidences, using lambda_e<1. It is unnecessary
to control either slider center by a small proximity radius.

The complete lower estimate is therefore

\[
\mathcal D\ge q_*+\mu_H M(t)
 +\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2
 +(9/500-128S)S.
\tag{2}
\]

For S<=1/10000,

\[
9/500-128S\ge13/2500>0.
\]

Combining(1),(2) and D<=R² proves the broad terminal lower bound R²>=q*.
It covers weak contacts, owner ties, every slider endpoint and S=0.

## 5. Sharp global contradiction and equality information

The complete123-case boundary capture and the four exact angle/owner
budgets prove every terminal hypothesis above after expansion to Qsharp.
The monotonic outer-radius theorem transfers the owners and angles back to
the original reduced ring. The projected slider audits include this transfer
and hold on the entire lower-radius interval. Thus the terminal inequality
is applied before expansion, at qtilde=max(q,q0)<q*, contradicting
qtilde>=q*. No approximate radius is substituted for the exact target.

Within the terminal theorem, equality forces S=0, all five anchored center
errors to vanish, and t=t*. If one fixes a genuine signed SAT witness for
every adjacent edge before the radial-boundary deformation, each selected
gap is nondecreasing throughout that deformation. At equality the positive
dual weights force every final gap to be zero, so every original gap and
every increment was zero. The five anchored labels have two nonparallel
incident normals and therefore cannot move; T and G can move only in their
respective slider directions. This is a rigorous equality pullback for the
seven exterior squares. The feasible freedoms of the eighth central square
are a separate description of the attaining configurations, not a premise
of the sharp lower-bound proof.
