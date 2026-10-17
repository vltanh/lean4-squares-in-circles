# Uniform local sharpness over both complete candidate slider ranges

This extends [HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md](HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md)
from one selected slider pose to a neighborhood of a compact two-parameter
family. It repairs a specific interface needed by the radial-boundary
reduction: either slider can end on the core or outer boundary, far from
the slider values used in the previous local theorem.

The proof uses only the seven adjacent true SAT conditions. Nonneighbor
overlaps are permitted, so the conclusion applies to the actual
adjacent-pair relaxation used in the global boundary cover. **The global
capture into this neighborhood is still a separate open theorem.**

## 1. Reference family and statement

Use the exact unique sharp stationary solution \((q_*,y_*,t_*)\) and
the five circle-contact centers \(p_A^*,p_B^*,p_D^*,p_E^*,p_H^*\) in
the existing adaptive-dual proof. Its notation has

\[
c=\cos t_*,\quad s=\sin t_*,\quad e=(c,s),\quad f=(-s,c),
\quad x_T=x_2-3/2.
\]

Keep the five standard frames of A, B, T, D, E at zero and the frames
of H, G at \(t_*\). Define

\[
p_T^*=(x_T,z_T),\qquad p_G^*=p_H^*+e+\eta f,
\]

and let \(K\) be the compact reference pose family with

\[
\boxed{7/12\le z_T\le11/8,\qquad -9/20\le\eta\le7/20.}
\tag{1}
\]

Every nominal separator of the seven-pair cycle is tight throughout
\(K\). Some members may violate extra nonneighbor or disk constraints;
they are comparison poses for the dual, not asserted eight-square packings.

**Theorem.** There is an open neighborhood \(\mathcal U\) of the whole
compact family \(K\), up to simultaneous rotation, such that any
seven genuine unit squares in \(\mathcal U\), contained in a disk
of radius \(R\), and with disjoint open interiors on the seven pairs

\[
AB,\ TB,\ DT,\ ED,\ GA,\ HG,\ HE,
\]

satisfy \(R^2\ge q_*\). Every square frame is independently variable.
No exact contact is required of the actual squares.

As in the previous local theorem, equality forces the five anchored
centers and the two orientation clusters to be the sharp ones. The
two slider positions are subject to their remaining actual geometric
constraints; this local theorem does not classify global eight-square
equality configurations.

## 2. Both radial endpoints are included

For the candidate-compatible component, T lies above the origin and G
has negative second coordinate in its tilted frame. At the exact
five-circle skeleton, write

\[
a_G=h_1+3/2,\qquad b_G=h_2+1/2.
\]

The exact candidate bounds give \(0<x_T<1/2\),
\(0<a_G<1/2\), and \(b_G<0\). Hence disk containment and avoidance
of the open radius-\(1/12\) core restrict the sliders to

\[
\begin{aligned}
7/12\le z_T&\le\sqrt{q_*-(x_T+1/2)^2}-1/2,\\
-\sqrt{q_*-(a_G+1/2)^2}+1/2-b_G
\le\eta&\le-7/12-b_G.
\end{aligned}
\tag{2}
\]

These are the full intervals in those respective components, because
the farthest vertex and the distance to the core have exactly the
displayed coordinate formulas. Cyclic-order capture must still select
these components; the present theorem does not silently identify a
distant component with the candidate one.

The exact rational interval check in
[verify_uniform_slider_local_dual.py](verify_uniform_slider_local_dual.py)
proves that (2) lies inside (1). For orientation only, its endpoint
enclosures are approximately

\[
z_T^{\max}=1.365995639804,\quad
\eta_{\rm outer}=-0.445049688478,\quad
\eta_{\rm core}=0.346653610109.
\]

Thus the theorem includes all four choices of moving T and G to their
respective outer or core boundaries. They yield the candidate-bearing
representatives of `OOOOOOO`, `COOOOOO`, and `COOCOOO`.

## 3. Uniform actual SAT-owner selection

The nominal positive separator directions are

\[
b,\ a,\ a,\ b,\ e,\ e,\ f
\]

in the displayed seven-pair order. The five same-frame edges allow
either endpoint to own the indicated axis. The mixed GA and HE edges
must be owned by G and H respectively. There are 32 owner assignments.

The 11 wrong unsigned axis gaps are those listed in the previous local
proof. For fixed sharp root data, each such gap is an absolute value
of an affine function of \((z_T,\eta)\), minus a constant support
width. It is therefore convex on the rectangle (1). Its maximum is
bounded by the maximum at the four rectangle corners: express any
point as a convex combination of the four corners and apply convexity.

The exact checker proves all 44 corner comparisons

\[
\boxed{g_{\rm wrong}<-1/125.}
\tag{3}
\]

The largest corner gap is enclosed near \(-0.009085787004\), strictly
below \(-0.008\). This uniformly selects the same true SAT owner
families on all of \(K\). The nominal positive projected gaps have
the correct sign throughout \(K\), independently of the sliders.
Compactness and continuity preserve (3) and these signs in a common
open neighborhood of \(K\).

## 4. Uniform angular coercivity on all owner assignments

Use the same positive adaptive weights \(\mu_i(t),\lambda_e(t)\)
and pseudo five-circle skeleton with \(F_y(q_*,y(t),t)=0\). The weights
do not depend on either slider. The five aligned-edge transverse
reference displacements are now

\[
Y_{AB}=x_1-x_2,\quad
Y_{TB}=p_B.y-z_T,\quad
Y_{DT}=z_T-p_D.y,\quad
Y_{ED}=x_4-x_3,\quad
Y_{HG}=\eta.
\tag{4}
\]

For the mixed edges,

\[
Y_{GA}=f\cdot(p_A-p_G),\qquad
Y_{HE}=-e\cdot(p_E-p_H).
\]

These enter the smooth angular coefficients exactly as in equations
(8)–(9) of the previous local proof. For any fixed owner assignment,
every resulting coefficient \(C_\sigma\) is affine in the sliders.
Consequently each reserve \(\lambda_\sigma/2-|C_\sigma|\) is concave
on (1), and its minimum is bounded below by the least corner value.

The exact checker covers every one of the 32 owner assignments, all
four corners, and all five aligned-edge coefficients: 640 comparisons.
It proves

\[
\boxed{\lambda_\sigma/2-|C_{\sigma,\rm owner}|>1/40}
\tag{5}
\]

uniformly on the entire slider rectangle. The smallest enclosure is
near \(0.027368029227\); no sampled interior slider value is used to
infer (5). By compactness, the strict margin persists for all nearby
common tilts t, using the analytic pseudo-chain and its adaptive weights.

These finite arithmetic checks use the previously certified exact
candidate root box and outward rational interval arithmetic from
`verify_adaptive_seven_square_dual.py`. They establish the strict
coefficient premises over that whole box. Root existence, identification
with the unique family minimum, and exact force balance are the existing
proof inputs; a small numerical residual does not substitute for them.

## 5. One nonlinear neighborhood for the whole rectangle

Choose the actual A frame as zero and the actual G frame as the nearby
tilt t. For each nearby pose select \((z_T,\eta)\) in the compact
rectangle and compare with its corresponding pseudo reference at t.
The five anchored reference centers depend only on t; the other two
are the freely chosen reference slider centers. Let

\[
S=|\Delta_{AB}|+|\Delta_{TB}|+|\Delta_{DT}|+
  |\Delta_{ED}|+|\Delta_{HG}|.
\]

The exact weighted disk-minus-separator expression is the same as in
the prior proof. All seven center forces vanish at every such reference:
the five anchored forces cancel by \(F_y=0\), while the equal opposing
edge weights cancel the T and G forces. The reference value is

\[
q_*+\mu_H(t)F(q_*,y(t),t),
\]

independently of both sliders.

Taylor expansion on the finitely many signed angular sectors and
owner branches gives a uniform constant \(K_0<\infty\) such that

\[
\begin{aligned}
\mathcal D-\mathcal D^0\ge{}
&\sum_{i=A,B,D,E,H}\mu_i|\delta p_i|^2+\frac1{40}S\\
&-K_0\left[S^2+S\sum_{i=A,B,D,E,H}|\delta p_i|
               +S(|\delta p_T|+|\delta p_G|)\right].
\end{aligned}
\tag{6}
\]

Uniformity follows because the slider rectangle is compact, the tilt
interval can be chosen compact inside the analytic chart, and there
are only finitely many branches. The derivative formulas are smooth
there apart from the explicit absolute-sine cusps already accounted
for in (5). The uniform lower bound for all five circle weights is
strictly positive.

Take a sufficiently small tube around the whole reference family.
Then the slider *deviations from their selected reference positions*,
not the slider ranges themselves, are small. Young's inequality
absorbs the five anchored center-angle cross terms into half of the
positive squared-center terms. Shrinking the tube once more bounds
all remaining error by \(S/80\). Hence

\[
R^2\ge\mathcal D\ge
q_*+\mu_H(t)F(q_*,y(t),t)
+\frac12\sum_{i=A,B,D,E,H}\mu_i|\delta p_i|^2
+\frac1{80}S.
\tag{7}
\]

The existing sharp family theorem gives \(F(q_*,y(t),t)\ge0\).
Equation (7) proves the announced uniform local bound. This is a
nonlinear local theorem with genuine SAT owners, not merely a
nonnegative first variation.

## 6. Exact remaining global interface

A global boundary-cycle capture may terminate in this neighborhood
even when T or G is at its core or outer endpoint. It must still prove
that the five anchored centers, independent frame angles, cyclic
labeling, and the correct slider components enter the stated tube.
This theorem supplies neither that global covering statement nor an
explicit numerical tube radius. A computational capture must also
make the neighborhood size quantitative before claiming that a
specific terminal box lies inside it.

Run the finite arithmetic audit from this directory:

```sh
python3 verify_uniform_slider_local_dual.py
```

All 44 wrong-axis and 640 owner-coefficient comparisons passed with
exact rational interval arithmetic. The full-domain statements in
sections 3–5 are the convexity, concavity, compactness, and Taylor
arguments above; finite corner testing alone would not supply them.
