# Broad stationary comparison graph, transverse coordinate, and curvature

The exact stationary comparison needed by every captured boundary word exists
throughout the common tilt interval `1/10<=t<=4/25`. Its transverse coordinate
satisfies `-29/20<h2<-7/5`, and its reduced defect F is nonnegative with a
strict minimum at the isolated candidate. These statements are now separately
certified from the owner-coefficient part of the local dual.

## 1. Algebraic comparison coordinates

Fix q at the exact isolated candidate q*. Write `z=tan(t/2)`,
`c=(1-z^2)/(1+z^2)`, and `s=2z/(1+z^2)`. The five-corner chain coordinates
are

\[
\begin{aligned}
x_1&=\sqrt{q-y^2},&x_2&=\sqrt{q-(y+2)^2},&x_3&=x_2-3,\\
y_3&=\sqrt{q-x_3^2},&y_4&=y_3-2,&x_4&=-\sqrt{q-y_4^2},\\
h_1&=cx_1+sy-2-c,&h_2&=-sx_4+cy_4-1-s,\\
F(q,y,t)&=h_1^2+h_2^2-q.
\end{aligned}
\]

All radicands and nonzero denominators used below are enclosed by the exact
interval calculation, so these functions are analytic on its entire domain.
The already isolated candidate satisfies `F=Fy=Ft=0`.

## 2. Exact stationary graph on a larger rational chart

Use the exact rational root centers from the candidate isolating certificate,

\[
y_c=-0.92065667800760613175,\qquad
z_c=0.06189741100766035970.
\]

Consider the closed rational z chart and its affine corridor

\[
\frac1{20}\le z\le\frac{81}{1000},\qquad
\left|y-y_c-\frac54(z-z_c)\right|\le\frac1{2000}.
\]

The script `verify_broad_stationary_h2.py` divides this z interval into512
closed equal cells. On each entire cell, using the full q isolating interval,
it proves

\[
F_y\left(q,y_c+\frac54(z-z_c)-\frac1{2000},t\right)<0,
\]

\[
F_y\left(q,y_c+\frac54(z-z_c)+\frac1{2000},t\right)>0,
\qquad F_{yy}>7
\]

throughout the corridor. The interval substitution encloses the correlated
sloping boundaries safely; treating their y and z ranges independently only
enlarges the checked sets.

For each fixed z, the intermediate value theorem and strict y monotonicity
give one and only one root of `Fy=0` in the corridor. The implicit function
theorem makes this root analytic locally. At shared cell endpoints uniqueness
identifies the neighboring roots, so these local graphs form a single
stationary comparison `y(t)` throughout the chart.

The candidate isolating y,z box lies strictly inside the same corridor.
Its exact `Fy=0` equation therefore identifies it with this graph at t*.
This proves branch identification without an appeal to floating optimization.

The rational chart contains every captured tilt: `atan(1/20)<1/20`, while

\[
\arctan(81/1000)\ge81/1000-(81/1000)^3/3>2/25.
\]

Thus every `1/10<=t<=4/25` has `z=tan(t/2)` inside the chart.

## 3. Exact transverse-coordinate bound

The same512-cell computation proves on the entire corridor

\[
\boxed{-\frac{29}{20}<h_2(q,y,t)<-\frac75.}
\]

The outward interval displayed in decimals is approximately
`[-1.444172550628,-1.407817935418]`; the proof uses its scaled integer
endpoints and the stated rational outer bounds. In particular the inequality
holds on the unique stationary graph at q*.

This is the h2 premise used in all terminal projected-slider formulas.
For a core G, `eta=-13/12-h2` lies in `(19/60,11/30)`. For an outer G whose
captured longitudinal coordinate lies in `(27/20,7/5)`,
`eta=-aG-h2-1/2` lies in `(-1/2,-2/5)`. Both are inside the broad local
comparison interval `[-1/2,37/100]`.

The complete output is `broad_stationary_h2_audit.json`. Independent code and
logical review, followed by a full replay, passed; its separate output is
`audit_capture/broad_stationary_h2_independent_replay.json`.

## 4. Strictly positive reduced curvature

At fixed y the trigonometric coordinates satisfy the exact identities

\[
h_{1,tt}=-h_1-2,\qquad h_{2,tt}=-h_2-1.
\]

Consequently

\[
F_{tt}=2\bigl(h_{1,t}^2+h_{2,t}^2-h_1(h_1+2)-h_2(h_2+1)\bigr).
\]

The separate script `verify_broad_reduced_curvature.py` uses the same closed
cell cover and proves throughout its corridor

\[
\boxed{F_{tt}-\frac{F_{yt}^2}{F_{yy}}>1.}
\]

Its outward enclosure is approximately `[1.334793102163,1.483255941497]`.
No rounding estimate is used as an assumption: the exact scaled lower bound
is compared directly with the rational1.

Let `G(t)=F(q*,y(t),t)` on the stationary graph. Since `Fy=0`, implicit
differentiation gives

\[
y'(t)=-\frac{F_{yt}}{F_{yy}},\qquad
G'(t)=F_t,\qquad
G''(t)=F_{tt}-\frac{F_{yt}^2}{F_{yy}}>1.
\]

At the exact candidate, `G(t*)=G'(t*)=0`. Integrating the strict curvature
bound on either side gives

\[
\boxed{F(q_*,y(t),t)\ge\frac12(t-t_*)^2\ge0.}
\]

This proves the reduced-family inequality on the whole broad chart.
An independent512-cell recomputation matches every exact curvature row;
its report is `audit_capture/broad_stationary_curvature_independent_audit.json`.
The owner and center-deviation terms of the local dual are separate; this
certificate supplies their nonnegative F term and the shared slider bound.
