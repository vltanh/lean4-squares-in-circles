# Independent audit of the quantitative slider tube

This checks the analytic interpretation of
[verify_quantitative_slider_tube.py](verify_quantitative_slider_tube.py), including the actual
SAT-owner coverage and the constants in the nonlinear remainder. It also checks the written [quantitative terminal theorem](HUMAN_QUANTITATIVE_SLIDER_TUBE.md). It does
not assert the separate global capture into this tube.

## 1. Chart and finite arithmetic

The checker applies outward rational interval arithmetic over the entire
existing candidate q-box, the y interval of radius1/500, and the
half-angle-tangent z interval of radius1/2000. The displayed derivatives of
the five-corner chain are correct. In particular

\[
x_4'=-y_4y_4'/x_4,\qquad
x_4''=-q(y_4')^2/x_4^3-y_4y_4''/x_4,
\]

including the negative sign of x4. The formulas for F_y,F_yy,F_yt follow
by direct differentiation of h1²+h2²−q. Opposite endpoint signs and F_yy>7
give the unique stationary y(t) throughout the common-tilt chart. The
implicit derivative is −F_yt/F_yy. The H and G derivative vectors are
written in the rotating e,f frame, so their Euclidean norm is unchanged.

The four slider corners suffice for every comparison: squared neighbor
distance and each wrong unsigned gap are convex in the two slider
coordinates, while each angular reserve λ/2−|C| is concave. All root/chart
variables remain enclosed by intervals during each corner comparison.
The 32 choices are the two genuine endpoint owners on each of five
aligned edges. The two mixed edges have only their one permitted owner.

## 2. Completeness of the actual owner selection

Fix A's actual frame as zero and G's actual frame as the common tilt t.
The five edge differences form the trees A--B--T--D--E and G--H. If their
total absolute sum is S, every non-root frame perturbation has absolute
value at most S. Every relative perturbation used on a neighboring edge
also has magnitude at most S; for HE the two tree paths are disjoint
subsets of the five edges. GA has no relative perturbation at all.

Suppose each center differs from its pseudo reference by at most P. For
an actual candidate axis owned by either endpoint, its unsigned projection
changes by at most

\[
2P+|n-n^0|\,|p_j^0-p_i^0|\le2P+2S.
\]

The owning square contributes the constant half-width1/2. The other
square's half-width is 1/2-Lipschitz in relative angle, so its change is at
most S/2. Therefore every wrong-axis gap changes by at most2P+5S/2,
which is bounded by the checker's conservative2P+3S. At P=1/1000 and
S=1/10000 this is below1/400. Thus all wrong axes remain invalid.
The reference directed positive projections are at least1, and their
change is below2P+2S; their sign remains positive. These comparisons
exclude both the wrong unsigned axes and reversed signs. The remaining
owners are exactly the 32 branches enumerated in the checker.

## 3. Explicit remainder audit

Write the weighted expression as the sum of five squared actual vertex
norms minus the seven weighted directed SAT gaps. Let u_i be a center
error and ε_i its frame perturbation; |ε_i|≤S. Exact force balance at the
stationary pseudo-chain cancels all purely linear center terms.

For a rotation Rε, use

\[
\|R_\varepsilon-I\|\le|\varepsilon|,
\qquad
\|R_\varepsilon-I-\varepsilon J\|\le\varepsilon^2/2.
\]

The pure angular remainders admit the following bounds.

| Contribution | Bound | Reason |
|---|---:|---|
| Five disk vertices |2S²| Expand about the selected reference vertex P_i^0, whose norm is below2; retain the nonnegative offset-change square; Σμ=1. |
| Seven normal projections |6S²| Every reference neighbor displacement has norm<2 and Σλ<6. |
| Five aligned support widths |2S²| Each loss is at most Δ²/3 and the sum of their weights is below6. |
| Mixed HE support width |2S²| Its second derivative has magnitude below1; a relative-angle change at most2S suffices. GA is constant. |

For an aligned pair,

\[
\frac{\cos\Delta+|\sin\Delta|-1}{2}
\ge\frac{|\Delta|}{2}
-\frac{\Delta^2}{4}-\frac{|\Delta|^3}{12}
\ge\frac{|\Delta|}{2}-\frac{\Delta^2}{2}
\]

when |Δ|≤S≤1/10000. The sharper aligned loss Δ²/3 follows from |Δ|≤1. The HE width is smooth throughout the stated tilt chart, and its second derivative has magnitude below1. GA has no angular change because A and G define the comparison frames. This proves the written table's total12S² bound without an unspecified Taylor constant. Expanding the disk terms about the reference center instead would give the alternative valid split3S²+6S²+3S².

The disk center/angle cross term is bounded by2μ_i S|u_i|. The separator
cross terms contribute each incident λ_e S|u_i|. Hence for each of the
five anchored centers the coefficient is exactly bounded by

\[
b_i=2\mu_i+\sum_{e\ni i}\lambda_e.
\]

Young's inequality gives

\[
b_iS|u_i|\le\frac{\mu_i}{2}|u_i|^2+
\frac{b_i^2}{2\mu_i}S^2.
\]

The checker proves the sum of the latter coefficients is below100.
T and G have no disk weight; each has two incident weights below1, so
their combined cross term is at most4PS. No term proportional to their
center errors alone remains, because both reference slider forces cancel.

Combining these bounds with the verified angular reserve9/500 yields

\[
\mathcal D-\mathcal D^0\ge
\frac12\sum_{i=A,B,D,E,H}\mu_i|u_i|^2+
\left(\frac9{500}-112S-4P\right)S.
\]

At P≤1/1000 and S≤1/10000, the final coefficient is at least7/2500>0.
The exact reference value q*+μ_H F(q*,y(t),t) and the earlier sharp-family
inequality F≥0 then give local sharpness. The force identities and F≥0
are explicit existing analytic inputs; small interval residuals are not
used as substitutes for either of them.

**Conclusion:** the owner enumeration and mixed remainder constants are
sound. The proposed quantitative curved tube is a valid local terminal
once the existing family/force inputs are invoked and a complete global
capture supplies its pose, frame, labeling, and slider-component hypotheses.

## 4. Executed finite check

The exact checker was independently run after the final chart condition tan(t)<1/5 was added. It passed every stated comparison, including the seven pseudo-center derivative norm bounds. Its interval outputs include minimum angular reserve greater than0.018210033830, largest wrong-gap upper endpoint below−0.002906395074, and Young coefficient sum below83.374650108721. The rational thresholds, not rounded output decimals, are the proof premises.
