# Exact center-free remainder with projected comparison sliders

This supplies the final analytic remainder estimate for the broad stationary
comparison graph. It assumes the independently certified coefficient premises
listed below. It does not use a center-neighborhood hypothesis, nor does it
infer the correct signed SAT owners from a neighborhood.

## 1. Hypotheses and frame convention

Let seven actual unit squares have all vertices in the centered disk of squared
radius q≤4. Their selected positively directed SAT witnesses are:

| Directed pair | Allowed actual owner normal | Reference normal |
|---|---|---|
| A→B | positive vertical axis of A or B | f₀ |
| T→B | positive horizontal axis of T or B | e₀ |
| D→T | positive horizontal axis of D or T | e₀ |
| E→D | positive vertical axis of E or D | f₀ |
| G→A | G's positive e-axis | eₜ |
| H→G | positive e-axis of H or G | eₜ |
| H→E | H's positive f-axis | fₜ |

Write e₀=(1,0), f₀=(0,1), eₜ=(cos t,sin t), and fₜ=(-sin t,cos t).
The canonical quarter-turn lifts have already been fixed. Set the actual
A frame to zero and choose the comparison tilt to be the actual G frame t.
Thus the frame errors are a_A=a_G=0; the other five errors are measured
relative to zero for B,T,D,E and relative to t for H.

The two rooted angle trees A–B–T–D–E and G–H give

\[
|a_i|\le S,
\quad
S=|\Delta_{AB}|+|\Delta_{TB}|+|\Delta_{DT}|
 +|\Delta_{ED}|+|\Delta_{HG}|\le10^{-4}.
\]

Assume 1/10≤t≤4/25. Let the exact stationary comparison at this same t have
anchored centers p_A⁰,p_B⁰,p_D⁰,p_E⁰,p_H⁰. Choose its free sliders by

\[
z_T=(p_T)_y,
\qquad
\eta=(p_G-p_H^0-e_t)\cdot f_t,
\]

and put

\[
p_T^0=(x_2-3/2,z_T),
\qquad p_G^0=p_H^0+e_t+\eta f_t.
\]

The capture interfaces prove z_T∈[29/50,7/5] and η∈[-1/2,37/100].
These intervals are hypotheses here. With d_i=p_i-p_i⁰, they imply the
**exact directional identities**

\[
d_T=\tau e_0,
\qquad d_G=\upsilon e_t
\tag{1}
\]

for real τ,υ. No component of any anchored displacement is constrained.

## 2. Certified reference premises

The broad coefficient audit supplies, throughout the stationary graph and
the complete comparison-slider rectangle:

- positive normalized disk weights μ_i on i∈{A,B,D,E,H}, with Σμ_i=1;
- positive edge weights λ_e<1, with Σλ_e<6;
- exact center-force balance, including λ_TB=λ_DT and λ_GA=λ_HG;
- zero reference gaps and reference dual value q_*+μ_H F(q_*,y(t),t);
- reference neighbor norms and selected reference-vertex norms less than2;
- first-order angular reserve at least (9/500)S for every one of the32 owner assignments;
- with b_i=2μ_i+Σ_(e incident to i)λ_e, the exact bound Σ_i b_i²/(2μ_i)<100.

Only the elementary slider displacement bounds |d_T|,|d_G|<8 are needed
below. They follow from q≤4 and the certified reference formulas, without
any center capture: every actual center has norm≤2, being the mean of four
vertices in the disk. For T, 0<x₂<2 and z_T≤7/5 give |p_T⁰|<3. For G,
|p_H⁰|<3 follows from its selected vertex norm<2 and corner-offset norm<1;
then |p_G⁰|<3+1+1/2=9/2. Consequently |d_T|<5 and |d_G|<13/2, which are
both below8. The broad audit also directly proves |p_T⁰|,|p_G⁰|<2, but
that stronger bound is unnecessary.

## 3. Exact dual decomposition

For a directed edge i→j with chosen actual unit normal n_e, let

\[
g_e=n_e\cdot(p_j-p_i)-h_i(n_e)-h_j(n_e)\ge0.
\]

Let o_i⁰ be the selected reference corner offset of an anchored square;
the corresponding actual offset is o_i=R(a_i)o_i⁰. Define

\[
\mathcal D=\sum_i\mu_i|p_i+o_i|^2-\sum_e\lambda_e g_e.
\]

Because every selected actual vertex lies in the disk, positivity and
normalization give q≥D. At the reference, D⁰=q_*+μ_H F. Expanding each
anchored disk square is exact:

\[
|P_i^0+d_i+(o_i-o_i^0)|^2
=|P_i^0|^2+2P_i^0\cdot d_i+|d_i|^2
 +2P_i^0\cdot(o_i-o_i^0)
 +2d_i\cdot(o_i-o_i^0)+|o_i-o_i^0|^2.
\]

The center-force equations cancel all terms linear in d_i against the
reference-normal parts of the separators. This cancellation is algebraic
and holds for arbitrary displacements. The remaining center-angle separator
terms are exactly

\[
-\lambda_e(n_e-n_e^0)\cdot(d_j-d_i).
\tag{2}
\]

In particular, no small-center estimate is required to obtain this formula.

## 4. Pure angular loss is at most12S²

For every vector v and real a,

\[
|R(a)v-v|\le |v||a|,
\qquad |R(a)v-v-aJv|\le\tfrac12|v|a^2.
\tag{3}
\]

The anchored disk terms, after subtracting their linear angular parts,
lose at most2S², since |P_i⁰|<2, |o_i⁰|<1 and Σμ_i=1. Their extra squared
offset changes are nonnegative. The seven reference-neighbor projection
terms lose at most6S², by |p_j⁰-p_i⁰|<2 and Σλ_e<6.

For an aligned pair its support sum is
(1+cos Δ+|sin Δ|)/2. For |Δ|≤1,

\[
\left|\frac{1+\cos\Delta+|\sin\Delta|}{2}
       -1-\frac{|\Delta|}{2}\right|
\le\frac{\Delta^2}{4}+\frac{|\Delta|^3}{12}
\le\frac{\Delta^2}{3}.
\]

The five weighted aligned support remainders therefore total at most2S².
The mixed G→A support sum is constant in the mismatch variables: the
actual A and G frames are exactly the comparison frames0 and t. For H→E,
the relative angle is t+a_H-a_E, which remains in (0,π/2) because
t∈[.10,.16] and |a_H-a_E|≤2S. On this interval the support second derivative
has magnitude at most1. Its weighted Taylor remainder is at most
(1/2)(2S)²=2S². These four contributions sum to12S².

This accounts for the true support widths, including their aligned cusps;
it is not a smooth approximation to a SAT disjunction.

## 5. Anchored center-angle terms cost at most100S² after absorption

Equation(3) bounds an anchored disk cross term by2μ_i|d_i|S. The anchored
parts of(2) are bounded byΣ_(e incident to i)λ_e|d_i|S. Hence

\[
\sum_i b_i|d_i|S
\le \frac12\sum_i\mu_i|d_i|^2
 +\left(\sum_i\frac{b_i^2}{2\mu_i}\right)S^2
\le\frac12\sum_i\mu_i|d_i|^2+100S^2.
\tag{4}
\]

This is Young's inequality for arbitrary d_i; no anchored displacement bound
is used or subsequently needed.

## 6. Projected slider terms cost at most16S²

The key elementary identity is

\[
(R(a)n-n)\cdot(\xi n)=\xi(\cos a-1),
\qquad
|(R(a)n-n)\cdot(\xi n)|\le\frac12|\xi|a^2
\tag{5}
\]

for every unit n. It has no first-order term because Jn is perpendicular
to n.

For T→B and D→T, both reference normals are e₀, and every allowed actual
normal is R(a)e₀ with |a|≤S. Equation(1) lets(5) apply to each appearance
of d_T in(2). Regardless of the incidence signs and owner choices, their
combined magnitude is at most

\[
\frac{\lambda_{TB}+\lambda_{DT}}2|d_T|S^2<8S^2.
\]

For G→A the chosen normal is G's own axis eₜ. As G defines the comparison
tilt, **n_GA=n_GA⁰ exactly**, so this edge has zero center-angle term for G.
For H→G the allowed normal is either eₜ or R(a_H)eₜ. Equation(1) again
makes(5) apply. In particular the same uniform two-incidence estimate is
valid:

\[
\frac{\lambda_{GA}+\lambda_{HG}}2|d_G|S^2<8S^2.
\]

It deliberately overestimates the zero G→A contribution. The slider terms
therefore cost at most16S² in total. The opposite signs with which an endpoint
occurs in the two directed edges are irrelevant to these absolute bounds.
There is no missing G-frame rotation: the comparison is made at the actual
G frame, held fixed throughout this mismatch expansion.

## 7. Completed inequality

Add the exact first-order angular reserve, the positive five-center quadratic
terms, and the losses from Sections4–6. Equations(2)–(5) give

\[
\boxed{
q\ge\mathcal D\ge q_*+\mu_HF(q_*,y(t),t)
 +\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2
 +\left(\frac9{500}-128S\right)S.
}
\]

At S≤1/10000,

\[
\frac9{500}-128S\ge\frac9{500}-\frac{128}{10000}
=\frac{13}{2500}>0.
\]

The stationary-family conclusion F(q_*,y(t),t)≥0 therefore yields q≥q_*.
This is a fully nonlinear bound for arbitrary anchored center positions
and all32 captured signed-owner branches. The only capture hypotheses
remaining in this statement are the named frames/owners, small mismatch,
common tilt interval and two actual projected-slider coordinates.
