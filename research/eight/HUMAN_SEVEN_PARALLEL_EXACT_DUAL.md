# Exact seven-square zero-tilt fiber: one rational SOS lower-bound certificate

**2026-10-13. Complete exact hand theorem**, including a genuine
seven-square attaining packing. This is a *fixed-frame regression
certificate* for the new global angle-fiber dual framework in
[GLOBAL_SAT_ANGLE_FIBER_DUALITY.md](GLOBAL_SAT_ANGLE_FIBER_DUALITY.md).
It is not the unrestricted eight-square lower bound.

## Theorem: a global-in-centers strict support-gap identity

Let seven genuine **axis-parallel** unit squares
A,B,T,D,E,H,G (no assumptions on their centers)
be in the centered disk \(D_R\).
Assume the seven *directed true-square* separators
\[
\begin{array}{rcl}
g_{AB}&=&(p_B-p_A)_y-1\ge0,\\
g_{TB}&=&(p_B-p_T)_x-1\ge0,\\
g_{DT}&=&(p_T-p_D)_x-1\ge0,\\
g_{ED}&=&(p_D-p_E)_y-1\ge0,\\
g_{GA}&=&(p_A-p_G)_x-1\ge0,\\
g_{HG}&=&(p_G-p_H)_x-1\ge0,\\
g_{HE}&=&(p_E-p_H)_y-1\ge0 .
\end{array}                                                    \tag{1}
\]
No exact contact (gap zero) is required.
No other square-pair relation is required for the lower bound.

Define the rational reference centers
\[
\begin{aligned}
p_A^0&=(29/24,-1/2),&
p_B^0&=(29/24,1/2),\\
p_D^0&=(-19/24,1),&
p_H^0&=(-19/24,-1).
\end{aligned}
\]
Let \(q_0=2257/576\).
Then **every** choice of actual seven square centers
with these frames satisfies the exact quantified inequality
\[
\boxed{
\begin{aligned}
R^2\ge{}&q_0
 +\frac{31}{144}\Big(|p_A-p_A^0|^2+
                      |p_B-p_B^0|^2\Big)\\
&+\frac{41}{144}\Big(|p_D-p_D^0|^2+
                      |p_H-p_H^0|^2\Big)\\
&+\frac{31}{72}g_{AB}
 +\frac{1271}{1728}(g_{TB}+g_{DT}+g_{GA}+g_{HG})\\
&+\frac{41}{48}(g_{ED}+g_{HE}).
\end{aligned}}                                                 \tag{2}
\]
All coefficients on the right are **strictly positive**.

In particular if the seven directed separators hold,
\[
\boxed{R^2\ge2257/576>19/5.}
\]
This bound is **sharp for that fixed-angle,
seven-directed-separator class**: a genuine packing
of seven unit squares with all 28 square pairs disjoint
attains radius exactly \(\sqrt{2257/576}\).

## Exact hand proof of the SOS identity

Take the four **actual** square vertices
\[
\begin{aligned}
v_A&=p_A+(1/2,-1/2),&
v_B&=p_B+(1/2,1/2),\\
v_D&=p_D+(-1/2,1/2),&
v_H&=p_H+(-1/2,-1/2).
\end{aligned}
\]
Each is a true unit-square vertex and lies in \(D_R\).
Give them the positive rational weights
\[
\mu_A=\mu_B=\frac{31}{144},\qquad
\mu_D=\mu_H=\frac{41}{144},
\qquad\sum_i\mu_i=1.
\]
Consequently
\[
R^2\ge
\frac{31}{144}(|v_A|^2+|v_B|^2)
+\frac{41}{144}(|v_D|^2+|v_H|^2).              \tag{3}
\]

At the rational reference centers these four vertices are
\[
(41/24,-1),\quad(41/24,1),\quad
(-31/24,3/2),\quad(-31/24,-3/2).
\]
Each has squared norm **exactly**
\[
(41/24)^2+1=(31/24)^2+(3/2)^2
=\frac{2257}{576}=q_0.
\tag{4}
\]

Assign the seven genuine directed separator-gap weights
in the order of (1):
\[
\boxed{
\lambda_{AB}=\frac{31}{72},\quad
\lambda_{TB}=\lambda_{DT}=
\lambda_{GA}=\lambda_{HG}
=\frac{1271}{1728},\quad
\lambda_{ED}=\lambda_{HE}=\frac{41}{48}.}     \tag{5}
\]

These are the **exact force-stationary dual
multipliers**: at the four circle-anchored
labels A,B,D,H the oriented incidence sum
of edge normals is the negative of
\(2\mu_i v_i^0\). At unanchored T,E,G,
the incident positive edge normals cancel
exactly. The nontrivial common x multiplier is
\[
\frac{1271}{1728}
=2\frac{31}{144}\frac{41}{24}
=2\frac{41}{144}\frac{31}{24}.
\]
The y multipliers similarly are
\(2(31/144)(1)=31/72\) and
\(2(41/144)(3/2)=41/48\).

Expand the weighted vertex sum in (3)
around these four reference points:
\[
\begin{aligned}
\sum_i\mu_i|v_i|^2
&=q_0+\sum_i\mu_i|p_i-p_i^0|^2
 +\sum_i2\mu_i v_i^0\cdot(p_i-p_i^0)\\
&=q_0+\sum_i\mu_i|p_i-p_i^0|^2
 +\sum_e\lambda_e g_e .
\end{aligned}
\]
The last line uses the exact oriented incidence
force balance, together with
\(g_e(p^0)=0\) for all seven edges.
No unsigned-gap substitution is made:
each \(g_e\) is the genuine **DIRECTED
separating projection** specified in (1).

Combine this identity with (3).
It is exactly (2), proving the theorem. QED.

## Attainment by seven actual unit squares

All seven squares are axis parallel. Use the four
reference centers above and choose the other three as
\[
p_T=(5/24,5/4),\qquad
p_E=(-7/5,0),\qquad
p_G=(5/24,-1).
\]
All seven genuine directed gaps in (1) are exactly
zero; the four selected vertices attain squared
radius q0; every other true vertex is no farther
from zero.

For nonoverlap, each of the **21 distinct square pairs**
has center difference with
\[
|\Delta x|\ge1\quad\text{or}\quad|\Delta y|\ge1.
\]
That is a genuine axis-owned SAT separator.
Thus the open square interiors are pairwise disjoint.
The disk constraints are satisfied by all 28
actual vertices, and four attain radius
\(\sqrt{q_0}\).

The independent exact symbolic checker
[verify_seven_parallel_exact_dual.py](verify_seven_parallel_exact_dual.py)
expands the **entire polynomial SOS identity in
the arbitrary seven center variables**, not sampled
points, and checks all 21 pairwise genuine SAT
nonoverlap and all 28 vertex inequalities of
the attaining construction.

## What this contributes to the still-open global problem

The five-corner family already includes a zero-tilt
aligned special case, so the value \(q_0\) is
**not** an improvement to the unrestricted
lower bound \(\sqrt{19/5}<R_8\le\widehat R\).

The new contribution is a **complete explicit
strictly positive dual**: circle weights, edge
support weights, center-squares, and projected
separation slacks are all visible as rational
terms in one formula. It is a rigorous
regression certificate for any future
disk-native global **angle+SAT-owner**
interval prover, and demonstrates how
fixed-angle center variables can be
eliminated rather than interval-branched.

To close n=8 one must certify every relevant
orientation/owner fiber, or find a valid
unconditional sharp geometry inequality
that bypasses this combinatorial cover.
Neither exists yet. Lean formalization is open.
