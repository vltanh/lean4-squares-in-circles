# Genuine SAT-local sharpness of the seven-square ring with independently rotated frames

**2026-10-13. COMPLETE HAND-PROVED LOCAL SHARPNESS,
for actual nonoverlapping unit squares, all frames free.**

This is a strict strengthening of
[HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md](HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md)
and removes its assumption that the **fixed** seven
candidate-directed normal projections happen to be valid.
Here the normal separating each specified pair is
**whatever actual side of either square owns that SAT separator**.

The key ingredients are:
1. a **positive five-circle/seven-contact adaptive dual**
   that depends on the common tilted-frame angle;
2. a **finite actual SAT owner classification** near the
   exact sharp reference packing (11 wrong axes have strict
   negative margins);
3. a strictly positive **angular-mismatch dual on all
   32 owner assignments** for the five aligned-frame
   contact edges;
4. a full nonlinear Taylor/Young argument that absorbs
   position-angle cross terms with the five positive
   squared-center weights;
5. the previously hand-proved five-corner family
   inequality \(F(q_*,y,t)\ge0\) at the sharp radius.

**This does NOT prove the unrestricted eight-square bound**:
a global packing/minimizer outside the local reference
neighborhood need not have this seven-square contact
topology or these approximate center/frame positions.
It proves an honest **local isolation of radius decreases**,
with no forced parallelism or exact contacts.

## Theorem: real seven-square local minimum, no frame constraints

Let \(S_*=(A_*,B_*,T_*,D_*,E_*,H_*,G_*)\)
be the seven genuine *outer* unit squares in the
exact attaining construction
[ANALYTIC_EXACT_CONSTRUCTION.md](ANALYTIC_EXACT_CONSTRUCTION.md),
with the particular reference slider values
\[
p_{T_*}.y=27/20,\qquad p_{G_*}=p_{H_*}+e_{t_*}.
\]
Take the exact sharp squared radius \(q_*=\widehat R^2\).

**Theorem.** There is an open neighborhood \(\mathcal U\)
of this **seven-square pose** (in the space of all
seven centers and seven independent true square-frame
angles) such that:

> Every configuration of seven genuine unit squares
> with pairwise disjoint open interiors, whose poses
> belong to \(\mathcal U\) up to simultaneous rigid
> rotation, and whose 28 true vertices lie in a disk
> of radius R, satisfies
> \[
> \boxed{R\ge\widehat R.}                          \tag{1}
> \]
>
> The seven frames need not be parallel in either
> candidate orientation cluster, and NO exact
> square-square contact is assumed.

In particular the full **eight-square** construction
has an open pose neighborhood in which there is
**no strictly smaller-radius packing of eight unit
squares**: simply discard the central eighth
square and apply the seven-square result.

This is LOCAL sharpness only. It says nothing about
other global minimizers or equality packings at
distant pose configurations.

### Quantitative support statement underlying the theorem

In a suitable smaller pose neighborhood, after rotating
the actual frame of square A to standard \(a,b\) and
letting \(t\) equal the actual tilted frame angle of G,
there is a positive continuous function \(\mu_H(t)\)
and constants \(\kappa>0\), \(c_0>0\) such that
\[
\boxed{
R^2\ge q_*+\mu_H(t)F(q_*,y(t),t)
+c_0\!\!\sum_{i=A,B,D,E,H}\!\!
   |p_i-p_i^0(t)|^2
+\kappa\!\sum_{\sigma\in\{AB,TB,DT,ED,HG\}}\!
   |\theta_{\sigma,\mathrm{from}}
        -\theta_{\sigma,\mathrm{to}}|.
}                                                   \tag{2}
\]
For the tilted HG pair, the angles are measured in
the same local physical orientation chart; for the
five standard-cluster labels angles use the fixed
A frame. The pseudo reference centers \(p_i^0(t)\)
are defined in the adaptive-dual note.
There is **no center square at T/G in (2)**:
the actual exact sharp ring has genuine
T and G one-dimensional slider freedoms.

One can take the angular coefficient \(\kappa=1/80\)
after shrinking the open neighborhood sufficiently.
The constant \(c_0>0\) depends continuously on
the smallest of the five positive circle weights.

## 1. Genuine SAT owner selection has a strict reference margin

The seven directed candidate pairs are
\[
AB,\ TB,\ DT,\ ED,\ GA,\ HG,\ HE,
\]
with their nominal corresponding true
normal families
\[
b,\quad a,\quad a,\quad b,\quad
e_{t_*},\quad e_{t_*},\quad f_{t_*}.
\]

At the sharp exact reference, each pair's **directed
actual support gap in that nominal normal is zero**.

There are exactly four unoriented actual square-side
SAT axes per pair, two owned by each square.
For the four standard-cluster pairs
AB,TB,DT,ED the correct nominal axis
is owned by either end square, while the
perpendicular owner axes are wrong.
For the tilted pair HG its correct
axis is owned by either H or G.
For the two mixed-frame pairs GA and HE,
the correct direction is owned by
**G** and **H**, respectively; the
other square's two own side axes
are wrong, as is the perpendicular
tilted side axis.

The exact candidate-root interval audit
[verify_sat_seven_local_dual.py](verify_sat_seven_local_dual.py)
checks **all 11 wrong true SAT axes**,
not samples, and proves their corresponding
unsigned projected support gaps satisfy
\[
\boxed{g_{\rm wrong}<-\frac1{20}.}             \tag{3}
\]
The closest wrong axis is the A-owned
horizontal axis for the mixed GA pair,
with exact-root interval near
\(-0.05224860546\).
The HE E-owned vertical wrong gap is
near \(-0.07334865128\).

By continuity of the true support functions,
all those wrong axes remain impossible
throughout some open pose neighborhood.
Nonoverlap of any pair supplies at least
one ACTUAL SAT-owner axis with weak
nonnegative gap. The wrong axes cannot
serve, and the sign-reversed directions
cannot serve because the directed nominal
center projections stay strictly positive.

Thus **every genuine seven-square packing**
in this neighborhood forces precisely:
* AB,TB,DT,ED: either corresponding
  positively directed square-owned axis;
* GA: G's positively directed \(e_G\)-axis;
* HG: H's or G's positively directed e-axis;
* HE: H's positively directed \(f_H\)-axis.

This gives **32**, not infinitely many,
actual directed owner branches:
\[
2^5=32
\]
choices for AB, TB, DT, ED, HG.
No frame is assumed parallel: the owner
normals rotate with their actual square frames.

## 2. Adaptive dual and a reference with no radius descent

Use the **exact positive dual weights**
\(\mu_i(t),\lambda_e(t)>0\) and the
stationary pseudo-chain \(p_i^0(t)\) from
[HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md](HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md),
at fixed \(q_*\) and the analytic
\(y(t)\) satisfying \(F_y(q_*,y(t),t)=0\).
These weights have
\[
\sum_{i=A,B,D,E,H}\mu_i=1,\quad
\lambda_{TB}=\lambda_{DT},\quad
\lambda_{GA}=\lambda_{HG},
\]
and precisely balance each pseudo
reference center's outgoing-minus-incoming
contact normals.

For ANY one of the 32 actual SAT owner
choices, let \(n_e\) be the selected
rotating true square side normal and
\[
g_e=n_e\cdot(p_j-p_i)-h_i(n_e)-h_j(n_e)\ge0
\]
its genuine nonnegative directed SAT gap.
The weighted disk/separator inequality is
\[
\begin{aligned}
R^2&\ge
\sum_{i=A,B,D,E,H}\mu_i |p_i+o_i(\theta_i)|^2
-\sum_{\text{seven edges}}\lambda_e g_e\\
&=:\mathcal D_{\rm owner}(p,\boldsymbol\theta,t).
\end{aligned}                                                \tag{4}
\]
The vertices \(p_i+o_i(\theta_i)\) are
actual genuine square corners, not
pseudo circle points.

At aligned reference angle clusters and
pseudo reference centers, all seven
chosen SAT gaps vanish and the
five squared circle vertex norms are
\(q_*,q_*,q_*,q_*,q_*+F(q_*,y(t),t)\).
Thus for **all 32 owner branches**,
\[
\mathcal D_{\rm owner}(p^0(t),\theta^0(t),t)
=\boxed{q_*+\mu_H(t)F(q_*,y(t),t).}           \tag{5}
\]
This may correspond to a fictitious reference H
outside the disk; it is only a dual comparison
point, not a claimed packing.

## 3. Positive five-edge mismatch dual on all 32 SAT choices

Rotate all actual poses together so that A's
actual square frame is the standard \(a,b\).
Let **t be G's actual tilted frame angle**.
In the neighborhood, the remaining five
independent angular degrees of freedom
are precisely the differences
\[
\begin{array}{ll}
\Delta_{AB}=\theta_A-\theta_B,&
\Delta_{TB}=\theta_T-\theta_B,\\
\Delta_{DT}=\theta_D-\theta_T,&
\Delta_{ED}=\theta_E-\theta_D,\\
\Delta_{HG}=\theta_H-\theta_G.&
\end{array}                                                \tag{6}
\]
Their graph is two anchored trees:
A--B--T--D--E, rooted at
\(\theta_A=0\), and H--G, rooted
at \(\theta_G=t\).
Every other small angle deviation is
a sum of at most four differences in (6).
There is no extra unexplained
*common angular gauge* left in this comparison.

At t=t* and the exact candidate pseudo-center
positions, differentiating (4) within any
fixed SAT-owner branch gives
\[
\boxed{
\mathcal D_{\rm owner}
=\mathcal D_{\rm owner}^0+
\sum_{i=A,B,D,E,H}\mu_i|\delta p_i|^2
+\sum_{\sigma\in\{AB,TB,DT,ED,HG\}}
 \left(\frac{\lambda_\sigma}{2}
       |\Delta_\sigma|
       +C_{\sigma,\mathrm{owner}}\Delta_\sigma
 \right)
+\mathcal R.}                                      \tag{7}
\]
The remainder \(\mathcal R\)
contains only terms quadratic or
higher in position/angle deviations;
its uniform estimate is given
in the next section.

**The exact coefficients are NOT guessed.**
For each of the five aligned-frame
edges, its true candidate transverse
center displacement is
\[
Y_\sigma=(Jn_\sigma)\cdot(p_j^0-p_i^0).
\]
The exact root has
\[
\begin{array}{c|rrrrr}
\sigma&AB&TB&DT&ED&HG\\\hline
Y_\sigma\text{ (approx.)}
&0.0930705732&-0.7706566780&
0.3954020590&-0.5606015515&0.
\end{array}
\]
Changing the true SAT owner axis from
the first square of an edge to the second
changes its smooth angular coefficient
by \(\lambda_\sigma Y_\sigma\).
That is the only owner dependence.

For transparency, let
\(L_A,L_B,L_T,L_D,L_E,L_H,L_G\)
be the signed smooth angular coefficients
from the five disk-corner terms
and the two *mixed* GA/HE edges
before the five aligned-edge normal
derivatives are added.
They are explicitly:
\[
\begin{aligned}
L_A&=\mu_A(x_1+y)-W(c-s)/2,\\
L_B&=\mu_B(y+2-x_2),& L_T&=0,\\
L_D&=-\mu_D(x_3+y_3),\\
L_E&=\mu_E(x_4-y_4)-\lambda_{HE}(c-s)/2,\\
L_H&=\mu_H(h_1-h_2)+
 \lambda_{HE}\big((c-s)/2-Y_{HE}\big),\\
L_G&=W\big((c-s)/2-Y_{GA}\big).
\end{aligned}                                                   \tag{8}
\]
The mixed transverse values are
\(Y_{GA}=f_t\cdot(p_A^0-p_G^0)\),
\(Y_{HE}=-e_t\cdot(p_E^0-p_H^0)\).

For each chosen owner assignment,
subtract \(\lambda_\sigma Y_\sigma\)
from L at its owner vertex, obtaining v.
Because the root angular variables
A,G are **fixed** (A=0,G=t),
the edge coefficients in (7) are
the exact tree back-substitution:
\[
\begin{aligned}
C_{ED}&=v_E,\\
C_{DT}&=v_D+C_{ED},\\
C_{TB}&=v_T+C_{DT},\\
C_{AB}&=-v_B-C_{TB},\\
C_{HG}&=v_H.                                     \tag{9}
\end{aligned}
\]

The complete candidate-root **rational interval
certificate** in
[verify_sat_seven_local_dual.py](verify_sat_seven_local_dual.py)
checks **every one of the 32 owner choices** and proves
the uniform positive coercivity
\[
\boxed{
\frac{\lambda_\sigma}{2}
-|C_{\sigma,\mathrm{owner}}|>\frac1{40}
\quad\text{for every edge and owner choice}.}    \tag{10}
\]

The five smallest actual reserves over
both owner choices are, respectively,
\[
\begin{array}{c|ccccc}
\sigma&AB&TB&DT&ED&HG\\\hline
\text{smallest angular reserve (approx.)}&
.04685757&.04685757&.12138739&.02736803&.31363402
\end{array}
\]
The tightest reserve occurs on ED,
and is **strictly larger than \(1/40\)**.

Since the weights, pseudo-centers and
coefficients depend continuously on t
through the analytic y(t), inequality
(10) remains valid on a smaller
open t-neighborhood about t*.

## 4. Promote the first-order margin to a FULL nonlinear local inequality

This step is important: **a first-order LP
certificate alone is not a local sharpness theorem.**

Fix any of the 32 owner branches and
t in the sufficiently small interval.
Let \(\delta p_i=p_i-p_i^0(t)\)
for all seven square centers, including
the slider centers T,G, and put
\[
S=\sum_{\sigma\in\{AB,TB,DT,ED,HG\}}
   |\Delta_\sigma|.
\]
At the reference angular clusters
all seven true separator support
functions are continuous and
piecewise smooth. The only
nondifferentiabilities are the
aligned-pair terms
\(|\sin\Delta_\sigma|\), whose
first-order coefficient is exactly
\(\lambda_\sigma/2>0\).
The mixed GA/HE support functions
are smooth because the candidate
tilt \(0<t_*<\pi/4\) is strict.

Apply Taylor's theorem on each of
the finitely many signed angular
sectors for the **actual**
owner-dependent scalar expression
(4). Its center variables appear
quadratically only in the five
positive disk terms, and linearly
in the actual separator projections.
The exact force equations of the
pseudo reference cancel *every
purely linear* center term.
Therefore there is a common
finite constant \(K>0\) (uniform
over all 32 owner branches and
nearby t) such that
\[
\begin{aligned}
\mathcal D_{\rm owner}-\mathcal D_{\rm owner}^0
\ge&\sum_{i=A,B,D,E,H}\mu_i|\delta p_i|^2\\
&+\frac1{40}S
-K\left(S^2+S\sum_{i=A,B,D,E,H}|\delta p_i|
 +S(|\delta p_T|+|\delta p_G|)\right).
\end{aligned}                                                \tag{11}
\]
All terms in this estimate are explicit
true-square support or actual disk vertex
terms. In particular there is **no**
negative term proportional to
\(|\delta p_T|\) or \(|\delta p_G|\)
*alone*: the positive equal
horizontal/tilted path weights make
their reference center forces vanish.

Shrink the pose neighborhood so
\(|\delta p_T|+|\delta p_G|+S\)
is sufficiently small. Apply
Young's inequality to the five
mixed \(\delta p_i\,S\) terms,
with the uniformly positive
\(\mu_i\), absorbing at most
half of the positive
\(\sum\mu_i|\delta p_i|^2\)
and leaving only a constant times \(S^2\).
For sufficiently small S,
the quadratic error is bounded
by \((1/80)S\).
This turns (11) into
\[
\boxed{
\mathcal D_{\rm owner}
\ge q_*+\mu_H F(q_*,y(t),t)
+\frac12\sum_{i=A,B,D,E,H}
   \mu_i|\delta p_i|^2
+\frac1{80}S.}                                  \tag{12}
\]
The same neighborhood works across
all **32** branches, since there
are finitely many and the exact
reserve in (10) is uniform.

**This is a rigorous nonlinear
neighborhood argument:** it uses
finite C² Taylor bounds on open
angle sectors, the genuine explicit
absolute-value cusps,
strictly positive dual weights
and a true uniform signed-angular
coercivity constant; it does
not infer local sharpness from
failure of a numerical solver.

## 5. Deduce sharpness from the full-domain five-corner scalar theorem

By actual disk containment and
genuine SAT nonoverlap,
(4) gives \(R^2\ge\mathcal D_{\rm owner}\).

The exact global-in-family
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md)
theorem proves
\[
F(q_*,y(t),t)\ge0
\]
in the valid radical/angle neighborhood
around its unique minimum at t*.

Combine with (12) to obtain
the quantitative inequality (2),
with \(c_0\) equal to half the
uniform minimum of the positive
circle weights. In particular,
\(R^2\ge q_*\), proving (1).

The equality conditions further force
all five angle differences in (6)
to vanish, the five circle-anchored
centers to coincide with their
pseudo references, and t=t*.
The T,G sliders remain free within
their remaining true disk/SAT constraints.
This matches the genuine known
candidate slider freedoms rather than
claiming an impossible isolated
unique seven-square pose.

A complete **eight-square**
packing sufficiently near the
exact eight-square construction
contains such a seven-square
configuration; deleting the central
square cannot invalidate seven-square
disk containment or pairwise
nonoverlap. Hence it cannot fit
in a smaller disk either. QED.

## 6. Precise remaining global obstruction

This theorem now removes both
**artificial** features from a
sufficiently small pose neighborhood
of the sharp seven-square ring:

1. the two distinguished end frames
   A and E need NOT be parallel;
2. the seven separator directions
   need NOT be imposed in fixed
   candidate coordinates; their
   genuine SAT owners are selected
   automatically by actual nonoverlap.

However the theorem is still **LOCAL
IN POSE SPACE**. A different global
eight-square minimizer might have
completely different contact topology,
centers, frames, or separator owners
far from the candidate. The next and
ONLY decisive global step is a
**capture theorem**, or a sharp
orientation-independent inequality
for all uncaptured minimizers,
as distinguished in
[PRIMARY_GLOBAL_BRIDGE.md](PRIMARY_GLOBAL_BRIDGE.md).

A certificate proof à la 11SquaresOptimal
would first prove every hypothetical
packing with \(R<\widehat R\) is
covered by finitely many sound
center/frame pose regions, exclude
all those incompatible with
the candidate neighborhood, and
apply the present exact local
theorem to the captured final
region. Such a cover **has not
been constructed here**.

The unrestricted \(R_8\ge\widehat R\),
global equality classification,
and Lean 4 formalization remain
**OPEN**. The true full seven-outer
equality ring is explicitly
preserved.
