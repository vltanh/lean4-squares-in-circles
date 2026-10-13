# Entire all-C-side radial SS branching triangle excluded by a near-origin support-face vertex bound

**2026-10-13. Full orientation-independent hand exclusion of a
global k=7/B3 actual stress subcase.** This is a *structural
circle-force obstruction*, not a cap-threshold refinement.
It strengthens [HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md]
(HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md), whose formerly
surviving opposite-side X/Y triangle case is now **impossible**.

## 1. General full-frame one-contact square lemma

**Lemma (inward cap face, limited transverse contact).**
Let Q be any genuine unit square of arbitrary orientation,
wholly contained in
\[
\{(x,y): x\le-k\},\qquad 0\le k\le\tfrac12.
\]
Suppose Q has an **actual point** on its *rightmost*
support face at
\[
z=(-k,\tau),\qquad |\tau|\le\tfrac12.
\]
Then **every** actual vertex v of Q obeys
\[
\boxed{|v|^2\le (k+1)^2+\frac94.}                \tag{1}
\]

**Proof.** If Q has a right-support **side**, its
frame is axis-parallel: its x interval is
[-k-1,-k]. Because z belongs to the support
side of length 1, the y displacement from z
to any true vertex is at most 1. Thus every
vertex satisfies \(|v_x|\le k+1\),
\(|v_y|\le|\tau|+1\le3/2\), proving (1).

Otherwise its rightmost support face is a
**single true corner** z. Its two inward
unit side-edge displacements may, by reflection
and relabeling, be written as
\[
u=(-c,s),\quad w=(-s,-c),\quad
c\ge s>0,\quad c^2+s^2=1 .
\]
The four actual vertices are
\(z,z+u,z+w,z+u+w\).
For z+u and z+w the same elementary
coordinate bounds \(|v_x|\le k+1\),
\(|v_y|\le|\tau|+1\le3/2\) prove (1).
For the opposite corner, write
\(L=c+s\), \(D=c-s\), so its coordinates are
\[
z+u+w=(-k-L,\tau-D).
\]
Consequently
\[
|z+u+w|^2
\le(k+L)^2+(\tfrac12+D)^2.
\]
Using the **exact true-square identities**
\(L^2+D^2=2\) and \(L+D=2c\le2\),
together with \(L\ge1\) and \(2k\le1\), we get
\[
\begin{aligned}
&(k+L)^2+(\tfrac12+D)^2
       -\left((k+1)^2+\tfrac94\right)\\
&\quad=2k(L-1)+(D-1)\\
&\quad\le (L-1)+(D-1)\\
&\quad=L+D-2=2c-2\le0.
\end{aligned}
\]
The key inequality **retains the correlated
linear terms** \(L-1\) and \(D-1\):
replacing both independently by their
worst endpoint bounds would be invalid. This proves (1) for every
independent square frame. QED.

**Disk consequence.** Put
\[
\rho=\sqrt{R^2-\tfrac14},\quad
b=\rho-1,\quad k=1-b=2-\rho.
\]
If
\[
R>\sqrt2+\tfrac12,\qquad R<2,
\]
then \(\rho>11/6\) and \(0<k<1/2\).
Indeed
\[
\rho^2=R^2-\tfrac14>2+\sqrt2>
\frac{121}{36},
\]
where \(\sqrt2>49/36\) follows by
squaring. Also \(R<2\) implies
\(\rho<\sqrt{15}/2<2\), so k>0.
For any Q satisfying the lemma's
contact hypotheses with this k,
\[
\begin{aligned}
R^2-\left((k+1)^2+\frac94\right)
&=\rho^2+\tfrac14-
   \left((3-\rho)^2+\frac94\right)\\
&=\boxed{6\rho-11>0.}                         \tag{2}
\end{aligned}
\]
Thus **every true vertex of Q is strictly
inside the disk**, so Q cannot have
a positive physical circle-vertex multiplier.

## 2. Apply to the smallest central branching core

Assume an attained minimum-radius
eight-square packing at \(R^2\le9789/2500\),
with seven outer exterior square centers,
whose sole nontrivial positive stress component
is exactly
\[
C-X-Y-C\quad\text{plus radial positive bridge }C-Z.
\]
Assume in addition that:

1. Z has genuine **radial side mode** (SS),
   with normal n from C to Z, common
   radial support point \(bn\), and
   \[
   b=\rho-1>4/5,\quad
   Z\subseteq\{q:n\cdot q\ge b\};
   \]
2. the positive C--X and C--Y
   contact normals are both
   **true C side normals**.

By the already proved full-frame
[HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md]
(HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md),
the entire high outward Z cap contains
no second square, and C force balance
forces both X,Y to contact the
**single opposite C side** with outward
normals \(-n\).

Choose coordinates \(n=(1,0)\),
\(t=Jn=(0,1)\).
Because C is a genuine unit square
whose +n side is at \(x=b\),
its opposite side is at
\(x=b-1=-k\), where
\(k=1-b=2-\rho\in(0,1/2)\).
The actual combined positive contact
points are therefore
\[
z_X=(-k,\tau_X),\qquad
z_Y=(-k,\tau_Y),
\]
with the two true squares X,Y
**wholly contained in** \(x\le-k\).

The earlier exact C torque/stress-circulation
argument proves that these two
contact transverse coordinates are
**strictly opposite in sign**:
\[
\tau_X\tau_Y<0.
\]
They both belong to the *same*
C opposite support **side of length 1**.
It follows immediately that
\[
\boxed{\min(|\tau_X|,|\tau_Y|)\le\tfrac12.}    \tag{3}
\]
Indeed two real points of opposite sign
with magnitudes both greater than 1/2
would have mutual transverse separation
strictly greater than 1, impossible
on one side segment of length exactly 1.
(The equality boundary is allowed.)

Choose Q to be the one of X,Y
satisfying \(|\tau_Q|\le1/2\).
Its true rightmost x-support
face contains the actual contact
\(z_Q=(-k,\tau_Q)\). By the
arbitrary-orientation lemma (1)
and strict disk comparison (2),
**all of its true vertices lie
strictly inside** the containing
circle. Therefore its physical
circle-multiplier sum is zero:
\[
m_Q=0.
\]

But
[HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md]
(HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md)
proves **both positive triangle squares**
X and Y must have **strictly positive**
circle-vertex multipliers: if one did
not, its two positive contact forces
would transmit along one common normal,
forcing its two actual-contact neighbors
apart even though they touch.

Thus \(m_Q=0\) contradicts \(m_X,m_Y>0\).
The entire all-C-side **radial SS
branching triangle subcase is impossible**.
QED.

## 3. Scope and exact next structural cases

This is a **complete structural subcase
elimination**, not a small interval exclusion.
It does not assume X/Y parallel to C,
or make any nonphysical alignment
assumption.

In the smallest k7/B3 positive core,
the radial Z bridge has only three
genuine SAT interfaces:
SS (C-side/Z-side), CS
(C-corner/Z-side), SD
(C-side/Z-diagonal).

The present theorem **eliminates the
entire SS branch whenever the two
triangle C contacts are themselves
true central-side normals**.
The remaining SS possibilities must
include at least **one non-side-normal
C--X or C--Y contact force** (i.e.
contact toward a C corner).

The CS and SD bridge modes are
not covered by this theorem.
In a contact-minimal minimizer
they require genuine zero-stress
spectator bracing, by
HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md.
All remaining B3 modes require
a global sharp-radius inequality
or a separate whole-mode
obstruction. The true equality
packing's full seven-outer contact ring
belongs to a different global root.

The unrestricted eight-square radius
inequality \(R_8\ge\widehat R\),
full equality classification and
Lean formalization remain OPEN.
