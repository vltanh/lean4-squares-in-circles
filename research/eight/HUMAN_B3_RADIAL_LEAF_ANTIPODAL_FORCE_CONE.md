# Global circle-force equilibrium puts the B3 radial leaf opposite its stressed triangle

**Structural research, 2026-10-13.** This is a whole-packing
force-cone theorem for the smallest seven-outer branching
positive-stress component. It is not another cap-offset
optimization and does not claim that the B3 root is eliminated.

## Theorem

Assume the hypotheses of
[HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md):
an attained radius-minimizing eight-square packing
with seven outer-center exterior labels, no full outer
actual-contact ring, and unique positive stress
component
\[
\boxed{C-X-Y-C\quad\text{plus the radial positive bridge }C-Z.}
\]
Here X,Y are circularly **consecutive** among all seven
outer center rays. Orient the plane so their unwrapped
angles are \(\theta_X<\theta_Y\) on the shorter ordinary
circular-neighbor arc, and let
\(\delta=\theta_Y-\theta_X\).
Let n be the actual radial positive bridge normal
from C to Z.

Put \(\beta=31/80\). Then the **actual Z-center ray
is exactly n**, and the normal n satisfies the
strict antipodal arc restriction
\[
\boxed{
\theta_X+\pi-\beta
<\arg(n)
<\theta_Y+\pi+\beta
\quad\pmod{2\pi}.}                               \tag{1}
\]

The interval in (1) has width
\[
\delta+2\beta
<\frac\pi2+\frac3{250}+\frac{31}{40}
<\pi.                                            \tag{2}
\]
Thus Z is confined to a **strict angular cone
opposite the positive-circle-force cone** of X,Y.

The X,Y and Z square centers are not assumed parallel
to their contact normals, except for Z, whose radial
center conclusion follows from the exact
[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md).

## Proof

### 1. All three outer labels have positive physical circle force

[HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md](HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md)
proves that both positive-cycle outer triangle
members X,Y have **strictly positive total
disk-circle multipliers**. Otherwise, at one
triangle vertex the two positive contact normals
would align, creating a full unit-width straight
separator between its two neighbors, contradicting
their **actual contact**.

The radial bridge Z has only one positive
square-pair contact, with nonzero resultant
force \(\lambda n\). The physical equilibrium
equation therefore gives positive circle
force \(\lambda n\), so \(m_Z>0\).
All other squares, including the central
circle-free C and four exterior positive-stress
spectators, have zero circle multipliers
by the established component force stationarity.

The bridge is radial, so its combined true
contact point has the form \(b n\), \(b>0\).
The leaf-classification theorem cited above
proves that the leaf Z is either a radial
side-mode unit square with center
\((\sqrt{R^2-1/4}-1/2)n\), or a radial
diagonal-mode unit square with center
\((R-1/\sqrt2)n\). In either case
\[
\arg p_Z=\arg n.                                 \tag{3}
\]

### 2. All X and Y circle forces lie in a short cone

Every genuine unit-square circle-contact
vertex lies within angular deviation
\[
<\beta=31/80
\]
of its **own center ray**, by the
exact true-vertex shadow theorem in
[HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md](HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md).

Because X,Y are two **consecutive**
outer-center rays among seven,
and every one of the other six
circular neighbor gaps is strictly
greater than \(\pi/4-1/500\),
their mutual directed gap obeys
\[
0<\delta
<2\pi-6(\pi/4-1/500)
=\pi/2+3/250.                                    \tag{4}
\]
Therefore all positively weighted
circle-vertex vectors of X and Y
have ray angles in the **single**
open arc
\[
(\theta_X-\beta,\;\theta_Y+\beta)
\]
of width strictly below the first
quantity in (2).

That width is **less than \(\pi\)**:
indeed \(\pi/2>3/2\)
and \(3/250+31/40<1\).
An angular sector of width
strictly below \(\pi\) is a
pointed convex cone. Every
strictly positive linear
combination of nonzero vectors
whose directions lie inside
that angular arc is nonzero
and has its direction inside
the **same** open arc.

In particular, the sum of
the positive circle-reaction
vectors of X and Y,
\[
V=\sum_{v\in\partial D_R\cap \mathrm{Vert}(X)}
  \mu_v v
 +\sum_{w\in\partial D_R\cap \mathrm{Vert}(Y)}
  \mu_w w,
\]
is nonzero with ray direction
strictly in
\((\theta_X-\beta,\theta_Y+\beta)\).

### 3. Global positive radial forces determine the bridge ray

The normalized global physical
circle-force equation is
\[
\sum_{\text{all true circle vertices}}\mu_v v=0.
\]
Only X,Y,Z carry positive multipliers,
so this reduces to
\[
V+\sum_{v\in\mathrm{Vert}(Z)\cap\partial D_R}
   \mu_v v=0.
\]
Since Z has one positive
C--Z force \(\lambda n\),
its circle-reaction sum is
\[
\sum_{v\in Z}\mu_v v=\frac\lambda2 n.
\]
Thus
\[
V=-\frac\lambda2 n.
\]
Because the direction of V is
strictly in the short cone
\((\theta_X-\beta,\theta_Y+\beta)\),
the direction of n is in its
**antipodal cone**:
\[
\arg n\in
(\theta_X+\pi-\beta,\,
 \theta_Y+\pi+\beta)
\pmod{2\pi}.
\]
With (3) this proves (1).
The width comparison (2)
was proved in section 2. QED.

## How this reduces the actual B3 case

The earlier outer-ray graph theorem
left exactly **three possible radial
leaf Z label offsets** relative to
the positive outer pair X,Y:
indices \(i+3,i+4,i+5\) modulo seven.
The present theorem adds a **global
physical-force angular cone** for
each placement, not merely a
contact-graph incidence condition.

Together with
[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md),
the remaining minimal B3 core is now:

* a true C--X--Y triangle of
  positive contacts, with **all
  X,Y,Z genuinely positive
  disk-circle multipliers**;
* one **radial** C--Z positive
  bridge of **side or diagonal
  leaf type**, with an exact
  C-to-Z radial contact distance;
* Z's radial center angle constrained
  by the antipodal force-cone (1);
* four other actual full unit-square
  spectators still occupying the disk.

No complete B3 impossibility
or sharp radius bound follows yet.
The equality-bearing seven-outer
full actual-contact ring remains
a separate valid branch.
