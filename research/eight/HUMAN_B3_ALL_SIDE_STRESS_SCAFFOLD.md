# All-side-normal minimal B3 stress is an opposite-side triangle with transverse bracing

**Structural research, 2026-10-13.** This is an exact,
orientation-independent case reduction for **one** of the
four bridge-interface types in the minimal branching core.
It is not a full exclusion of B3 or the global radius theorem.

## Hypotheses

Let an eight-unit-square minimum-radius packing satisfy
\(R^2\le9789/2500\), with unique origin-containing C,
seven outer exterior square centers and no complete outer
actual-contact ring. Let its unique nontrivial positive
stress component be the smallest central branching core:
\[
C-X-Y-C \quad\text{plus positive radial bridge }C-Z.
\]

Suppose further that **all three positive C-contact normals
are true side normals of C**, and that the leaf bridge
C--Z is in the **radial side mode** proved in
[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md).

Write n for the outward radial C--Z contact normal, and
\(t=Jn\). Because n is a true side normal of C, its
positive contact with Z uses C's +n side, at offset
\[
b=\sqrt{R^2-\tfrac14}-1>\tfrac45.
\]
Let the positive contact forces on C--X,C--Y,C--Z
have magnitudes \(\lambda_X,\lambda_Y,\lambda_Z>0\).

## Theorem (no three-distinct-side stress, exact opposite-side scaffold)

Under these hypotheses:

1. **Both** X and Y have the **same** outward
   C-contact normal \(-n\). They contact C on
   the central side opposite Z, and
   \[
   \boxed{\lambda_Z=\lambda_X+\lambda_Y.}       \tag{1}
   \]
   Thus the three stressed C contacts occupy **only
   two opposite sides**, never three distinct sides.
2. Their two actual positive-contact points on C,
   \(z_X,z_Y\), have **strictly opposite signed
   transverse coordinates**:
   \[
   \boxed{(t\cdot z_X)(t\cdot z_Y)<0,\qquad
     \lambda_X(t\cdot z_X)+
     \lambda_Y(t\cdot z_Y)=0.}                   \tag{2}
   \]
3. The outer triangle contact X--Y cannot have
   a separating normal parallel to n.
   Its positive contact normal has a **nonzero
   transverse t component**.
4. X,Y,Z all have **positive physical circle-vertex
   multipliers**, and the resulting circle reaction
   forces at X,Y have **opposite nonzero transverse
   components**. Thus true positively weighted
   circle vertices occur on both transverse sides
   of the disk origin.

The frames of X and Y are **not assumed parallel** to
C. Their contact points may be on sides or corners.
These are necessary structural constraints, not a proof
of geometric realizability.

## Proof

**1. A high whole-cap excludes any second +n contact.**
The radial **side** mode of Z proves
\[
z_Z=b n,\quad b=\sqrt{R^2-\tfrac14}-1,\quad
Z\subseteq\{w:n\cdot w\ge b\}.
\]
The rigorous radius lower bound
\(R>\sqrt2+1/2\) gives \(b>4/5\).
The existing exact two-unit high-cap capacity theorem
in HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md shows
**no two distinct packed unit squares** can both
lie wholly in the same cap \(n\cdot w\ge b\).
In particular, neither X nor Y may have an actual
C-contact normal +n, since that would put the
corresponding whole square in the same high cap
already occupied by Z.

The positive C-contact normals are assumed to be
true **side** normals of C, so the only remaining
possibilities for X and Y are \(-n,+t,-t\).
C has zero disk-circle force, so its positive
force balance, with outward contact normals, reads
\[
\lambda_Z n+\lambda_X n_X+\lambda_Y n_Y=0.
\]
Dotting with n requires at least one of n_X,n_Y
to be \(-n\): the other permitted normals have
n component zero. If exactly one were -n, the
other would be ±t and would contribute an
uncancelled nonzero t component. Therefore
both must equal \(-n\), and the n component of
force balance gives (1).

**2. Central torque forces the two opposite-side contacts
to straddle the radial line.**
The true combined C--Z contact point is \(b n\),
so its contact force has **zero torque about the disk
origin**. At C, the other two positive forces point
along +n (since their outward C-contact normals are
-n). Write
\[
z_X=-k n+\tau_X t,\qquad
z_Y=-k n+\tau_Y t
\]
for their actual combined contact points on the *same*
opposite C side. The exact physical torque equilibrium
at the circle-free C is
\[
\lambda_X\tau_X+\lambda_Y\tau_Y=0.              \tag{3}
\]

If both \(\tau_X,\tau_Y\) vanished, then **all three**
positive C-contact edge moments about the disk origin
would vanish. The only remaining positive-stress
edge X--Y would also have zero moment, by torque
conservation at X and Y: circle-vertex reactions
produce no origin moment and each of X,Y has only
the two positive triangle contact edges.
The entire positive component would then have
**zero contact-moment circulation**, contradicting
the established nonzero-moment component theorem
in HUMAN_CONTACT_COMPONENTS.md.

Consequently (3) has two **nonzero**, strictly
opposite signed values \(\tau_X,\tau_Y\),
proving (2).

**3. The triangle edge cannot transmit along ±n.**
Both X and Y lie wholly to the **same** side of
C's opposite support line:
\[
n\cdot w\le -k
\quad(w\in X\text{ or }Y).
\]
Each actually contacts C along that common line,
so each has the **same maximal n projection**
\(\max_X n\cdot w=\max_Y n\cdot w=-k\).
Their projected n intervals are positive-length
intervals both ending at -k, hence **overlap
in a positive-length interval**. Therefore neither
±n can separate the closed interiors of X and Y.
The positive true X--Y separating normal must
have a nonzero t component, proving 3.

**4. The transverse circle-force signs are opposite.**
By
[HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md](HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md),
both X and Y have strictly positive total circle
multipliers; by the radial-leaf force equation
Z also does.

Choose the directed positive X--Y contact normal m
from X toward Y. Its t component is nonzero by 3.
At X its only two positive pair-contact forces
are the C--X force \(-\lambda_X n\) and the X--Y
force \(-\lambda_{XY}m\); at Y they are
\(-\lambda_Y n\) and \(+\lambda_{XY}m\).
Their transverse t components are therefore
\[
F_X\cdot t=-\lambda_{XY}(m\cdot t),\qquad
F_Y\cdot t=+\lambda_{XY}(m\cdot t),
\]
strictly nonzero and opposite.
The physical circle stationarity equations
\(F_Q=2\sum_v\mu_{Q,v}v\) transfer these
opposite signs to the positively weighted
circle-vertex reaction sums.
Hence at least one positively weighted true
circle vertex of X and at least one of Y lie
on **opposite signed transverse sides**.
This proves 4. QED.

## What remains

This theorem eliminates every alleged **all-C-side-normal
minimal B3 core using three distinct C sides** in radial
side-leaf mode. The surviving all-side-normal case is one
specific true geometry: a high radial +n leaf, two genuine
outer stressed square contacts straddling the radial foot on
the opposite C side, an oblique outer triangle contact, and
positive circle reactions on both transverse sides.

Other B3 cores may have a C **corner** radial bridge, an
outer diagonal-mode leaf, or one or both triangle C contacts
with non-side-normal forces. Those alternatives are **not**
removed. This result has not established
\(R_8\ge\widehat R\), global equality classification
or Lean 4 formalization. The true seven-outer ring
equality construction remains admissible.
