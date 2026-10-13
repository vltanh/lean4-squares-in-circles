# A genuine radial bridge has only THREE side/corner interface types

**Structural research, 2026-10-13.** This is a full-frame,
actual square-separator theorem that eliminates the
previously speculative **central-corner/outer-diagonal**
bridge combination. It is an exact consequence of the
two-mode radial stress leaf theorem AND genuine SAT-normal
ownership; it does not depend on numeric cap optimization.

## Theorem (three exhaustive radial positive bridge interfaces)

Assume the full hypotheses of
[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md):
C contains the disk origin in its open interior,
Z is an exterior square with exactly one **positive**
contact-neighbor square C, the edge C--Z is a positive
stress bridge, and the true combined actual contact point
and force normal are
\[
z=b n,\quad b>0,\quad |n|=1.
\]
The square Z has side-radial or diagonal-radial mode.

**Importantly**, n is a genuine unit separating-axis
normal of the square-square contact. Hence it is a
signed true **side normal of C or of Z**, as provided by
the exact separating-axis/physical-stress theorem
[HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md).

Then precisely one of the following **THREE**
actual geometry modes occurs:

| Mode | Owner of the true pair-separating normal n | Contact face of C | Contact face of Z | Leaf Z circle vertices |
| --- | --- | --- | --- | --- |
| **SS** | Both square frames own n | Actual C side | Z's **inner side midpoint** | Two outer-side vertices, equal positive weights |
| **CS** | Z owns n | Actual **C corner** radial toward origin-normal n | Z's **inner side midpoint** | Two outer-side vertices, equal positive weights |
| **SD** | C owns n | Actual C side | Z's **inward corner** | One outward corner \(R n\), positive weight |

The combination **C-corner/Z-diagonal is impossible**:
\[
\boxed{\neg(\text{C corner support of }n
   \land\text{Z diagonal support mode of }n).}   \tag{1}
\]

The corresponding exact outward radial support offsets
are
\[
\begin{aligned}
\text{SS or CS:}\quad
& b=\sqrt{R^2-1/4}-1,\\
\text{SD:}\quad
& b=R-\sqrt2.
\end{aligned}                                    \tag{2}
\]

Additional consequences:

1. In mode SS the frames of **C and Z are parallel
   modulo right angles**, and their true contact
   is at the Z inner side midpoint.
2. In mode SD Z's frame is rotated by **45 degrees
   modulo right angles** relative to C's frame.
   The contact is a true central side-to-leaf-corner
   contact, with the leaf's *other* corner on the
   disk circle.
3. In mode CS Z's frame is aligned to n as a side normal,
   but **C's frame need not be parallel** to Z:
   the radial direction of an off-center C corner
   is not generally a diagonal of C.
4. Both SS and CS have
   \(b=\sqrt{R^2-1/4}-1>4/5\) in the
   established n=8 radius range.
   Thus no **other whole unit square** can
   lie beyond the same central-owned
   half-plane \(n\cdot x\ge b\), by the
   previously proved high-cap capacity lemma.

These statements are true for **positive stress bridge
leaves**, even with additional *zero-stress actual*
contacts of Z. They do not assert that any of the
three surviving modes is geometrically feasible
in a full eight-square packing.

## Proof: true separating-axis ownership rules out the fourth interface

The exact leaf theorem cited above already proves
there are just two radial Z frames:

* Side mode: n is a genuine **side normal of Z**,
  with inner side midpoint at \(bn\),
  \(b=\sqrt{R^2-1/4}-1\), and two equal-positive
  outer circle-vertex multipliers.
* Diagonal mode: n is a genuine **diagonal direction
  of Z**, with inner vertex at \(bn\),
  \(b=R-\sqrt2\), and a unique outer
  true circle vertex at \(Rn\).

Independently, the convex square C's exposed support
face in n must be either (i) a **side segment**,
which happens exactly when n is a true C
side normal; or (ii) a **single C corner**,
which happens when n is *not* a side normal.
The contact point \(bn\) belongs to that face;
in case (ii) the corner itself is radial
from the disk origin.

At a genuine actual contact of two squares,
the separating-axis theorem states the true
contact separating normal **is a signed
side normal of at least one of the two squares**.
That is part of the underlying physical
stress construction, not an additional ansatz.

If Z is in **diagonal** radial leaf mode,
n cannot be a Z side normal (an honest square
diagonal is separated from either side normal
by \(\pi/4\)). The separating-axis theorem
therefore forces n to be a side normal **of C**.
This is mode SD, and the C-corner/Z-diagonal
combination is **completely impossible**.

If Z is in **side** radial leaf mode,
n is a true Z side normal; C may then have
either a side exposed face or a corner
exposed face. Those are modes SS and CS.
They exhaust all true contacts.

If n is a C side normal and simultaneously a
Z side normal, the two genuine unit-square
frames share a side direction and are parallel
modulo \(\pi/2\). If n is C side but Z diagonal,
their frames differ by \(\pi/4\) modulo
\(\pi/2\). The off-center C radial corner
mode does not force a C diagonal frame.

Finally the exact radial b formulas come from the
earlier full true-circle-vertex stress leaf theorem.
When Z is in side mode, the established radius lower
bound \(R>\sqrt2+1/2\) yields b>4/5, and the
all-orientation high-cap pair capacity theorem
forbids another entire unit square in that
cap. This proves all assertions. QED.

## Application to the smallest seven-outer B3 root

The exact stressed-graph normal form
[HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md)
consists of a positive triangle C-X-Y-C
and a radial stress leaf C-Z. The leaf
must use exactly one of **SS, CS, SD**.

**The fourth former bridge case is now rigorously
excluded**, regardless of the square centers,
unused spectator orientations, or zero-positive-stress
actual contacts.

* **SS:** C and Z are parallel; high radial
  leaf side cap is exclusive. If C-X/C-Y also
  use true side normals, the opposite-side
  and transverse-bracing theorem in
  [HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md](HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md)
  applies.
* **CS:** C has a genuine radial **corner**
  contact to a side-framed Z, with the same
  high cap capacity restriction.
* **SD:** C has a **side** contact to the
  diagonal-framed Z, with a unique
  outermost circle vertex on \(Rn\).
  Its support offset is the lower
  \(b=R-\sqrt2\), so the high-side
  pair-capacity theorem cannot
  be imported without new proof.

The B3 radial leaf no longer has an arbitrary
frame angle, but the rest of the contact triangle,
four exterior spectators and global sharp radius
obstruction remain OPEN. The known full seven-outer
contact-cycle equality packing is untouched.
