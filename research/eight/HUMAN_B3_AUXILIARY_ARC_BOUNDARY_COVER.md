# Complete zero-stress B3 spectator arcs force disk vertices or a rigid transmitter

**Structural research, 2026-10-13.** Exact all-orientation
geometric rigidity for the complete zero-positive-stress
outer spectator paths of the smallest k7/B3 triangle-
plus-radial-leaf core. This uses genuine actual contact
degree, not positive-stress degree, and does not
optimize a cap threshold.

## Theorem

Assume an eight-square radius minimizer selected
with **minimum actual pair-contact count** at \(R<2\),
with k=7 exterior outer centers, no full actual outer
seven-ring, positive stress graph
\[
C-X-Y-C\quad\text{plus positive radial bridge }C-Z,
\]
and **exactly three actual C square neighbors**
X,Y,Z.

The actual outer contact graph is one of the
three patterns in
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md]
(HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md):
all spectators isolated, or exactly one
**complete actual Y-Z or Z-X outer contact arc**.
Consider the latter case and call its stressed
endpoints A,B (so \(\{A,B\}=\{Y,Z\}\) or
\(\{Z,X\}\)). Let the consecutive actual
spectator squares along this full arc be
\[
A-T_1-T_2-\cdots-T_s-B,
\qquad 1\le s\le3.
\]
Every edge along the arc is a **real
square-square contact**, but every such
edge has zero positive stress in the
chosen physical stress.

Then:

1. Each spectator \(T_j\) has **exactly two
   actual square neighbors**, its immediate
   predecessor and successor on the arc.
2. The spectator labels with **true
   containing-circle vertices** form a
   **vertex cover of the internal spectator path**:
   \[
   \boxed{\text{for }1\le j<s,\quad
       T_j\text{ circle-contacts}\quad\text{or}\quad
       T_{j+1}\text{ circle-contacts}.}
   \]
   In particular at least \(\lfloor s/2\rfloor\)
   of the spectator labels have true
   disk-circle vertices, even though
   **all their chosen physical circle
   multipliers are zero**.
3. For a **single-spectator arc** (\(s=1\)),
   either T1 has an actual disk-circle
   vertex, or it is a true, circle-free
   degree-two **aligned transmitter**
   between A and B. In the latter case
   \[
   \boxed{\operatorname{dist}(A,B)=1,}
   \]
   and T1 has its true opposite contacts
   on two parallel frame sides.
4. The **complete arc size** s is fixed
   combinatorially by Z's outer-ray index.
   Normalize the positive X-Y pair to
   outer indices \(i,i+1\) modulo seven;
   the radial leaf Z is index \(i+3\),
   \(i+4\), or \(i+5\). The two
   possible complete arc sizes are:
   \[
   \begin{array}{c|cc}
   Z\text{ ray index}&Y\to Z&Z\to X\\
   \hline
   i+3&1&3\\
   i+4&2&2\\
   i+5&3&1
   \end{array}
   \]
   Thus **four of the six
   Z-position/arc-direction patterns**
   force at least one zero-positive-stress
   spectator genuinely **touching the circle**;
   the other two have a one-square
   transmitter-or-circle-contact alternative.

These are true-square necessary conditions,
not a classification of feasible complete
eight-square packings.

## Proof

By the exact complete-arc actual-contact
theorem cited above, one complementary
outer-ray path A-T1-...-Ts-B has **all
its edges present**, while the other
complementary arc has no actual edges.
The four exterior spectators are
not actual C neighbors, by hypothesis,
and the outer-center angular-visibility
theorem prevents contacts with any
nonconsecutive outer ray label.

Thus every Tj in the full arc
has exactly its two immediate path
neighbors as **all** its actual
square contacts; this proves 1.

Suppose two consecutive such
spectators Tj,Tj+1 were both
strictly inside the containing circle.
Each is then a circle-free true
unit square with **exactly two actual
square neighbors** in a radius-minimal
configuration chosen with minimum
actual contact count.
The existing strict interior
transmitter theorem in
HUMAN_CYCLE_ANALYSIS.md section 8
forces both to be **genuine
aligned side-to-side unit-width
transmitters**. But they are
themselves actually contacting
neighbors, and the exact
adjacent-interior-transmitter
lemma prohibits two adjacent
circle-free such transmitters
at \(R<2\).

Hence at least one of each
consecutive spectator pair
must have a true disk-circle
vertex, proving 2.
The standard disjoint-edge
lower bound for a path on s
vertices gives a minimum
vertex-cover size
\(\lfloor s/2\rfloor\).

If s=1 and T1 is circle-free,
the same actual-degree-two
interior transmitter theorem
applies. Section 9 of
HUMAN_CYCLE_ANALYSIS.md proves
that a strictly interior
two-contact transmitter
has opposite true side-frame
contact normals, and its two
distinct neighbor squares
A,B have **exact Euclidean
closed-set distance one**.
This proves the alternative
and (3) without asserting that
T1 is circle-free a priori.

The ray-index table is the
elementary counting of the
outer-center path intervals.
With XY occupying i,i+1,
a Z at i+d, d∈{3,4,5},
has d−2 internal spectators
between Y and Z and
\(6-d\) spectators between
Z and X. These pairs are
(1,3),(2,2),(3,1).
At least one spectator circle
contact follows for s>=2,
by the vertex cover just proved.
This proves 4. QED.

## Implication for genuine CS/SD radial stress bridges

The exact
[HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md]
(HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md)
theorem proves that in contact-minimal
**CS (C corner/Z side)** and
**SD (C side/Z inward corner)**
radial-bridge modes, Z must
have at least one additional
**actual** contact with a
neighboring spectator. With
exactly three actual C neighbors,
the complete-arc theorem
forces the whole Y-Z or Z-X arc.

The present theorem therefore
supplies genuine additional
disk-circle vertices (for
spectator arcs of size two
or three), or an exact
distance-one aligned transmitter
when a one-spectator arc is
circle-free. This is a
structural next input to a
whole-packing sharp-radius
inequality, *not* a standalone
B3 impossibility proof.

If C has extra zero-weight
actual contact neighbors, these
complete-arc conclusions cannot
be imported without proving a
corresponding true actual-contact
normal form. The equality-bearing
full seven-outer contact ring
and all other global stress roots
remain OPEN.
