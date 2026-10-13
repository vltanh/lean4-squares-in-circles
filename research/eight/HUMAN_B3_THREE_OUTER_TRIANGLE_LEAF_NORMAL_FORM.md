# The smallest k=7 central-branching stress core is a triangle plus one radial positive leaf

**2026-10-13. Complete finite positive-stress graph normal form
for the four-square B3 core**, valid for all actual independent
square frames. This is a structural deduction from the new
global circle-force semicircle theorem and the previous
actual bridge/cycle theorems, not a numerical interval result.

## Theorem

Let a packing of eight genuine, pairwise interior-disjoint
unit squares attain the least containing-disk radius
\(R\le\sqrt{9789/2500}<2\).
Let C denote the unique open origin-containing square,
and assume exactly **seven exterior square centers are outer**.
Assume the induced actual-contact graph on those seven
outer centers is a **proper subgraph of their angular
seven-cycle**, not the full actual contact ring.

Choose a normalized physical stress whose **unique
nontrivial positive contact component J** contains
**exactly four square labels**, namely C and
three distinct outer squares X,Y,Z, with
\(\deg_{G_+}(C)\ge3\).

Then, after renaming the three outer labels:

1. The **entire positive-contact graph J** is
   exactly the triangle
   \[
   \boxed{C-X-Y-C}
   \]
   together with the **pendant positive-stress edge C-Z**.
   In particular C has positive degree exactly three,
   and there is exactly **one** positive outer--outer
   contact pair X--Y.
2. X and Y are **consecutive outer-center ray labels**,
   while the three labels X,Y,Z **cannot form one
   consecutive three-label block** among all seven
   outer center rays.
3. The positive C--Z edge is a **true stress bridge**.
   Its actual contact is **radial about the
   containing disk origin**: the perpendicular foot
   from zero onto its true supporting line belongs to
   the actual C∩Z contact set. Its contact normal is one
   of the **eight signed C side or radial-corner
   directions** established in
   HUMAN_ACTUAL_BRIDGES.md.
4. Z has a **strictly positive physical circle-vertex
   multiplier** (and therefore a true vertex touching
   the containing circle). At least one of X,Y has a
   strictly positive circle-vertex multiplier as well,
   because the entire physical circle reaction
   cannot be supported on a single square's circle
   vertices.

This graph normal form is a **necessary configuration**,
not a proof that it is actually feasible at the
sharp eight-square radius.

## Proof

### 1. C touches all three positive outer labels

The positive component contains exactly C,X,Y,Z
and central positive degree at least three.
Since only three other labels are available,
\[
C-X,\quad C-Y,\quad C-Z
\]
are all **positive-stress actual contact edges**.

The outer-induced actual contact graph is a
forest, by the outer-center visibility theorem
HUMAN_OUTER_GRAPH_REDUCTION.md, so the
positive outer-only graph on X,Y,Z
is also a forest.

The full normalized stress contains a
**nonzero contact-moment circulation**,
proved in HUMAN_CONTACT_COMPONENTS.md.
Thus J has a directed nonzero-moment cycle;
a graph with only the three C spokes
would be a tree and have no cycle.
Therefore **at least one positive
outer--outer edge must exist**.

### 2. Two outer positive edges would force a forbidden consecutive triple

If there were two positive outer--outer edges
among X,Y,Z, the forest condition
forces them to form a **two-edge path**
on these three outer labels.

Every actual outer--outer contact joins
consecutive outer center rays among
the seven outer labels, by
HUMAN_OUTER_GRAPH_REDUCTION.md.
Two such edges on just X,Y,Z
make those three labels a **consecutive
three-label angular block** (with the
middle label having the two outer
neighbors).

But
[HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md](HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md)
proves that when the *only*
three noncentral labels in the
positive stress component form a
consecutive three-ray block,
the **global nonnegative physical
circle forces cannot balance**:
all possible positive circle
vertices lie in an angular arc
strictly shorter than π.

Indeed the central C has zero
circle multiplier, and every
noncomponent square has zero
positive contact force and thus
zero circle multiplier, by
HUMAN_CONTACT_COMPONENTS.md.
So all positive circle-force
vectors would come from these
three consecutive labels,
giving the prohibited
semicircle sum. This is a
complete geometric contradiction
for two positive outer edges.

Three outer positive edges would
form an actual outer triangle
X-Y-Z-X, which is not a subgraph
of the seven-center simple cycle
for seven distinct outer labels
(and would in any case violate
the proper outer-forest theorem).
Thus there can be **exactly one**
positive outer edge, say X--Y.

Together with the three C
spokes, the entire positive
graph is the stated C-X-Y-C
triangle and the C-Z pendant
edge. X,Y have consecutive
outer center directions;
X,Y,Z as a group must *not*
be a three-consecutive block,
by the same semicircle theorem.
This proves items 1,2.

### 3. The unique pendant edge is a genuine radial stress bridge

Removing the positive pair C--Z
disconnects Z from the other three
positive component labels, so C--Z
is a **positive-stress bridge**.

The exact physical stress bridge
theorem in
[HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md)
section 5, or its actual bridge
counterpart in
[HUMAN_ACTUAL_BRIDGES.md](HUMAN_ACTUAL_BRIDGES.md),
proves that every positive
stress bridge is radial:
its effective contact point
lies on the normal ray
from the disk origin.
The radial-contact lemma
also forces the central C
endpoint, which is already
identified here.

The eight allowed signed central
directions (the four true C
side normals or four radial
directions to actual C vertices)
are proved in HUMAN_ACTUAL_BRIDGES.md
section 3 and apply to the
genuine contact point and normal.
Thus item 3 follows. Note:
the edge is *certainly a positive
stress bridge*, but it need **not**
be a bridge of the full actual
contact graph if some other
square contact carries zero
positive weight; we invoke
the valid stress-bridge theorem
and do not assume that stronger
actual-bridge condition.

### 4. Circle-force support on Z and at least one of X,Y

The **only positive contact force**
on Z is from the C--Z edge,
with strictly positive magnitude.
Its nonzero resultant physical
contact force therefore satisfies
\(F_Z\ne0\).

The exact force/circle equivalence
in HUMAN_CONTACT_COMPONENTS.md
says \(F_i=0\) if and only if the
total circle multiplier \(m_i=0\).
Therefore
\[
\boxed{m_Z>0.}
\]
Every positive multiplier occurs
at a genuine vertex on the disk
circle, so Z is a true
circle-contact square.

Suppose both X and Y had total
circle multipliers zero.
C also has m_C=0, and all four
noncomponent spectators have
zero multipliers because they
have zero positive forces.
Then **every** positive circle
multiplier would belong to Z
alone. The global
[HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md](HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md)
theorem excludes such a
one-square angular force support
(a single center ray lies in
an arc of width zero,
well below π−31/40).
Equivalently all true circle
vertices of Z belong to a
common open semicircle and
cannot balance global
positive radial reactions.

Thus at least one of X,Y
also has \(m>0\). This proves
item 4. QED.

## Next structural proof target for B3

The **entire k=7 central-branching
four-square positive core**
has been reduced to one
specific contact/force graph:
a stressed **C-X-Y triangle**
plus one **radial stressed
C-Z leaf bridge**, with Z's
outer ray not making a
three-consecutive block with
X,Y.

The next sharp goal is to
combine the true radial
C-Z contact (normal among
eight central signed frame
directions), the actual
C-X-Y triangle contact
separator axes, two or more
genuinely positive
circle-multiplier outer
vertices, and the **four
remaining full unit-square
spectators** to prove the
sharp radius lower bound.

This theorem neither excludes
the entire B3 root nor assumes
the triangle's contact axes
are parallel, nor discards
zero-weight actual spectator
contact edges. The real
equality-bearing seven-outer
actual-contact ring A remains
valid. The unrestricted
\(R_8\ge\widehat R\),
equality classification and
Lean 4 formalization remain
OPEN.
