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


## Exact 21-way outer-ray label classification for this minimal B3 core

The unique positively stressed outer
contact X--Y must join **consecutive**
outer center rays in the full seven-
label circular order. There are
seven possible choices of this
adjacent pair.

Once the pair is fixed as ray
indices \(i,i+1\) modulo seven,
the third positively stressed
outer label Z cannot occupy
indices \(i-1\) or \(i+2\):
either choice would make X,Y,Z
**three consecutive outer rays**,
contradicting the proved
global circle-force semicircle
theorem (independently of the
positive outer-edge structure).

It cannot coincide with X or Y.
The only three possible Z
ray positions are therefore
\[
\boxed{i+3,\quad i+4,\quad i+5
\pmod7.}
\]
These are exactly the positions
*not adjacent in the center-ray
cycle* to either X or Y.
Thus the four-square B3
triangle-plus-radial-leaf core
has precisely
\[
\boxed{7\cdot3=21}
\]
**combinatorially surviving
labeled positive-stress supports**,
all with the unique C-X-Y
triangle and C-Z radial bridge.
This is a finite contact-stress
label count, **not** 21
certified feasible packings.

The independent exact enumerator
[verify_B3_triangle_leaf_ray_labels.py](verify_B3_triangle_leaf_ray_labels.py)
checks all \(\binom73=35\)
three-outer-label subsets:
seven triples have no
outer-ray-adjacent pair and
cannot have a nonzero moment
cycle, seven triples are
consecutive and fail circle
force balance, leaving exactly
21 with one adjacent pair.
The **geometric and physical**
proof of the exclusions is
the preceding hand theorem,
not the enumerator.


## Sharper physical support theorem: ALL THREE outer labels have positive circle multipliers

[HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md](HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md)
strengthens the earlier necessary
\(m_Z>0,\ m_X+m_Y>0\) to
\[
\boxed{m_X>0,\quad m_Y>0,\quad m_Z>0.}
\]
Both X and Y have **exactly two
positive contact pairs** on the
C-X-Y positive triangle. If one
had zero circle force, its pair
normals would coincide and its
two neighboring squares (which
**actually contact** one another)
would have positive projected
separation at least one unit.
This is impossible for true
contacting squares. Z is a
positive bridge leaf, so its
single nonzero contact force
requires positive circle weights.

This says **all three** stressed
outer squares X,Y,Z contribute
genuinely positive disk-circle
reaction forces, irrespective of
zero-weight actual contacts to
spectators.

## Exact side/diagonal radial leaf normal form

[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md)
fully classifies the true square
Z (despite possible extra
zero-weight *actual* contacts):
the radial positive C-Z bridge
point is \(z=b n,\ b>0\),
and **Z's frame has only two
possibilities**:

| Z leaf mode | C--Z radial contact support b | Z's actual disk-circle vertices | Z's center |
| --- | --- | --- | --- |
| **Side** | \(b=\sqrt{R^2-1/4}-1>4/5\) | Two endpoints of Z's outer true side, **equal positive circle multipliers** | \((\sqrt{R^2-1/4}-1/2)n\) |
| **Diagonal** | \(b=R-\sqrt2\) | The **one** true outermost Z corner on \(R n\), with positive multiplier | \((R-1/\sqrt2)n\) |

Both have a **genuinely radial
leaf center ray n**, now
independent of Z's actual
contact degree. There is no
third generic oblique leaf
frame mode compatible with the
force/circle multipliers.

At C, the same radial contact
normal n can be a **true C side
normal** or a **radial direction
toward one of C's four true
corners**. An off-center radial
C corner is not generally a C
diagonal direction; do **not**
silently infer C and Z parallel
from a positive stress bridge.

The remaining minimal B3
bridge-interface geometric
modes are therefore the
four **C-side/C-corner times
Z-side/Z-diagonal** combinations,
each with the exact b and
Z true disk vertex equations
above.

## Exact antipodal global force cone

[HUMAN_B3_RADIAL_LEAF_ANTIPODAL_FORCE_CONE.md](HUMAN_B3_RADIAL_LEAF_ANTIPODAL_FORCE_CONE.md)
uses the global physical
circle-force balance and
the now-proved positive
circle weights at **X,Y,Z**.
Because X,Y are angularly
consecutive outer centers,
their positive disk-circle
vertices lie in a narrow
pointed cone near those
two center rays. Their total
reaction is exactly minus
the radial Z reaction.
Hence the genuine Z **center
ray** n lies in the strict
**antipodal** angular cone
\[
\boxed{
\theta_X+\pi-31/80
<\arg p_Z
<\theta_Y+\pi+31/80
\pmod {2\pi},
}
\]
with X,Y labeled in
positive outer cyclic order.
This restricts the three
eligible Z ray positions
without making any unjustified
center-to-whole-square
quadrant inference.

## Complete elimination of three distinct C-side contacts in the side-leaf, all-C-side mode

[HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md](HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md)
addresses the concrete mode
where **all three positive C
contact normals are C side
normals**, and the radial
leaf Z is in its **side** mode.
Its high outward cap
\(b=\sqrt{R^2-1/4}-1>4/5\)
is **exclusive** for whole
unit squares, so X,Y cannot
also contact C with the
same +n normal.

True C force balance with
three positive side normals
then forces both X,Y normals
to equal **the single opposite
side normal** -n (not
perpendicular ±Jn), with
\(\lambda_Z=\lambda_X+\lambda_Y\).
The actual C--X and C--Y
contact points must **straddle
the radial origin line** along
that opposite central side:
their signed transverse
coordinates are nonzero and
have opposite signs, by
C torque balance and the
required nonzero triangle
contact-moment circulation.

The positive outer triangle
edge X--Y has a genuine
separating normal **with nonzero
tangential component**, and
its positive circle reaction
forces on X and Y have
opposing nonzero tangential
components. This is a finite
global *side-scaffold* normal
form; it **eliminates**
the purported all-side-normal
subcase with three distinct
positive central sides, but
does **not** yet eliminate
the one surviving opposite-side
X/Y configuration.

All four bridge-interface
combinations, the surviving
opposite-face triangle and
four true spectator squares
still require a sharp global
radius bound \(R\ge\widehat R\).
The full equality ring A
is preserved and the
unrestricted proof is OPEN.


## 2026-10-13 further exact all-frame branch closures

**The full all-C-side SS radial leaf subcase is
now eliminated**, not merely normalized.
[HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md](HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md)
shows one of the two forced opposite-side
C triangle contact points is within
one-half unit of the radial origin line,
which by a **coupled true rotated-square
vertex bound** makes the corresponding
positive circle-stressed square strictly
circle-free. The positive triangle
circle-multiplier theorem contradicts this.
The strict squared-radius reserve is
\(6\sqrt{R^2-1/4}-11>0\).

The surviving SS positive C triangle normals
must have **strictly opposite tangential
components**, with actual C support points
on its top and bottom transverse sides.
At least one actual positive C contact is
at a **negative radial-side C corner**:
[HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md](HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md).
The CS (C radial corner/Z radial side) mode
also requires two nonzero opposite transverse
positive C triangle force components, by
[HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md](HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md).
These claims do not apply to SD unless
separately proved.

**Complete conditional actual spectator arc form:**
If C has *exactly the three actual neighbors*
X,Y,Z, then
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md](HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md)
proves the four other exterior squares can
form **no partial outer contact paths**:
each of the two complementary spectator arcs
between Y-Z or Z-X must be entirely present
or absent. Not both present (that is the
forbidden full outer actual ring).
This leaves only **three possible outer
actual graph patterns per positive ray triple**:
all four spectators isolated; complete Y-Z arc;
complete Z-X arc. With 21 prior positive
ray triples this gives **63 graph-only templates**,
versus 1,344 raw optional-edge assignments.

In contact-minimal CS/SD interface modes, the
Z positive bridge **must** also actually contact
a spectator; hence it requires one of the
two complete zero-stress spectator paths.
If C has additional zero-stress *actual*
spectator C contacts, this simple three-arc
classification is not asserted.

All full eight-square sharp radius bounds
and equality classification remain OPEN.
