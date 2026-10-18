# The unique k=7 m=6 spectator is isolated, a central leaf, or a circle-anchored triangle

**2026-10-12. Complete global actual-contact incidence classification
of the spectator in the B2/k=7/m=6 stressed-path root.**
The theorem holds for **any** actual central degree; it
does not assume a bare central transmitter and does not
optimize any cap interval.

## Theorem

Choose an attained eight-unit-square least-radius minimizer,
with the **fewest actual square-square contacting pairs**
among all least-radius packings, and assume
\(R^2\le9789/2500\).

Suppose the seven exterior centers are outer (norm >=1),
their **actual** outer-contact graph is a **proper
subgraph of the seven-ray neighbor cycle**, and
a normalized physical stress has exactly two
positive-stress central neighbors S1 and S6,
with unique nontrivial positive component
\[
C-S_1-S_2-S_3-S_4-S_5-S_6-C.
\]
Let T be the sole seventh outer square
on the complementary center-ray arc between
S6 and S1.

Then the true *complete actual-contact
neighborhood of T* has **exactly one of
four labeled possibilities**, grouped into
three structurally distinct classes:

| Class | True square-contact neighbors of T | Necessary disk / frame geometry |
| --- | --- | --- |
| **I — isolated** | \(\varnothing\) | No square-square contacts at all; T remains a genuine space-occupying square |
| **L — central leaf** | \(\{C\}\) | T has two true disk-circle vertices, is radial and frame-parallel to C; if C's two positive normals are side-aligned, the leaf lies on a perpendicular C side |
| **\(\triangle_1\)** — actual triangle | \(\{C,S_1\}\) | T has a true disk-circle vertex; the three actual pair contacts C--T, T--S1 and C--S1 form a physical contact triangle |
| **\(\triangle_6\)** — actual triangle | \(\{C,S_6\}\) | Same conclusion with S6 |

There are **no other** spectator-contact possibilities
in this root.

In particular,
\[
\boxed{
T\text{ has an actual outer-square contact}
\Longrightarrow
T\text{ also actually touches C AND touches the disk circle}.
}                                                    \tag{1}
\]
And
\[
\boxed{
T\text{ does not actually touch C}
\Longrightarrow
T\text{ is completely isolated in the actual-contact graph}.
}                                                    \tag{2}
\]

This is stronger than earlier spectator restrictions
which depended on C having exactly two or three
actual neighbors. It preserves arbitrary square
frames and all zero-positive-stress actual contacts
to internal stressed path squares.

## Proof

### 1. Outer visibility restricts T to two possible outer contacts

The all-frame outer-center angular visibility theorem
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md)
proves that outer squares can actually contact
only their circularly adjacent outer-center
ray neighbors. Since S1,...,S6
are six consecutive outer labels in the
stress normal form, the **only outer
labels T could possibly touch** are
S1 and S6.

The stressed path already contains
all five consecutive actual outer edges
S1--S2--...--S6. If T touched both
S1 and S6, those two optional actual
edges would **close the full outer
seven-contact cycle**, contradicting
the explicitly assumed actual-outer-
graph forest. Hence
\[
\#\{\text{actual outer neighbors of }T\}\le1.
\]

Because k=7, C is the **only inner
square**; there are no further
noncentral inner labels T might touch.

### 2. A spectator cannot be a noncentral actual leaf

Suppose T touched one outer endpoint,
say S1, but did **not** touch C.
The first section shows it then
has exactly **one actual
square-square neighbor**, S1,
which is a **noncentral square**.

But the exact actual-leaf theorem
[HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md)
proves in a contact-minimal radius
minimizer that *every square with
exactly one actual square contact*
must have C as its sole neighbor.
Thus the supposed T--S1-only
actual edge is impossible. The
same holds for S6.

Therefore if T does not touch C,
it touches neither S1 nor S6
and is **fully isolated**:
class I. If it has any actual
outer neighbor, it must additionally
touch C, giving the triangular
contact classes in the table.
If it touches C but neither outer
endpoint, it has exactly one actual
neighbor and is class L.

These four exhaust all actual incidence
choices and prove (2) and the contact
part of (1).

### 3. Any non-isolated spectator has a true circle vertex

If T is class L, it is an **actual
one-contact leaf**, so the same
exact leaf theorem proves it is
radial, parallel to its unique
neighbor C and touches the disk
circle at **two true vertices**.
The
[HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md](HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md)
theorem additionally forces its
normal onto a perpendicular C side
when C's two positively stressed
contact normals are side-aligned.
No perpendicular conclusion is
drawn if C's two positive normals
are diagonal.

If T is triangular class, it has
**exactly two actual square-square
neighbors**, C and one endpoint S_i,
and those neighbor squares C,S_i
already **actually touch each other**
(the pair C--S_i carries positive stress).

Suppose for contradiction T were
strictly circle-free. The contact-
minimal interior-degree-two rigidity
theorem
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md),
section 8, would then make T an
aligned two-contact transmitter.
Its two contacts have **opposite
normals** along a T side; the
two *other* neighbor squares C and
S_i would therefore be separated
by the full T width of at least
one along that normal. In particular
they would have **strictly positive
closed-square distance**, contradicting
their actual positive-stress C--S_i
contact.

Equivalently, section 9 of the
same note proves that the two
neighbors of a circle-free
actual-degree-two transmitter
are at **exact Euclidean distance
one**, whereas C and S_i are
already at distance zero.
Both statements are incompatible.

Thus T is **not circle-free** and
must have an actual vertex on
the containing circle. This
completes (1) and the table. QED.

## Exact finite contact-incidence audit

There are three candidate boolean
actual edges: T--S1, T--S6 and T--C,
giving eight raw incidence words.

* T--S1 and T--S6 **both present**:
  forbidden full outer actual cycle
  (two boolean words, with and without
  T--C).
* Exactly one outer edge with **no**
  T--C edge: forbidden noncentral
  actual leaf (two boolean words).
* The remaining **four** boolean
  words are precisely I, L,
  \(\triangle_1\), \(\triangle_6\).

[verify_m6_spectator_contact_types.py](verify_m6_spectator_contact_types.py)
enumerates these eight raw words and
checks the four exact legal contact
neighborhoods. It is **only a
finite graph cross-check**.
All geometry follows from the
true-square visibility, leaf and
transmitter hand theorems.

## Consequences and remaining global task

In the previously proved P/S/K
central actual-contact classification:

* **P** (C actual degree two)
  forces T to be **isolated**.
  This recovers the stronger
  [HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
  theorem's m6 specialization.
* **S** (C actual neighbors S1,S6,T
  only) is either spectator leaf L
  or spectator triangle \(\triangle_i\),
  with T a true circle-contact square.
* **K** (at least one C-to-internal
  path actual chord) may have
  spectator type I, L or
  \(\triangle_i\). Diagonal
  positive-stress mode additionally
  forces C to have two opposing
  tangential bracing contacts and
  at least one internal chord.

None of these combinations is asserted
geometrically realizable. They are
**exhaustive actual-contact necessary
forms for the complete eight-square
k7/B2/m6 root**. All other
structural roots and the sharp
\(R_8\ge\widehat R\) conclusion
remain OPEN; the full seven-outer
actual-contact ring equality packing
belongs to a separate root A.
