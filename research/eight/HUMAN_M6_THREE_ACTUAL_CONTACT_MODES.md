# Three exhaustive actual-contact modes for the surviving k=7, m=6 B2 stress path

**2026-10-12. Exact global structural case reduction.**
This note combines the new diagonal bracing theorem,
actual-leaf/transmitter rigidity, and the complete
seven-outer angular-neighbor ordering. The result
is a **three-mode decomposition of an entire global
positive-stress root**, not an interval optimization
or a proof that the root is empty.

## Theorem

Let an attained minimum-radius packing of eight
interior-disjoint genuine unit squares in a disk
\(D_R\), \(R^2\le9789/2500\), be chosen with
the **fewest actual square-square contacting pairs**
among all least-radius packings.

Assume the seven exterior unit-square centers are
outer (norm >=1), their induced *actual* contact
graph is a **proper subgraph** of the seven-center
cyclic neighbor graph, and some normalized physical
stress has **exactly two positive C neighbors**
\(S_1,S_6\). Let its unique nontrivial
positive-stress component be the actual cycle
\[
C-S_1-S_2-S_3-S_4-S_5-S_6-C,
\]
where the six S labels are consecutive in the
cyclic outer center-ray order, and T is the sole
remaining outer spectator.

Then **exactly one of the following mutually
exclusive structural modes applies:**

| Mode | Actual central contacts | Additional necessary geometry |
| --- | --- | --- |
| **P — pure transmitter** | C touches **only** the two stressed endpoints S1,S6 | Central positive normals are **side-frame** normals; **at least one** of S1,S6 has a true circle vertex |
| **S — spectator spoke** | C touches exactly S1,S6 and T, not S2–S5 | Central positive normals are **side-frame** normals; spectator T has a true circle vertex and its C–T contact has zero positive stress |
| **K — internal chord** | C touches at least one stressed internal square \(S_j\), \(2\le j\le5\), besides S1,S6 | This extra C–Sj actual contact has **zero positive stress**; it is a **real central chord** of the stressed C-rooted cycle |

Moreover, **every diagonally two-stressed central square belongs
to mode K**, and in that diagonal subcase C has
**at least four actual neighbors**: besides the
positive pair S1,S6 it has two further
zero-stress contact normals with opposite
projections onto the tangent of its stressed
central diagonal. Since T is a single
square, **at least one** of these two
required extra central contacts is with
an *internal* stressed-path label S2–S5.

All three modes are *necessary full-geometry
subcases*, not existence assertions.
The actual S4 equality packing has a
full outer actual-contact ring and belongs
to another root; it is not excluded here.

## Proof

### 1. No other possible central square labels exist

By the positive-stress cycle normal form
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md),
the two C--S1 and C--S6 contacts have positive
stress. The other exterior labels available
to C as actual-contact neighbors are exactly
\[
\{S_2,S_3,S_4,S_5,T\}.
\]
If C has no other actual neighbor, we are in P.
Otherwise, if C has **no** actual contact with
any S2–S5, every extra actual C contact must
be with T alone, so C touches exactly S1,S6,T:
mode S. If any internal S2–S5 actually
contacts C, we are in K. This is an exhaustive
and mutually exclusive partition with no
geometric inference hidden in its definitions.

Each C--T or C--S_j contact outside
S1 and S6 is **zero-positive-stress** by
the hypothesis that precisely those two
neighbor pairs have positive stress.

### 2. Mode P: at least one stressed endpoint touches the circle

C has actual degree exactly two, is
strictly inside the circle because
it contains the disk origin in its open
interior, and the packing was selected
to minimize actual contacts.

The true-square transmitter theorem
HUMAN_CYCLE_ANALYSIS.md section 8
forces its two opposite contact normals
to be **aligned with a side of C**.
The global [HUMAN_M6_SPECTATOR_ENDPOINT_BOUNDARY.md](HUMAN_M6_SPECTATOR_ENDPOINT_BOUNDARY.md)
then proves that the unique spectator T
can actually touch at most one of S1,S6.
At least one endpoint therefore has
only two actual square-square contacts:
one to C, one to its positive-stressed
outer-path neighbor. If this endpoint
were circle-free, it and C would be two
**adjacent circle-free actual-degree-two
transmitters**, prohibited by the
exact four-square straight-chain theorem.
Thus that endpoint has a true disk-circle
vertex. Mode P is established.

### 3. Mode S: the spectator must touch the containing circle

In S the only actual neighbors of C
are S1,S6 and T, with T carrying
zero positive contact weight.
The diagonal two-force case is excluded:
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
requires at least **four** actual C neighbors
and two-sided tangential bracing, whereas
C has just three. Thus the central positive
normal pair is in **side mode**, by
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md).

We prove the spectator T is actually
a *circle-contact* square.
By outer-center angular visibility,
T can actually touch **only** S1 or S6
among the outer squares. If it touched
**both**, the actual outer graph would
be the forbidden full seven-cycle.
Hence T has **at most one actual outer
neighbor**.

If T touches **neither**, its only actual
square neighbor is C: T is an actual leaf.
The global actual-leaf theorem
[HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md),
section 1, proves that in a
contact-minimal radius minimizer any
one-contact square has two true vertices
on the disk circle. Thus T touches
the circle in this case.

If T touches **exactly one** endpoint,
say S1, then T has exactly two
actual neighbors, C and S1.
Suppose toward contradiction that T
is strictly inside the containing
circle. The actual-degree-two interior
transmitter theorem
HUMAN_CYCLE_ANALYSIS.md sections 8–9
states that such a square must lie
between two **distinct neighbor squares
whose Euclidean closed-square distance
is exactly one**.
But C and S1 **already have an actual
contact**, because C--S1 is a
positive-stress edge. Hence their
closed-square distance is **zero**, not
one. Contradiction. Thus T also must
touch the disk circle in this second case.

So in *every* mode-S arrangement the
spectator T has a true circle vertex,
as claimed. No stress weight at
that circle vertex is implied:
T may still have zero chosen circle
multipliers, since T is not in the
positive-stress component.

### 4. Mode K and the diagonal implication

In K there is by definition a
genuine actual contact C--S_j
for some \(2\le j\le5\).
It has **zero** positive contact weight
because the stress assigned positive C
weights only to the two endpoint pairs.
This contact adds a *chord* from C
to an internal vertex of the true
positive-stress cycle; it must be
retained in any actual square geometry
or SAT feasibility model.

Suppose C's two opposite positive
contact normals are central-square
diagonals. The exact tangential
bracing theorem cited above forces
two additional **distinct zero-stress
actual C neighbors**, with opposite
tangent-normal signs. Since among
the non-endpoint exterior labels
there is **only one spectator T**,
at least one of those two extra
neighbors must be an internal
S2–S5 square. Therefore diagonal
positive mode implies K and a
true internal central chord.
QED.

## Why this is stronger than counting positive contacts

A computer optimizer of **only the positive
stress graph** would incorrectly permit a
"bare diagonally stressed C" with no
additional actual C contacts; the tangential
bracing theorem rules it out. It would also
allow a nonboundary isolated spectator
in mode S; true minimum-contact leaf
and transmitter rigidity rules that out.
Finally, an m6 core model in mode P
which omits the required circle-contact
endpoint violates the actual-adjacency
transmitter theorem.

**Next valid three-way computational target
for B2/k7/m6:**

* **P:** optimize true side-aligned
  C-S1/S6 contact geometry with a
  designated circle-contact path endpoint;
  retain T with its full square shape.
* **S:** force an actual zero-stress
  C-T contact and a true circle vertex
  of T, with side-mode central stress.
* **K:** force an additional
  C-S_j actual contact for an internal
  stressed-path label; in the diagonal
  subcase enforce two oppositely
  bracing zero-stress central contacts.

No local numerical optimizer output
proves that any mode is feasible,
and none of P/S/K has yet been
eliminated as a whole. A global
\(R_8\ge\widehat R\) inequality,
equality classification and Lean
formalization remain OPEN.


## Exact diagonal-mode refinements: internal zero-stress chords must brace both tangent signs

Retain all assumptions of the m=6 theorem, and suppose
C has **diagonal** positive-stress normal n.
Write \(t=Jn\). The two stressed
C--S1 and C--S6 contact points are
**opposite central vertices**.

The tangential bracing theorem implies the
following exhaustive **genuine actual-contact
requirements**, beyond merely asserting
the existence of one internal chord:

1. **T does not contact C.** Then the
   required **positive- and negative-tangent
   auxiliary contacts must be two distinct
   internal path squares** \(S_j,S_k\)
   with \(j,k\in\{2,3,4,5\}\):
   \[
   (m_j\cdot t)(m_k\cdot t)<0.
   \]
   Both C--S_j and C--S_k are
   **real zero-positive-stress actual chords**.
   A diagonal C with only one internal
   auxiliary chord is impossible.
2. **T does contact C.** The actual
   C--T contact has zero positive
   stress. If one selected genuine C--T
   normal has \(m_T\cdot t>0\), then
   at least one internal actual C--S_j
   contact must have \(m_j\cdot t<0\).
   The reverse sign requires an internal
   positive-tangent normal. If
   \(m_T\cdot t=0\), **two different
   internal path labels** with opposite
   tangential contact-normal signs
   are required instead.

All statements are necessary for **every
choice of one genuine contact normal per
auxiliary C-neighbor pair**, as required
by the original bracing theorem. In particular
the chosen SAT directions of additional
C--S_j contacts cannot all be assigned
the same tangential normal sign.

This is not an extra geometric estimate:
it is a precise **finite graph/contact-normal
specialization** of the proved global
two-sided bracing theorem. No central
diagonal mode is claimed globally impossible.
The next computational geometry model must
enforce these **actual** zero-weight chords,
not optimize only the positive stress cycle.
