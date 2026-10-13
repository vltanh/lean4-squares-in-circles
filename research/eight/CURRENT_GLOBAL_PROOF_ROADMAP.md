# Current global proof roadmap

Reorientation: 2026-10-13. Baseline audited: `605af6c522c0928d3fd1ab7b1765ed20d3e7dc1f`.

## Latest completed structural reduction: the minimal B3 branching core (October 13)

The smallest **seven-outer central-branching** positive-stress
component has exactly the triangle C-X-Y-C and positive
radial bridge C-Z. The previous graph theorem gives seven
choices of X-Y consecutive ray pair and three nonadjacent Z
ray placements (**21 labeled positive graph templates**),
all still subject to genuine eight-square geometry.

**New complete hand deductions, not a finished B3 radius bound:**

1. [HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md](HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md)
   forces **all three outer labels X,Y,Z** to have
   strictly positive **physical circle multipliers**.
   Otherwise the two forces through X or Y transmit
   straight through a unit square and separate
   its two other *contacting* neighbors, impossible.
2. [HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md)
   proves the positive radial bridge square Z has
   only two true disk-circle shapes: **side mode**
   \[
   b=\sqrt{R^2-1/4}-1,\quad p_Z=(\sqrt{R^2-1/4}-1/2)n
   \]
   with two **equal positively weighted circle vertices**,
   or **diagonal mode**
   \[
   b=R-\sqrt2,\quad p_Z=(R-1/\sqrt2)n
   \]
   with one positively weighted vertex at \(Rn\).
3. The genuine SAT-owner condition eliminates the
   false C-corner/Z-diagonal combination.
   [HUMAN_RADIAL_BRIDGE_THREE_SAT_INTERFACES.md](HUMAN_RADIAL_BRIDGE_THREE_SAT_INTERFACES.md)
   gives **exactly three** true interfaces:
   **SS** (C side/Z side, frames parallel),
   **CS** (C radial corner/Z side), and
   **SD** (C side/Z inward diagonal corner,
   frames differing by 45 degrees).
4. [HUMAN_B3_RADIAL_LEAF_ANTIPODAL_FORCE_CONE.md](HUMAN_B3_RADIAL_LEAF_ANTIPODAL_FORCE_CONE.md)
   constrains the genuine radial center ray n of Z
   to the antipodal cone of X,Y's two positively
   circle-stressed square center rays:
   \[
   \theta_X+\pi-31/80<\arg n
   <\theta_Y+\pi+31/80\pmod{2\pi}.
   \]
   The cone's width is strictly below pi.
5. In a **contact-minimal** radius minimizer,
   [HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md](HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md)
   rules out **unbraced CS and SD**. Those
   nonparallel bridges require a further **actual
   zero-positive-weight contact** to one of
   Z's two angularly adjacent spectator squares;
   that spectator may not end as a noncentral
   actual leaf.
6. In the further **all-positive-C-side-normal,
   side-mode** subcase, [HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md](HUMAN_B3_ALL_SIDE_STRESS_SCAFFOLD.md)
   proves X,Y must both contact the *opposite* C side,
   their actual C contact points must straddle
   the radial origin line in tangent sign, and
   X-Y has a transverse positive contact normal.
   The conjectured **three-distinct-C-side**
   branching case is **fully excluded under those
   explicit hypotheses**, but the opposite-side
   triangle remains.

**Next B3 handproof target:** handle complete **SS actual
leaf** versus **CS/SD externally braced** configurations,
with all four remaining full spectator squares.
Try force-cone + exact true-square triangle contacts,
not cap-cutoff tuning or incomplete stress-core optimization.
The global root A (genuine equality ring), B2 m=4..6,
B3 larger components, X and k<=6 remain open.

This is a *structural reduction*, not a claim of global
\(R_8\ge\widehat R\), equality classification or Lean completion.

---

## New B3 structural closures: opposite-face SS impossible and only complete spectator arcs (October 13)

**This section is the newest authoritative B3-small-core status.**
The positive-stress component remains the four-square
contact graph \(C-X-Y-C\) plus radial positive leaf C-Z,
with X,Y outer-ray neighbors, Z in one of three
nonneighboring ray positions, **all X,Y,Z with positive
physical circle multipliers**.

**Exact true-SAT radial bridge modes:** SS (C side/Z side),
CS (C radial corner/Z side), and SD (C side/Z diagonal).
The former fourth C-corner/Z-diagonal pair is impossible
because no genuine square side owns its separating axis.

**A complete global SS subcase is now CLOSED.**
[HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md](HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md)
proves the entire **SS with both X and Y
positively contacting C along true C side normals**
impossible. Central force balance puts both on
the opposite C side, and torque makes their contact
points straddle the radial origin line. One of
the true contacts is at \(z=(-k,\tau)\) with
\(k=2-\sqrt{R^2-1/4}\in(0,1/2)\),
\(|\tau|\le1/2\), and the corresponding
unit square lies wholly in \(x\le-k\).
The **new arbitrary-frame contact-vertex lemma**
bounds every one of its true vertex norms by
\[
|v|^2\le(k+1)^2+9/4
=R^2-(6\sqrt{R^2-1/4}-11)<R^2.
\]
It consequently has no circle vertex and no
positive circle multiplier, contradicting the
rigorous positive circle force already required
at both triangle labels X,Y. This closes that
**whole SS contact-normal subcase**, not just
another parameter interval.

**Surviving SS geometry is corner-forced.**
[HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md](HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md)
shows the X/Y positive C contact normals
must have **strictly opposite nonzero transverse
components**, touch the *top and bottom* C side
supports, and at least one positive contact
is a genuine corner of C on its side opposite Z.
[HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md](HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md)
independently proves the same strict opposed
transverse normal signs for the C-corner/Z-side
(CS) radial bridge, using radial torque and
nonzero stress moment circulation. The SD
radial bridge is **not** included in these results.

**Complete spectator arc classification in the
C-actual-degree-three representative.**
If C actually contacts **only** its three positive
neighbors X,Y,Z, then
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md](HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md)
shows every complementary outer-ray spectator
arc is either completely present or completely
absent as an *actual contact path*. A partial
arc creates a spectator actual-degree-one leaf
whose neighbor is not C, impossible in the
contact-minimal minimizer. Both arcs complete
would form the excluded full seven-outer ring.
Therefore the entire outer actual graph is
one of **three** patterns per positive stress
label triple: no spectator edges, the full Y-Z
spectator path, or the full Z-X spectator path.
There are **63** graph-only templates
(\(21\times3\)), cross-checked against all
\(21\times64=1,344\) optional-edge assignments.
For genuine **CS/SD**, a further zero-weight
spectator contact is mandatory by the
actual-leaf rigidity theorem, so **the empty
spectator path is excluded**. SS may have an
actual leaf Z in the empty-arc case.

**Remaining meaningful proof obligations:**
derive a full eight-square sharp radius inequality
for the **corner-forced SS** triangle, for the
**CS side-leaf** with a complete bracing spectator
arc, and for the **SD diagonal leaf** with
mandatory spectator bracing. If C has extra actual
zero-weight spectator neighbors, the 63-template
arc classification **does not apply**; keep those
separate actual-contact modes. B2 m4..6, the full
equality ring A, larger B3, k<=6 and exterior root X
also remain OPEN. Preserve the genuine S4/k7 equality.

The supporting hand proofs have exact symbolic
vertex identities and exhaustive finite graph
audits; neither the graph count nor any optimizer
is a global packing feasibility certificate.

---

## 1. The actual objective

Let R8 be the least radius containing eight interior-disjoint genuine unit squares, with independent orientations. The candidate construction supplies R8 <= Rhat. The remaining theorem is **R8 >= Rhat**, not impossibility at the inclusive candidate radius. The known equality packing must remain admissible.

`HUMAN_FAMILY_CLOSURE.md` proves optimality **within its specified five-corner family**. It is not a theorem that an arbitrary packing belongs to that family. Completion requires either an exact structural bridge into the family or separate sharp inequalities for every global root below. Equality classification and Lean formalization are subsequent, distinct obligations.

No additional cap-threshold improvement is a primary milestone in this roadmap.

## 2. Dependencies and what has actually been checked

The reorientation reread the physical multiplier construction in `HUMAN_CONTACT_EQUILIBRIUM.md`, the component argument in `HUMAN_CONTACT_COMPONENTS.md`, the full-domain outer graph reduction in `HUMAN_OUTER_GRAPH_REDUCTION.md`, and the scope of `HUMAN_FAMILY_CLOSURE.md`.

The physical model uses one selected genuine separating normal per actual contacting pair, nonnegative forces at actual common contact points, and nonnegative multipliers on actual disk-circle vertices. It includes force and torque balance and normalization of total circle weight to one. Additional actual contacts may have zero weight. These distinctions must survive every reduction.

These are research hand arguments, not a completed independent audit of every ancestor lemma. In particular, radius/central-square, outer angular separation, radial escape, and contact-minimal leaf/transmitter lemmas remain named dependencies. Fraction checks verify arithmetic, not those geometric implications.

For the lower bound one may select a minimizer with the fewest actual contacts, but results requiring that representative may not be applied to arbitrary minimizers. They also do not, by themselves, classify every equality packing.

## 3. The global case ledger

Fix a normalized physical stress. Test the rows in this order. They are an exhaustive organization of minimizers under the established radius ceiling, not independent lists to multiply together.

| Root | Exact remaining case | Already available | Missing decisive result |
| --- | --- | --- | --- |
| A | Full seven-outer **actual contact ring**, with central unit inside its pocket | Actual ring/winding reduction; genuine candidate in this root | Sharp bound for ring **and central unit together**, preserving equality |
| B2-7 | Seven outer centers; proper outer actual forest; central positive degree two | One positive cycle C-S1-...-Sm-C; **m=3 and m=7 excluded**; only m=4,5,6 remain | Sharp full-packing bound for each remaining stressed path **with all spectators** |
| B2-low | At least one noncentral inner center; central positive degree two | Opposite central forces; side/diagonal force axes; inner units strictly circle-free | A valid normal form that retains inner attachments; the k=7 consecutive-path classification cannot be imported |
| B3-7-small | Seven outer centers; branching central positive degree; positive component C plus exactly three exterior labels | Triangle C-X-Y-C plus radial positive bridge C-Z; 21 eligible cyclic label choices | Eliminate or sharply bound this genuine triangle/radial-leaf configuration, retaining four spectators |
| B3-7-large | Seven outer centers; central positive degree >=3; at least four exterior labels in the positive component | Central force polygon; outer-forest visibility; global circle-force angular spread | A structural bridge or sharp inequality for branching support with four through seven exterior labels |
| B3-low | Noncentral inner centers and branching central positive stress | Inner-circle clearance and actual force/torque conditions | Joint inner/outer contact structure; no k=7 forest simplification beyond its proved domain |
| X | Central unit outside the positive component; proper outer forest | Directed exterior moment cycle of 5--7 labels, at least one noncentral inner-center witness; k<=6 | Sharp bound including C and unused squares; distinguish actual-degree-two transmitters from actual-degree>=3 witnesses |

Root A takes precedence even if its chosen stress has central degree two or three. A zero-weight missing positive edge is not a missing **actual** edge.

### B2-7 in detail

Each remaining positive path has seven cyclic placements. Thus m=4,5,6 gives **21 positive graph templates**, not 21 feasible packings and not the whole remaining problem.

* **Pure central actual degree two:** the complete actual graph is the positive C-rooted cycle plus 7-m isolated spectators. Both endpoints have positive circle weights; the positive-circle support covers each internal path edge. At least 3,3,4 stressed outer labels carry positive circle weight for m=4,5,6. Isolated spectators may be chosen circle-free but remain full unit squares in every occupancy argument.
* **Side-force mode with extra actual C contacts:** retain every zero-weight central spoke/chord. The pure-contact leaf argument no longer applies automatically.
* **Diagonal-force mode:** in the contact-minimal representative, at least two auxiliary actual C contacts must brace opposite tangent directions. Neither may be omitted just because its stress weight is zero.
* **m=6 spectator:** it is isolated, a central leaf, or a circle-contacting C-T-endpoint triangle. These are necessary contact forms; none is presently a full sharp-radius proof.

The m=3 semicircle argument is recorded in `HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md`. Earlier m=3 parallel-scaffold and circle-weight notes are intermediate conditional results, not additional open branches.

### Geometric side-status filters, not a second global partition

The exclusive all-seven-single-side ledger remains:

| Type | Counts not globally excluded |
| --- | --- |
| S1 | k=3,4,5,6 |
| S2 | k=4,5,6; the nearer 2+2 pair cannot both be inner |
| S3 | k=4,5,6,7 |
| S4 | k=4,5,6,7; includes genuine equality |

D0 corner-only exceptions and D1/D2 double-side cases remain. Apply their established inequalities **inside** the global roots, with distinct-label hypotheses checked. Do not confuse S2's geometric cells A/B/C with the global stress roots A/B2/B3/X.

## 4. Work order and stopping criteria for an attempted lemma

### First: improve a complete structural support class

Use exact physical force support, actual polygon contact geometry, and the radial-bridge classification. The small branching core is particularly concrete: three stressed exterior labels, a genuine triangle, and one radial stress leaf. Search for a structural contradiction before adding more coordinate subdivisions.

For B2, seek one inequality that handles an entire m=4,5,6 class or several of them together. Every calculation must include the spectator squares when invoking eight-square occupancy. A stressed core alone is not an eight-square packing.

### Second: use computation to falsify proposed bridges

A useful diagnostic models true vertices and genuine signed SAT support inequalities. Any fixed geometric candidate must then pass a separate nonnegative force/torque feasibility check. Failure to locate a candidate proves nothing. A strict rational counterexample ends that proposed bridge and is retained as a regression test.

Promote a computer clue only after replacing it with an explicit hand argument: a finite support identity, convexity/monotonicity proof, exact polynomial positivity identity, or an exhaustive geometric contact classification. Do not present sampled minima, unsuccessful optimizer outputs, or graph-only counts as geometric exclusions.

### Third: close the equality-bearing ring and low-k roots

The full outer ring requires a central-pocket inequality. The existing outer-ring counterexamples show that omitting the central unit is invalid. The low-k roots require additional inner squares and cannot be covered by a seven-outer theorem. These tasks do not disappear even after B2-7 is closed.

## 5. Completion gates

1. Every global root above has an exact R >= Rhat inequality, or is reduced by a proved map to another root already covered.
2. Such a reduction preserves the radius, all eight genuine squares, and every hypothesis used at its destination. Moving to a contact-maximal representative does not preserve contact-minimal lemmas automatically.
3. The candidate supplies equality, and any proposed uniqueness/classification statement handles all equality freedoms rather than only a specially selected representative.
4. The resulting proof is formalized and checked in Lean without changing the mathematical statement or adding unproved axioms.

**Current status:** the unrestricted lower bound, global equality classification, and Lean proof remain open. This file replaces scattered chronological threshold summaries as the current case inventory. Subsequent progress should record the exact parent root closed and any new dependencies, rather than append another incompatible enumeration.
