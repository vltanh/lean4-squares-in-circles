# Structural closure roadmap: stop narrowing cap constants, finish the global four roots


## NEWEST force-level cycle invariant and completed m3 structural subcase

**Sharper than true disk contact geometry:**
[HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md](HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md)
proves a universal simple-positive-stress-cycle
theorem at R<2: **no two consecutive
cycle squares can both have zero physical
circle-vertex multiplier**.
Otherwise contact-force equilibrium
propagates three equal genuine
separating normals along four
distinct unit squares, which would
have projected width >=4 in
a disk of diameter 2R<4.

Thus the genuinely **positive
circle-multiplier square labels
cover the full stress cycle**.
For C-rooted cycle
C-S1-...-Sm-C with C's circle
multipliers zero, **both endpoints
S1 and Sm must have positive
circle weights**, and the internal
m−2 labels carry enough positive
weights to cover their path edges.
The minimal number of stressed
outer labels with *positive*
circle multipliers is
\[
\boxed{m=3:\ 2,\quad m=4:\ 3,\quad
m=5:\ 3,\quad m=6:\ 4.}
\]
This holds for **every B2
actual-central-contact mode**, even
if actual zero-stress internal C
chords are present. For m6 with
a spectator C leaf or triangle,
the spectator is an *additional*
distinct true circle-contact square,
so there are >=**five different
exterior circle-contact labels**.
An exact 0/1 stress-support audit
lists three minimal four-positive
m6 patterns, all including endpoints
S1 and S6.

**One more complete m3 subcase eliminated:**
[HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md](HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md)
combines those positive endpoint
circle weights with the previously
proved genuine four-parallel-square
scaffold forced if the sole
internal S2 is circle-free.
The two outer endpoint forces
are then horizontal and nonzero;
their positive circle reactions
force their transverse center
coordinates to zero, and the
two true disk-circle vertex
equations force
\(R^2=5/2\), impossible because
eight disjoint unit squares require
\(R^2\ge8/\pi>28/11>5/2\).

Hence the **entire pure-central-contact
m3 circle-free internal-scaffold
alternative is IMPOSSIBLE**.
In any surviving pure C-degree-two
m3 path, **all three** positive
path square labels actually
touch the circle. The candidate
equality-bearing full seven-outer
ring remains a separate valid root.

**Next actual global proof goal:**
Use these *positive physical
circle-force anchors* (not just
geometric disk contacts) to constrain
the force polygons and true vertex
locations of m6 P/S/K paths with
their real spectators, then the
remaining m3/m4/m5 cases.
The global \(R_8\ge\widehat R\)
is still OPEN.

---

## NEWEST complete actual-contact collapse: bare stress cycle plus isolated, circle-free spectators

**This is the strongest newly proved global contact-graph
normal form within the central-actual-degree-two root.**

[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
shows that when k=7, C has exactly two
*actual* contacts (its two positive
stress neighbors), and the outer
actual graph is not the full
seven-contact ring, **every remaining
outer spectator is completely
isolated in the actual-contact graph**.

The reason is genuinely structural,
not numeric: any nonempty **proper**
additional spectator-edge run on
the complementary seven-ray angular
arc would have a degree-one
spectator contacting a *noncentral*
square. The exact **actual-leaf theorem**
for a minimum-contact radius minimizer
says every actual leaf must instead
contact the central square. Contradiction.
Thus there are **no extra outer actual
contacts at all** beyond the positive
stressed path.

The earlier **392 graph-only possible
actual outer supergraphs** for
m=3,4,5,6 collapse in this root to
**only 28 complete actual-contact
graphs** (the seven cyclic placements
of each bare m=3,4,5,6 stressed
C-rooted cycle). The exact finite
[verify_B2_isolated_spectators.py](verify_B2_isolated_spectators.py)
audits all 364 excluded extra-edge
templates. The actual-leaf impossibility
is proved in the hand theorem, not
inferred from enumeration.

**Both stressed endpoints now MUST
touch the disk circle**, not merely
"at least one." Combine the internal
path vertex-cover theorem to get
the following minimum number of
different stressed outer squares
with true circle vertices:

| m | 3 | 4 | 5 | **6** |
| --- | ---: | ---: | ---: | ---: |
| Required stressed-path circle-contact labels | **2** | **3** | **3** | **4** |
| Actual isolated outer spectators | 4 | 3 | 2 | 1 |

[HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md](HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md)
proves a further exact **representative
normalization**: each actually isolated
outer square can be translated a tiny
distance **radially inward** until every
true vertex has strict disk clearance,
*without changing its outer-center
classification, any actual contacts,
the minimizing radius, or the physical
stress core*. Thus in this root we may
work with **all spectators both isolated
and strictly circle-free**. They still
occupy full unit-square area and must
be retained in every global inequality.

The m=3 pure-C-two-contact subcase
has a sharp **boundary-or-four-parallel**
motif: if its sole internal S2 is not
circle-contacting, the actual shared
two-transmitter theorem forces
**C,S1,S2,S3 all parallel**.
No parallelism assumption was made.

### Even more precise m=6 spectator incidence

[HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md](HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md)
proves for the *entire* k7/B2/m6
root, **regardless of C actual degree**,
that the unique spectator T is exactly
one of:

1. **Actually isolated.**
2. An **actual central leaf** C--T,
   with radial, C-parallel true unit
   frame and two disk-circle vertices;
   in side-positive C mode the leaf
   points along a **perpendicular** side.
3. An **actual contact triangle**
   C--T--S1--C or C--T--S6--C;
   T has a true circle vertex.

No outer-only T leaf is possible, by
the global actual-leaf theorem, and
contacting both path endpoints would
form the excluded full actual ring.
An exact 3-bit graph audit reduces
8 candidate contact words to 4
labeled legal incidences.

The existing P/S/K actual central
contact modes can now be sharpened:

* **P:** C actual-degree-two,
  T actually isolated and (by choice)
  circle-free; **both** stressed
  path endpoints and at least
  **two internal path squares**
  circle-touch. At least **four
  distinct stressed outer squares**
  touch the circle.
* **S:** the extra actual C contact
  is to T alone, which is a leaf
  or circle-anchored triangle.
  At least two internal stressed
  path squares also circle-touch.
* **K:** a real C-to-internal
  zero-stress chord exists; all
  internal boundary-or-chord vertex
  cover constraints remain, and
  diagonal positive mode forces
  two-sided auxiliary C bracing.

**Next decisive proof goal:** derive a sharp
global radius lower bound for **P with
four true boundary-anchored stressed
outer squares plus an isolated circle-free
spectator**, or close the S0
perpendicular radial leaf geometry.
The missing inequality must retain the
spectator's full square and the entire
central pocket. This is now an
explicit global support-contact
problem, not a local offset gap.

---

## LATEST structural invariant: internal path boundary-or-chord vertex cover

**This is the current first proof gate**, stronger than the
older P/S/K case split below:

[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md)
proves, for the *entire* k=7, two-positively-stressed-C
root with any stressed outer path size \(m=3,4,5,6\),
that each internal stressed path square either
(a) has a true disk-circle contact or
(b) has an **actual** zero-positive-stress C contact
chord, **unless** it is a circle-free
actual-degree-two aligned transmitter.
Two consecutive internal vertices cannot both
be unanchored transmitters. Consequently
the **true boundary-or-chord anchors form a
vertex cover** of the path of m-2
internal stressed vertices.

The exact minimum number of required anchored
internal labels is respectively
\[
m=3:\ 0;\qquad m=4:\ 1;\quad
m=5:\ 1;\quad m=6:\ 2.
\]
This combinatorics is audited by the
exact 0/1 vertex-cover enumerator
[verify_B2_internal_path_vertex_cover.py](verify_B2_internal_path_vertex_cover.py);
the all-frame geometric proof is the existing
*actual-contact* transmitter rigidity.

**New global m=6 consequences:**

* **P, C actual degree two:** no C-internal chords;
  **at least two distinct S2..S5 circle-contact squares**,
  plus **at least one of S1,S6 circle-contact**.
  Hence **three or more true circle-contact
  stressed outer labels**.
* **S, C actual neighbor spectator T:** also
  no C-internal chords, so **at least two
  circle-contact internal stressed labels**
  plus **the circle-contact spectator T**.
  Hence three or more true circle-contact
  exterior squares. In S0, the leaf T
  additionally has two true circle vertices,
  is radial and frame-parallel to C, and
  lies on a **perpendicular C side**.
* **K, internal actual central chord:**
  among S2..S5 **at least two different
  indices** must have either a real
  C chord or a true circle vertex.
  In particular a single C-internal
  chord forces a **separate internal
  circle-contact label** (unless
  further central chords are present).
  In diagonal positive-stress mode
  the two additional bracing contacts
  have opposing tangential normal signs.

**New global m=3 scaffold gate:** when C has
exactly two *actual* contacts, if its sole
internal stressed square S2 does not touch
the circle, C and S2 are two separate
circle-free actual-degree-two
transmitters with the **same two
outer neighbors S1,S3**. The exact
shared-transmitter theorem then forces
**all four frames C,S1,S2,S3 parallel**,
a genuine candidate-like four-square
scaffold. Thus m3 necessarily has
an internal circle anchor **or**
a proven four-parallel-square motif,
with no frame ansatz.

**The next proof target is now genuinely
global:** derive a sharp bound
\(R\ge\widehat R\) from the *minimum
three circle-contact squares* in the
m6 pure/spectator modes, or from the
forced internal zero-stress chord(s)
in K. For m3, combine the forced
parallel scaffold with the **other
four actual square labels**, using the
already proved conditional five-corner
optimum without discarding spectators.
Do not optimize more tiny cap offsets.

---

## CURRENT structural frontier: finite central normals and P/S/K modes for k=7/B2/m=6

**This section supersedes the older first-priority m=6
discussion below, which lacked the newly proved
actual-contact rigidity. No global root is now
being declared closed.**

**Step 1 — Central positive two-force axis is finite.**
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md)
uses *true physical force and torque equilibrium*
to prove that if C has exactly two positive
contact-neighbor labels, the opposite force normals
lie on **one of only four central-frame unoriented
axes**: the two side normals or the two
diagonals. The two aggregated C contact points
form either a same-transverse-coordinate chord
between opposite **sides** of C, or the
two **opposite vertices** of C. No other
oblique central-force orientation is possible.

**Step 2 — Diagonal two-force contact is not a bare two-spoke core.**
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
proves that in a **minimum-actual-contact
radius minimizer**, diagonally positive C
degree two requires **at least four
distinct actual C-contact neighbors**,
with at least two *zero-positive-stress*
extra contacts whose true selected
contact normals brace the diagonal's
tangent from **opposite signs**.
The proof rotates C to open the two
opposite-corner stressed contacts and
translates it tangentially to open all
contacts if those auxiliary normal
signs were one-sided. Thus diagonal
C-positive-degree-two with zero or one
extra actual C contact is **fully impossible**.

**Step 3 — All remaining outer path endpoints have actual boundary obligations.**
[HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md](HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md)
proves that for k=7, positive C degree two,
**actual C degree two**, and positive
stressed cycle outer length
\(m=3,4,5,6\), *each* stressed path
endpoint must have **either**
a true disk-circle contact **or**
an additional actual contact with the
immediately adjacent spectator.
Both endpoints circle-free requires
\(m\le5\). For m=5 it forces the
outer actual graph to be a seven-vertex
path missing **exactly** the edge
between the two spectator squares.
The exact graph enumerator
[verify_B2_endpoint_spectator_graphs.py](verify_B2_endpoint_spectator_graphs.py)
cross-checks 392 purely combinatorial
outer-actual-contact supergraphs:
217,105,49,21 for m=3,4,5,6,
respectively. These are not feasible
packing certificates.

**Step 4 — m=6 is now an exhaustive three-mode whole-contact root.**
[HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md](HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md)
reduces the k7/B2 m6 stressed path
plus its one real spectator to:

| Mode | Forced *actual* C contacts | New real geometry |
| --- | --- | --- |
| **P — pure transmitter** | Exactly the two positive stressed path endpoints | C true **side** mode; at least one endpoint has a true disk-circle vertex |
| **S — spectator spoke** | Exactly the two endpoints **plus the spectator T** | C side mode; T is **true circle-contacting**, even though its positive stress is zero |
| **K — internal chord** | At least one additional **internal** stressed-path square S2..S5 touches C | True zero-stress C--S_j chord; in diagonal mode at least **two extra C contacts** with opposite tangential normal signs |

For **S0**, the spectator T is an actual
one-contact C-leaf. Then
[HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md](HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md)
and [HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md](HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md)
force its side normal **perpendicular**
to the two opposite positively stressed
C sides, with its own frame **parallel**
to C, center radial in that direction
and two actual circle vertices.
The other spectator-spoke case S1
has T contacting C and one stressed
outer endpoint; T still has a true
circle vertex but no parallelism
assumption may be made.

If C is **diagonally stressed in m6**,
it must be mode K, with at least
one internal zero-stress chord; when
the spectator T does not also
touch C, there must be **two distinct
internal chords of opposing tangential
normal signs**. The actual zero-weight
contacts are geometric obligations,
not optional edges to discard from
an optimizer.

### Next decisive handproof targets, in order

1. **S0 orthogonal leaf scaffold.** Exploit the
   *exact radial/frame leaf geometry*,
   two perpendicular central side
   directions, two opposite positive
   stressed C neighbors, and five
   successive true outer pair contacts.
   Derive a sharp seven-plus-one pocket
   inequality \(R\ge\widehat R\)
   or a strict contradiction below the
   candidate; retain all eight units.
2. **P endpoint-boundary support.** Use at least
   one forced true circle vertex at a
   stressed endpoint and the side-aligned
   central transmitter to derive a
   five-corner length/angle inequality
   for the full six-outer stressed path
   plus its spectator.
3. **S1 boundary spectator triangle.** T has a
   circle vertex and forms an actual
   C--T--S_i--C contact triangle with a
   stressed endpoint. Determine the
   exact rotated-square support inequality
   that constrains this triangle plus the
   remaining path.
4. **K internal-chord rigidity.** Use real
   C--S_j zero-stress chords to split the
   stressed outer-path cycle into smaller
   *actual* cycles; prove these are incompatible
   with the sharp radius or force the
   five-corner support family. In diagonal
   mode enforce the two-sided tangential
   bracing theorem, not a bare two-spoke
   diagonal model.
5. Then return to **m=5,4,3**, true ring A,
   central branching B3, exterior witness X
   and k<=6. These are separate global
   obligations, not automatically
   covered by any m6 result.

**Research standard:** the next *major*
success should close **one of P/S/K entirely**,
or prove a radius inequality common to
several roots. More local cap-constant
improvements alone should not be counted
as progress toward the unrestricted
optimality theorem.


**Working target:** prove the sharp unrestricted lower bound
\[
\boxed{R_8\ge\widehat R}
\]
for every packing of eight genuine unit squares,
classify equality, then formalize in Lean 4.

**Status, 2026-10-12:** the inequality above remains **OPEN**.
This roadmap supersedes the strategy of indefinitely improving
\(h=0.37,0.316,\ldots\) in a local two-square cap.
The sharp five-corner *conditional* optimum
is already proved in HUMAN_FAMILY_CLOSURE.md,
but the **structural implication** from
arbitrary configurations is missing.

## 1. The exhaustive proof roots are now genuinely structural

[HUMAN_GLOBAL_STRESS_ROOTS.md](HUMAN_GLOBAL_STRESS_ROOTS.md)
proves a four-root partition for *any attained minimizer*
under \(R^2\le q_+=9789/2500\),
via actual contacts, positive force equilibrium,
and genuine nonzero contact-moment cycles:

| Root | What must be proved globally | Current exact result |
| --- | --- | --- |
| **A — outer ring** | Full seven-outer **actual contact cycle**, enclosing central C | Genuine sharp equality packing belongs here; **must not be excluded at equality** |
| **B2 — central two-force** | C belongs to positive-stress core and has degree 2 | Two opposite support normals; for k=7 and outer actual **paths**, only m=3,4,5,6 stressed outer-path lengths remain |
| **B3 — central branching** | C has >=3 positive-stress neighbors with force balance | No alignment/two-spoke assumption is valid; positive normal cone contains zero |
| **X — exterior stress cycle** | C is outside positive-stress core | Stressed exterior cycle of 5–7 labels has at least one **noncentral inner-center witness**, strictly circle-free |

[HUMAN_EXTERIOR_STRESS_INNER_WITNESS.md](HUMAN_EXTERIOR_STRESS_INNER_WITNESS.md)
proves that the root-X witness has
\(1/2<|p|<1\), strictly positive disk
slack, and >=2 stressed contacts.
In a **minimum-actual-contact** radius minimizer,
if that witness has **exactly two actual**
contacts, its own square frame is aligned to the
two opposite contact normals and its neighbors
have exact distance 1. If it has >=3
actual contacts, retain the *branching* case:
positive-degree two alone is not enough.

These roots are a **theorem-supported case partition**,
not a numerical guess. The old twelve-status
D0/D1/D2 and S1..S4 flags are available *inside*
the roots, but they must not be multiplied into
millions of independent claims of realizable packings.

## 2. The first real global stress subcase is now closed

[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
proves that when k=7, the outer actual graph is a
forest and C has exactly two positive stress
neighbors, the nontrivial positive graph is
**one C-rooted cycle**
\[
C-S_1-\cdots-S_m-C,\qquad m=3,4,5,6,7.
\]
Positive noncentral edges cannot be dangling tails,
because each carries nonzero moment and moment
conservation puts it on a directed cycle through C.

A standalone pure-Python enumeration of all
proper subgraphs of the seven-center cycle
independently finds seven cyclic supports per m,
35 before geometry. The hand proof obtains
the same count without using enumeration
as a geometric feasibility oracle.

**Major new complete subcase elimination:**
[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md)
proves using only actual opposite central supports,
the established \(h\ge2/5\) *one-square*
cap envelope and four rational offset bands:
\[
\angle(p_A,p_B)>\pi/2+1/13.
\]
This is a **uniform true-square and whole-configuration
constraint**, not a one-sided local cap threshold.

[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md)
then eliminates the entire **m=7** centrally
two-stressed outer-path root: six actual
successive outer center pairs force the
seventh missing angular gap
\(<\pi/2+3/250\), incompatible
with the opposite-central lower bound.

Thus **only 28 cyclic graph supports**, m=3..6,
remain in the k7/B2/actual-path root.
This is not the entire global n=8 theorem;
but it is an actual whole stress-support
macro-branch exclusion, beyond another tiny
numerical threshold.

## 3. Ranked computer-assisted attacks with exact hand-proof outputs

### Priority 1: B2, k=7, stressed path m=6 (one spectator)

* **Finite support templates:** seven choices of
  a six-outer stressed path attached twice to C.
  The seventh outer square is a genuine
  **zero-positive-stress spectator**, but can
  have actual zero-weight contacts or circle contact.
* **Computer task:** optimize **all eight true square
  centers, frames and vertices**, with exact
  C-to-path contact normals opposite, five
  consecutive true outer contacts, and the
  spectator's full disk/pair SAT constraints.
  Search first for a minimum strictly below
  \(q_+\) or the sharp \(\widehat R^2\), and record
  which SAT/contact normals bind. Do *not* omit
  the spectator or claim its zero weight means zero area.
* **Hand goal:** show either this entire m=6 case
  has \(R\ge\widehat R\), or derive a
  uniform support/contact inequality reducing
  it to a shorter chain plus spectator
  with the same global sharp bound.

### Priority 2: B2, k=7, m=5,4,3 (two–four spectators)

* **Computation:** use the same stress-normalized
  model with 7 cyclic placements per m; index
  the spectator rays in the complementary outer
  angular arc, and check all 28 pair SAT
  disjunctions on the **actual eight squares**.
* **Hand goal:** find a single sharp
  angular-winding/central-pocket inequality
  that treats all m<7 with their required
  spectators. Do not prove an inequality
  merely for the m+1 stressed core and
  discard the other squares.

### Priority 3: A, full seven-outer actual-contact cycle (equality root)

* **Computation:** optimize the **actual seven-contact
  ring plus the central square**, and inspect
  the central pocket and contact normals.
  Preserve the candidate's valid orientation
  and slider family. Use circle vertex
  constraints and a true separating-axis
  certificate for every pair.
* **Hand goal:** prove a universal sharp
  radius bound \(R\ge\widehat R\)
  **without ruling out the equality packing**;
  equality should force the previously
  established five-corner family hypotheses
  (or another exact classification).

### Priority 4: B3, central positive-stress degree >=3

* **Computer task:** solve the central force polygon
  \(\sum_i\lambda_i n_i=0\), \(\lambda_i>0\),
  simultaneously with true square contacts.
  Disallow any SAT owner assignment not
  supported by an actual contact point.
* **Hand goal:** classify genuine central
  branching, reduce to a five-corner
  support inequality or show
  \(R\ge\widehat R\) by an independent route.
  The candidate can have **four actual central
  contacts**; positive and actual degrees must
  never be conflated.

### Priority 5: X, exterior moment cycle with a circle-free inner witness

* **Computation:** enumerate true exterior
  directed moment-cycle lengths 5, 6, 7.
  Record whether the noncentral inner
  witness has two **actual** neighbors
  (then its frame is a forced aligned
  transmitter) or >=3 (branching).
  Include C and every unused square
  in the packing constraints.
* **Hand goal:** prove the sharp bound
  from the inner transmitter geometry
  and angular winding, or close the
  >=3 actual-degree subcase separately.

### Priority 6: B2/B3 with k<=6

At least one noncentral exterior square is
inner. The k7 graph normal form cannot
be copied to this setting. Enumerate
the extra inner labels on contact/moment
cycles explicitly and retain their
full square frames. Apply existing
corner-status/whole-cap tools *after*
root classification. Derive one global
five-corner bridge, not more marginal
cap cutoff shifts.

## 4. Reproducible computational pipeline

A valid **discovery program**, not a proof oracle,
should use the following data:

1. **Actual shapes:** eight centers \(p_i\), eight
   unit-square frames \((e_i,f_i)\), and **all
   32 true disk vertices**.
2. **True SAT nonoverlap:** for each of the 28
   unordered square pairs, require at least
   one genuine owner normal from
   \(\pm e_i,\pm f_i,\pm e_j,\pm f_j\).
   Keep owner/sign disjunctions explicit.
3. **Actual contact witnesses:** a designated
   stressed edge must have a real shared
   support point/segment and zero true
   signed projection gap, not just center
   distance one or adjacency in a guessed graph.
4. **Actual stress:** positive square-pair
   multipliers, disk-vertex multipliers,
   center force balance and torque balance.
   For a frozen geometry solve the stress
   feasibility equations separately,
   e.g. a rational or high-precision LP.
   A geometrically feasible packing
   without such stress **does not realize**
   that stress-root minimizer.
5. **Circle and center classes:** retain
   genuine outer norm \(\ge1\), true
   circle contact/slack and the central
   square's origin-containing condition.
6. **Diagnostics and certificates:** distinguish
   a local optimizer candidate (with full
   residual report), a strict rational
   counterexample (true vertices and 28
   SAT certificates), and a hand theorem
   covering every continuous frame/position
   domain. Never promote a local numeric
   minimum or an LP feasibility guess
   directly to a sharp lower bound.

**Suggested implementation order:**
start with m=6 B2 (one spectator), use a
continuation sweep in q and allow all frame
tilts, inspect binding SAT normals and
dual contact multipliers; then search for
an exact inequality with a small
rational endpoint or polynomial certificate.
Apply the same template to m=5..3 before
investigating more combinatorial status words.

## 5. Required mathematical exit gates

The research is **not complete** until:

* Every A, B2, B3 and X minimizer root,
  including all k<=6 and legitimate
  equality configurations, has an
  exact sharp lower bound \(R\ge\widehat R\).
* The bound is attained by the already
  certified five-corner construction,
  and all equality cases are understood
  with the correct square-frame
  and slider freedoms.
* Each invoked geometric claim has a
  full-domain hand argument; every
  computer-derived coefficient is
  rationally certifiable, and every
  zero-stress contact distinction is
  maintained.
* The final mathematics is translated
  into actual Lean 4 theorems and
  checked end-to-end.

**Latest status:** global stress-root
decomposition complete; k7/B2 stress
normal form proved; **m=7 path support
completely excluded**, leaving m=3..6
(28 cyclic supports) in that particular
structural subbranch. All other roots
and the unrestricted theorem remain OPEN.
The real S4/k7 equality cycle is
still a valid and indispensable root-A
configuration.
