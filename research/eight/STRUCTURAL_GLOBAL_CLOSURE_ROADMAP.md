# Structural closure roadmap: stop narrowing cap constants, finish the global four roots


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
