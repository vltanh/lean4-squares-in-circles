# Every stressed outer-path endpoint needs a circle contact or a spectator contact

**2026-10-12. Exact global contact-graph theorem** for all
four remaining k=7, central-two-stress, actual-outer-path
lengths m=3,4,5,6. It is not a sharp numerical radius bound.

## Theorem

Choose an eight-unit-square **least-radius minimizer with
the fewest actual square-square contacting pairs**, and
assume \(R^2\le9789/2500\). Let C be its origin-containing,
strictly circle-free central square. Assume:

* All seven exterior centers are **outer** (\(|p|\ge1\));
* their induced **actual** contact graph is a *proper*
  subgraph of the cyclic seven-center neighbor graph;
* a normalized physical stress has exactly two
  **positive-stress** C neighbors \(S_1,S_m\),
  where \(3\le m\le6\);
* **C has exactly these two actual square-contact neighbors**;
* its sole nontrivial positive-stress component is
  \[
  C-S_1-S_2-\cdots-S_m-C
  \]
  with \(S_1,\ldots,S_m\) consecutive in the
  seven outer-center-ray cyclic order.

Let \(T_{\rm left},T_{\rm right}\) denote the
immediate spectator outer labels adjacent,
respectively, to \(S_1\) and \(S_m\) on
the *complementary* outer angular arc
(they are the **same** spectator when m=6).

Then the actual square geometry forces
the **boundary-or-spectator dichotomy**
\[
\boxed{
\begin{aligned}
&S_1\text{ touches the circle }
   \quad\text{or}\quad
   S_1\text{ actually touches }T_{\rm left},\\
&S_m\text{ touches the circle }
   \quad\text{or}\quad
   S_m\text{ actually touches }T_{\rm right}.
\end{aligned}}                                        \tag{1}
\]

Furthermore:

1. The two stressed C-contact force normals are
   actual **side normals** of C. Its side frame is
   aligned with their opposite directions.
2. If **both stressed endpoints are circle-free**,
   then both endpoint-to-spectator actual contacts
   must exist. To avoid the forbidden full
   seven-outer actual cycle, **some contact between
   consecutive spectator squares must be missing**.
   In particular
   \[
   \boxed{\text{both endpoints circle-free}
          \Longrightarrow m\le5.}                \tag{2}
   \]
3. At m=5 there are exactly **two exterior
   spectator squares**, say T1,T2 in angular order
   \(S_m,T_1,T_2,S_1\). If both stressed endpoints
   are circle-free, then the entire outer
   *actual* contact graph has all seven outer
   ray-neighbor edges **except exactly T1--T2**.
   Thus it is a **single outer path using all
   seven labels**, with the missing edge precisely
   between the two spectators:
   \[
   \boxed{
   m=5,\ \text{both endpoints circle-free}
   \Longrightarrow
   S_mT_1,\ T_2S_1\ \text{actual contacts},
   \ T_1T_2\ \text{not an actual contact}.
   }                                              \tag{3}
   \]
4. For m=6 at least one stressed path endpoint
   must touch the containing circle, as proved
   separately in
   [HUMAN_M6_SPECTATOR_ENDPOINT_BOUNDARY.md](HUMAN_M6_SPECTATOR_ENDPOINT_BOUNDARY.md).
   If the unique spectator touches neither endpoint,
   **both** endpoints circle-touch.

The statements do **not** assert that any remaining
actual graph is realizable. For each m they are
genuine necessary conditions on the *whole*
eight-square packing. They are not applicable
automatically to a representative with more than
two actual C neighbors.

## Proof

### 1. C is an aligned actual-degree-two transmitter

The central square C is strictly circle-free
because it contains zero in its open interior,
so all its points have norm <sqrt2<R.

It has exactly two actual contacting neighbors
by hypothesis. The true-square
minimum-actual-contact lemma
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md),
section 8, therefore forces the two actual
separating normals to be **opposite and
parallel to a genuine C side frame normal**.
Thus C is an actual-degree-two aligned
transmitter, proving statement 1.

### 2. Either the endpoint has another outer neighbor or it must touch the circle

By outer-center angular visibility
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md),
an outer square can actually touch only
its two circularly neighboring outer
center rays. The stressed path endpoint
\(S_1\) already touches its inner-path
neighbor \(S_2\), and its **only other
possible actual outer neighbor** is the
immediate spectator \(T_{\rm left}\)
on the complementary arc.

If \(S_1\) does not actually touch
\(T_{\rm left}\), its only actual
square-square neighbors are therefore
C and \(S_2\). (There are no noncentral
inner squares when k=7.) Thus S_1 has
**exactly two actual square contacts**.

Suppose it were also strictly circle-free.
Section 8 of HUMAN_CYCLE_ANALYSIS.md would
then force S_1 to be an actual-degree-two
aligned **interior transmitter**.
But C is an *adjacent* strictly circle-free,
actual-degree-two transmitter. The
proved corollary that **two interior
transmitters cannot be adjacent below
radius 2** forbids this situation.
Hence S_1 must meet the disk boundary.
A contained square meeting the disk
boundary necessarily has a **true vertex
on the circle** (an edge-interior boundary
point with both vertices interior is
impossible by strict convexity of the disk).

The identical argument for S_m proves (1).

### 3. Both circle-free endpoints require a gap between spectators

If S_1 and S_m both have no circle
contact, (1) forces actual contacts
\(S_1-T_{\rm left}\) and
\(S_m-T_{\rm right}\).
The positive-stress outer path already
includes all \(m-1\) consecutive actual
edges among S_1,...,S_m.

There are \(7-m\) spectators along the
complementary cyclic arc. If \(m=6\)
there is exactly **one** spectator:
the two forced endpoint edges close
the full seven-outer actual cycle, contrary
to the hypothesis. Hence both endpoints
circle-free implies \(m\le5\), proving (2).

For m<=5, the two forced end edges
connect the positive path to the
first and last spectators. The only way
that the entire outer graph fails to
be the full seven-cycle is that **some
edge between consecutive spectators
is actually missing**.

For m=5 there are precisely two
spectators, and hence **just one**
spectator-spectator neighbor edge.
It must be absent. Every other outer
circular-neighbor edge already belongs
to the positive path or to one
of the two forced endpoint edges.
Therefore the actual outer graph is
the full seven-vertex path with its
single missing edge T1--T2. This proves (3).
The m=6 statement follows immediately.
QED.

## Exact finite graph count (discovery cross-check only)

For a fixed positive m-outer stressed
path, the seven cyclic outer-neighbor
edges consist of \(m-1\) forced
positive path edges and
\[
8-m
\]
optional edges along the complementary
spectator arc. Since the actual outer
graph is **not** the full seven-cycle,
not all optional edges may be present.
Thus, for each of the seven cyclic
starting placements, the number of
purely combinatorial outer actual-graph
supergraphs of that stressed path is
\[
\boxed{2^{8-m}-1.}
\]

| m | Optional actual outer edges | Templates per cyclic placement | Seven labeled cyclic placements |
| --- | ---: | ---: | ---: |
| 3 | 5 | 31 | 217 |
| 4 | 4 | 15 | 105 |
| 5 | 3 | 7 | 49 |
| 6 | 2 | 3 | 21 |
| Total | | 56 | **392** |

These **392 are graph-only templates**, NOT
feasible geometric configurations; many
may fail the required circle-boundary
dichotomy or the sharp radius inequality.
A separate exact combinatorial script
[verify_B2_endpoint_spectator_graphs.py](verify_B2_endpoint_spectator_graphs.py)
enumerates all 392 and checks the endpoint
and spectator-edge implications, without
any floating-point calculations.

## Remaining structural work

The important unresolved cases now are:

* **C has exactly two actual neighbors (side mode):**
  every stressed outer-path endpoint is either
  a true circle-contact square or it has a
  specific actual spectator contact. This
  fixes some real supports/contact witnesses.
* **C has more than two actual neighbors
  but only two positive-stress neighbors:**
  extra central contacts have weight zero.
  If the positive central axis is a
  **diagonal**, the exact
  [HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
  requires **at least two** such extra
  contacts of opposite tangential normal signs.
* **B3 central branching** and the
  *true full seven-outer actual ring* A
  still require their own global
  sharp radius inequalities.

These are structural case reductions
and contact-boundary necessities, not
proof of the unrestricted
\(R_8\ge\widehat R\), equality
classification, or a Lean theorem.
