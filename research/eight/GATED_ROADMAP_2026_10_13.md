# Gate 3B.2 / M5-DIFFUSE: new owner structure and exact boundary audit (2026-10-13)

**CURRENT GATE STILL OPEN.** A hypothetical eight-square packing at `q<=9789/2500` must be in M5-DIFFUSE `J>3/1000`, since the complete exact 3+5 and 4+4 certificates already exclude every small-J reference family. See [the fixed-frame proof replay](GATE3B_M5_HIGH_4PLUS4_CERTIFICATE_REPLAY.md) and [the low reference theorem](GATE3B_M5_LOW_EXACT_CERTIFICATE.md). The compressed 4+4 roots remain a separate research archive, not committed in this GitHub branch.

**New complete global structural theorem:** [GATE3B_M5_DIFFUSE_SEVEN_RATIONAL_ORDERS.md](GATE3B_M5_DIFFUSE_SEVEN_RATIONAL_ORDERS.md) uses fourteen exactly rational Pythagorean unit directions, identifies seven opposite-ray owner graphs, and proves that every such graph has no directed path of FOUR edges for any actual eight-square packing under `q<=9789/2500`. Every edge retains its genuine canonical SAT width and all seven orders share the same centers. The center-free frame-dependent path inequality also rules out THREE-edge owner paths whose three canonical normals lie in a common `1/100`-radian cone. These are whole-family necessary conditions, not one sampled angular box. [Exact regression](verify_seven_rational_projection_orders.py) passed the rational fan, a word that evades the old four-DAG path screen but fails the new one, and all 32 vertices/28 SAT pairs of an actual rational n8 packing.

**New intrinsic structural identity:** [GATE3B_M5_INTRINSIC_JENSEN_DEFECT.md](GATE3B_M5_INTRINSIC_JENSEN_DEFECT.md) proves that the odd folded barycentric weight is precisely the measure of half-circle starting positions with exactly four frames in the window. Consequently both `J=W-W0-c*A` and folded pair variance `V` are invariant under rotation, legitimate maximizing reanchoring, relabeling and reflection—even at angular ties. The remaining `J>3/1000` domain is not a normalization artifact.

**Important exact counter-control:** [GATE3B_M5_DIFFUSE_EXACT_POSITIVE_CONTROL.md](GATE3B_M5_DIFFUSE_EXACT_POSITIVE_CONTROL.md) and [its Fraction verifier](verify_m5_diffuse_rational_positive.py) supply a full eight-square M5-I packing at `q<397/100` with all 28 genuine strict SAT gaps, all 32 true vertices, `J>1/120>3/1000`, and seven order graph depths `(2,0,2,2,1,2,0)`. This is ABOVE the research radius ceiling, not a counterexample to `R_8>=R_*`. It demonstrates that graph pruning plus the J condition alone is not a complete disk obstruction; the strict radius ceiling and actual whole-square geometry are essential.

**NEXT MATHEMATICAL EXIT:** exploit the seven-order graph restrictions, exact endpoint disk support/path inequality, exterior marker/central core and real square SAT geometry to cover or exclude the entire M5-DIFFUSE domain at `q<=9789/2500`. In particular, a center-free Farkas rejection of isolated owner words, a positive control above the ceiling, or a finite cover without complete termination does NOT pass Gate 3B.2. Do not proceed to M6--M8, claim global sharpness, or merge. No Lean or CI.

---

# Current definitive n=8 proof frontier (2026-10-13, later continuation)

**Gate 3B.2 / M5 is STILL OPEN, but both small-J reference branches are now excluded by exact finite certificates.** New checked result: [GATE3B_M5_HIGH_4PLUS4_CERTIFICATE_REPLAY.md](GATE3B_M5_HIGH_4PLUS4_CERTIFICATE_REPLAY.md) proves the exact 4+4 two-frame reference impossibility at R=198869/100000, including all center arrangements, via 66 complete D4 roots and 64,067 exact rational contradiction leaves. The solver-independent checker [verify_m5_fourfour_certificate.py](verify_m5_fourfour_certificate.py), geometry model [m5_fourfour_exact_model.py](m5_fourfour_exact_model.py), and mutation tests [verify_m5_fourfour_mutations.py](verify_m5_fourfour_mutations.py) have been committed. Full compressed proof-root archive is an accompanying download, **not yet stored in GitHub**; this GitHub documentation alone is NOT a standalone replayable certificate.

Together with the already completed 3+5 LOW theorem and the full-domain M5 Jensen reduction, **any hypothetical M5 packing at squared radius q<=9789/2500 must satisfy**

    J > 3/1000,
    V > 3*sqrt(2)/500,

where J is the strong Jensen defect relative to the eight folded two-frame cut configurations and V is the corresponding pairwise folded-angle variance. All J<=3/1000 cases, including their boundary and both even 3+5 and odd 4+4 nearest cuts, are now excluded. HIGH defined only by the earlier W surplus is NOT the active frontier.

**Next active gate: M5-DIFFUSE, J>3/1000.** Keep both folded M5 angular types, all eight true orientations, all 32 actual disk vertices, every one of 28 true SAT pair disjunctions, and possible canonical owner ties. Do not claim that V>3sqrt(2)/500 is sufficient or equivalent to J>3/1000. No full continuous center/angle cover of DIFFUSE exists yet; Gate 3B.2, M6--M8, global R_8>=R_* and equality are open. The equality-bearing S4/k7 ring and sliders must be retained. No Lean, CI or merge.

---

# Previous decision: M5-DIFFUSE is the only remaining M5 child (2026-10-13)

**The unrestricted sharp radius remains OPEN.** This note retains the historical status below as a chronology; the present current M5 state supersedes its earlier references to LOW and small-J HIGH as unresolved.

* `GATE3B_M5_GLOBAL_SUPPORT_SURPLUS.md` and `GATE3B_M5_SURPLUS_CIRCLE_SPLIT.md`: true full-M5 support/Jensen reductions, independent of original owner selection.
* `GATE3B_M5_LOW_EXACT_CERTIFICATE.md`: complete exact **3+5** reference exclusion at radius `198869/100000`, computer-assisted with exact rational replay; LOW excluded.
* `GATE3B_M5_HIGH_JENSEN_EVEN_EXCLUSION.md`: any folded M5 configuration with `J<=3/1000` is within `1/200` radians of a single even 3+5 or odd 4+4 exact cut, and yields an actual reference packing at `q_ref<=3.95485389` by whole-square inscription.
* `GATE3B_M5_HIGH_4PLUS4_EXACT_COVER.md`: a new complete **4+4** exact rational certificate, 66 D4 order roots, 73,210 replayed nodes, 64,067 contradiction leaves. Full 66-root proof data and independent verifier have been delivered in conversation archive `n8_m5_high_fourfour_exact_certificate.zip` but are **not yet stored on this PR branch**. This closes the odd small-J child, conditional on that independently replayed data.
* `GATE3B_M5_HIGH_RING_BUDGET_AND_NO_GO.md`: every seven-frame cycle in M5 has width-excess at least `sqrt(2)-1`, but a uniform additional term proportional to whole-pair HIGH surplus cannot be deduced from orientations alone.

**Current only unresolved M5 branch:** `J>3/1000` (M5-DIFFUSE), with both folded types, all actual disk vertices, 28 true SAT disjunctions, and no assumed central geometry or selected chain. A necessary consequence is `V>3sqrt(2)/500`, **not an equivalent definition**. M5 cannot be closed until this branch is excluded or classified with sharp bounds. Then proceed through M6, M7, M8, global coverage/optimality, and equality. No production Lean, CI, compilation, merge or global theorem claim.

The new 4+4 certificate was replayed in full twice without SciPy/NumPy in its checker; five proof-data mutations were rejected. A rational-center positive 4+4 regression above the excluded radius passes all true vertices and 28 SAT pairs and the necessary model in an actual D4-root class. The exact archive (66 root objects, code, logs and SHA256 manifest) is a required part of the computer-assisted proof.

## Gate 3B.2 / M5-DIFFUSE: next structural decision

The positive-width exclusions now cover ALL M5 frames with Jensen defect `J<=3/1000`, including the 3+5 and 4+4 cut neighborhoods. Exact independent 4+4 proof data are delivered separately from this PR; see the note above.

The active remaining condition is `J>3/1000`, **not** just `V>3sqrt(2)/500`. The latter is necessary but weaker.

**New exact obstruction to a plausible shortcut:** `GATE3B_M5_DIFFUSE_CENTRAL_OUTLIER_NO_GO.md` constructs strict M5 orientation data with `J>1/5` where, after omitting a particular label, the seven remaining frames approach a 3+4 two-phase ring and their cyclic width excess tends to the sharp baseline `sqrt(2)-1`. Hence one cannot charge ANY fixed positive multiple of the entire J to the seven exterior ring widths from orientation combinatorics alone.

**Next proof obligation:** use actual central-square containment/avoidance and all real disk vertices to treat central-frame outliers. For a given center label `c`, the exact pair Jensen decomposition gives `J=J_exterior+J_center`. The structural split `J_exterior>3/2000` or `J_center>3/2000` is exhaustive, but neither child is excluded. Do NOT infer an exterior ring bound from this dichotomy without a geometric matching of the physical angular order.

No sharp `R_8>=R_*`, equality classification, or full M5 exit is established. Do not proceed to M6 as though M5 had closed.

---

# Sequential gates for the unrestricted n=8 proof

Date: 2026-10-13. Initial reorientation head: `ce35213455ad9d0715db88d7a732b380d6436f3d`.
This continuation started at `f093f234c979ee2a5696630e08bb6d83575a9c9c`.
Scope: PR #9, `research/eight/**` only. Pen-and-paper research; no Lean or CI.

**This is the authoritative active work queue.** It replaces older work
queues without retracting their valid conditional results. Advance only
when the stated exit theorem is proved. A subfamily exclusion does not
close a gate about an entire domain.

## Current status

| Gate | Requirement | Status |
|---|---|---|
| 1 | Exact exhaustive seven-angle actual-square domain | PASSED |
| 2 | Complete sparse center-fiber alternatives | PASSED |
| 3A | First owner-complete structural reduction | PASSED |
| 3B.1 | Exhaustive M5--M8 frame-majority cover | PASSED |
| 3B.2 | Joint owner-family classification, starting with M5 | ACTIVE / OPEN |
| 3C | Exhaustiveness and usability of final survivor list | WAITING |
| 4 | Sharp bounds on every surviving continuous family | WAITING |
| 5 | Assemble unrestricted optimality | WAITING |
| 6 | Global equality and later formalization handoff | WAITING |

**The unrestricted lower bound R_8>=R_* is NOT proved.**
New progress inside M5: its angular order has two exhaustive normal forms;
a full near-two-frame oblique-chain separator family is excluded by
circle curvature; a projection-only closure route is disproved by exact
actual-square examples. The remaining M5 center/owner classification is
not complete, so do not advance to M6.

## Target and baseline

Let q_*=R_*^2 be the exact five-corner family optimum selected by the
construction and family-closure notes. The actual eight-square construction
has R_* approximately 1.97877086534. The missing theorem is that every
packing of eight interior-disjoint unit squares has R^2>=q_*.

Do not replace the exact target by a rounded decimal. The larger ceiling
Q=9789/2500 is a convenient domain for strict exclusions, not the optimum.
Equality classification is separate from the lower-bound objective.

Previous inputs include the exact construction, sharp conditional family
bound, genuine local pose sharpness with independent frames, and exact
fixed-angle/owner convex center fibers. Individual owner/Farkas boxes do
not cover their union. Exact contacts and frame alignment may not be
assumed for arbitrary near-sharp packings. This is not an assertion that
every historical note has been independently re-audited.

## Gate 1 — exact exhaustive domain: PASSED

`GATE1_ORDERED_RATIONAL_GLOBAL_MODEL.md` represents every packing on

    z_1=0<=z_2<=...<=z_8<=1,

with seven relative half-tangent angles after removing common rotation.
All 32 true vertex inequalities and all 28 eight-way SAT disjunctions
have positive-denominator polynomial forms. The proof retains frame ties,
quarter-turn duplicates, tangencies, both directions of representation,
and compact attainment below Q. It gives no sharp radius bound by itself.

## Gate 2 — complete original-fiber alternatives: PASSED

`GATE2_COMPLETE_SPARSE_FIBER_ALTERNATIVE.md` proves for every fixed frame
and full original true-SAT owner word:

* an infeasible separator system has a positive force certificate on at
  most 15 edges, or at most 2m-1 on m labels;
* otherwise its attained optimal dual uses at most 17 total vertex and
  separator constraints;
* zero-anchor forces must balance, rather than being silently dropped;
* strict exclusions admit rational positive-anchor witnesses stable in
  relative angular neighborhoods, using
  D_epsilon>=(1-epsilon)D+epsilon/2;
* a local minimum propagates over its same-frame convex fiber, not
  automatically over a positive-width angular neighborhood.

The sparse optimal support count need not survive regularization. Finite
strict-cover existence is conditional on already proving the strict bound
throughout the covered compact set; it is not a sharpness proof.

## Gate 3A — canonical owners and four orders: PASSED

`GATE3A_CANONICAL_OWNER_FOUR_ORDERS.md` proves that every packing can use
maximum-projection true SAT owners without changing the squares. With
all ties retained, a canonical normal n and center difference d satisfy

    n dot d >= |Jn dot d|.

Their octants give four jointly realized center projection orders in
(12,5), (5,12), (-5,12), (-12,5). Every directed edge has gap >=7w>=7.
Opposite octants are merged with reversed arrows. Every graph is acyclic
and has no six-edge path under Q. Positive cross-order force balances
exclude whole coarse families.

**New limitation now proved:** even these joint orders together with exact
M5 maximality, all actual square nonoverlap conditions, and all four
FULL-SQUARE strip bounds admit the exact radius-191/100 strip example.
Thus they are useful pruning constraints, not a sufficient route to M5
exclusion without retaining actual disk curvature.

## Gate 3B.1 — frame-majority cover: PASSED

`GATE3B_FOUR_FRAME_MAJORITY_BRANCHES.md` gives an orientation window of
45 degrees containing at least five frames: sum_i M_i>=8+28=36.
Choose a maximizing anchor and call the frames inside its window L,
with remaining frames H. The four broad branches are

| Branch | L / H | L-L pairs, orders 0/2 | H-H pairs, orders 1/3 | Mixed pairs |
|---|---|---:|---:|---:|
| M5 | 5 / 3 | 10 | 3 | 15 |
| M6 | 6 / 2 | 15 | 1 | 12 |
| M7 | 7 / 1 | 21 | 0 | 7 |
| M8 | 8 / 0 | 28 | 0 | 0 |

The two allowed orders within either group are orthogonal. These are
exhaustive broad branches, not already solved cases. Closed chamber
inequalities overlap at 45-degree ties and alone do not imply maximum
window count. M8 retains the known sharp construction and does not mean
that its individual frames are parallel.

## Gate 3B.2 — current M5 work

### Completed: the entire M5 angular-order cover has two types

`GATE3B_M5_TWO_FOLDED_TYPES.md` uses actual maximality. On the orientation
circle of circumference T=pi/2, let h=T/2. With sorted cyclic lifts,
maximum closed-window count five is exactly

    theta_{i+5}-theta_i>h    for all eight cyclic indices.

Fold H frames back by h and sort them with the five L frames. Generic
M5 gives an occupancy walk from five to three, staying in {3,4,5}.
The complete eight-word classification reduces, by explicit legitimate
re-anchoring, to

    M5-I:  L H L H L H L L,
    M5-II: L H L L H H L L.

Both closed folded-type regions are needed. They cover coincident and
antipodal frames by a boundary argument that perturbs orientations ONLY
for the combinatorial proof, not by assuming a feasible square deformation.
Mixed folded comparisons have integer-coefficient polynomial tests in
the Gate 1 half-tangents. Keep the strict maximality constraints whenever
using M5 itself instead of the larger closed covering regions.

This is an exhaustive parent-to-two-children covering theorem for M5's
ANGULAR order. It is not a classification of their actual center/owner
arrangements.

### Completed: a whole oblique-chain family is excluded by curvature

`GATE3B_M5_OBLIQUE_CHAIN_CURVATURE.md` proves a geometric obstruction for
seven squares arranged by the directed supports

    A->B; H->A; E->B; H->L->D; E->R->D,

with reference normals east; northeast; northwest; southeast; southwest,
respectively. A,B have reference standard frames and the other five have
reference 45-degree frames. No center symmetry or exact contact is assumed.

Averaging ACTUAL outward vertex inequalities and adding the path supports
gives the all-centers scalar bound

    2q >= (2+sqrt(2)-sqrt(q-1))^2
           +(3sqrt(2)-sqrt(q))^2,

which proves q>99/25 for that reference family.

This is upgraded to independently rotated true square frames, all within
1/200 radian of their reference frames, with canonical pair normals within
1/200 of the stated directed reference normals. Inscribing reference
squares and using n dot d>=|Jn dot d| gives

    q > (99/25)*(1591900401/1600000000)^2
      = 250880541783692119299/64000000000000000000
      > Q.

The exact margin is 282141783692119299/64000000000000000000.
This excludes the entire specified continuous frame/owner family, for
arbitrary centers, in any eight-square packing. The eighth square is
unrestricted. It is not merely rejection of the displayed witness pose.

The frame and canonical-normal tests can be imposed by sufficient rational
dot/cross inequalities; no rounded-angle oracle is needed to recognize
this excluded subfamily.

### Completed: two exact no-go checks constrain the next approach

`GATE3B_M5_FOUR_STRIP_NO_GO.md` gives two actual rational M5-I packings,
with all 28 pair separators strict and exact window counts (5,5,5,5,4,4,4,4):

1. One lies in all four whole-square strips of radius 191/100<79/40,
   but not in that disk. Thus even the strengthened four-strip relaxation
   cannot exclude all M5; actual circle constraints are indispensable.
2. Another fits in squared DISK radius 397/100<4, but not below Q.
   Therefore the proposed stronger M5 radius-at-least-two shortcut is false.

Both contain the above canonical oblique chain. Its curvature theorem
rejects their whole specified separator/frame family for the true disk
ceiling, despite the relaxed strip feasibility. Neither configuration is
a counterexample to the candidate disk radius.

### ACTIVE next obligation: cover the still-unclassified M5 geometry

Start with M5-I, then M5-II. Keep the ten L-L, three H-H and fifteen mixed
pairs, all actual canonical axes, all 32 disk-vertex constraints, and the
SAME planar centers realizing every projection.

The missing theorem must classify the center/owner arrangements beyond
the already excluded near-reference oblique chain. In particular, neither
folded angular type forces that chain or its frame-neighborhood hypotheses.
There is no justification for assuming five parallel frames, standard/
45-degree clustering, a central label, or the seven displayed supports.

Required next deliverable: an explicit further parent-to-children geometric
cover of M5-I using the actual circle, with whole children excluded or
precisely retained. Then do the same for M5-II. Do not replace that with
more consequences of the disproved strip-only relaxation, another local
constant improvement, or 'every counterexample has the chain'.

**M5 exit:** an explicit usable joint center/owner survivor classification
or a complete M5 exclusion, with coverage proved. This exit is still OPEN.
Only after it is established proceed to M6, then M7, then M8.

## Gate 3C — final coverage audit: WAITING

Show that every Gate 1 packing belongs to a listed survivor or a proved
impossible family. Audit weak boundaries, angle ties, canonical ties,
corner-only and double-side statuses, and the actual equality ring/sliders.
An unfinished generator or presumed convergence is not an exit theorem.

Adding homogeneous canonical comparisons to a fiber can force equalities.
Do not assume the original strict-Slater argument applies unchanged to
that augmented system. Original-fiber dual bounds remain valid on subsets.

## Gate 4 — sharp bounds on every survivor: WAITING

Prove q>=q_* on each full continuous survivor. Apply local pose results
only after their center and slider hypotheses have been established.
The exit is a complete finite dependency table, not sampled minima or
individual PASS flags. Whole-family exclusions developed during Gate 3
are retained as already discharged children.

## Gate 5 — unrestricted optimality: WAITING

Combine exhaustive representation, structural coverage, and all survivor
bounds, then the actual construction, to conclude R_8=R_*. Audit weak
boundaries and eliminate circular dependencies before making that claim.

## Gate 6 — equality and later formalization: WAITING

Trace equality through every global alternative, including genuine slider
freedoms and symmetry orbits. Only afterward prepare a Lean handoff if
requested. No Lean compilation or CI belongs to this task.

## Executed audits from this continuation

* `verify_m5_folded_order_cover.py`: every bounded-walk word and explicit
  re-anchoring, 1,616 exact generic maximizing-anchor cases, all eight words
  observed, and an exact antipodal boundary control.
* `verify_m5_four_strip_counterexample.py`: both full rational packings,
  all 32 vertices and every displayed one of 28 signed SAT separators,
  full-square strips, exact M5 counts/type, all seven canonical chain
  hypotheses, and the exact rational margin in the curvature proof.

These use Fraction arithmetic. The continuous cover, curvature inequality,
and independent-angle lifting are the written proofs, not consequences of
finite testing. No Lean compilation or CI was invoked.

## Continuation rule

Resume at **Gate 3B.2 / M5-I's uncovered center/owner arrangements**.
Do not mark M5 or the whole gate passed. Do not move to M6 while its
predecessor's coverage/exclusion obligation is still unproved.
