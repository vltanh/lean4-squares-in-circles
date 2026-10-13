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
