# Sequential gates for the unrestricted n=8 proof

Date: 2026-10-13. Audited starting head: `ce35213455ad9d0715db88d7a732b380d6436f3d`.
Scope: PR #9, `research/eight/**` only. Pen-and-paper research; no Lean or CI.

**This is the authoritative active work queue.** It replaces earlier work
queues, including the accumulated historical sections of
`CURRENT_GLOBAL_PROOF_ROADMAP.md`, without retracting their valid results.
Advance only after a gate's stated exit theorem is proved. One useful
lemma or one rejected box does not pass a gate about an entire domain.

## Current status

| Gate | Requirement | Status |
|---|---|---|
| 1 | Exact exhaustive seven-angle actual-square domain | PASSED |
| 2 | Complete sparse center-fiber alternatives | PASSED |
| 3A | First owner-complete structural reduction | PASSED |
| 3B.1 | Exhaustive four-branch frame-majority cover | PASSED |
| 3B.2 | Joint owner-family classification, starting with M5 | ACTIVE / OPEN |
| 3C | Exhaustiveness and usability of the final survivor list | WAITING |
| 4 | Sharp bounds over every surviving continuous family | WAITING |
| 5 | Assemble unrestricted optimality | WAITING |
| 6 | Global equality and later formalization handoff | WAITING |

**The unrestricted lower bound R_8>=R_* is NOT proved.** Gates 1 and 2
close representation/certificate foundations. Gate 3A gives a global
necessary structural reduction. Gate 3B.1 covers all packings by four
macrobranches; it does not classify their internal owner families.

## Target and audited baseline

Let q_* be the exact five-corner candidate squared radius defined by
`ANALYTIC_EXACT_CONSTRUCTION.md` and `HUMAN_FAMILY_CLOSURE.md`.
The research record establishes an actual eight-square construction at
R_*=sqrt(q_*) approximately 1.97877086534. The missing optimality theorem is:

> Every eight pairwise interior-disjoint unit squares contained in a disk
> of squared radius q satisfy q>=q_*.

Do not replace q_* by a rounded decimal or by the larger research ceiling
9789/2500. Equality classification is a separate later objective.

The dependency review found an exact construction, a sharp conditional
family theorem, a genuine **local pose** theorem with independently
varying frames, and exact convex fixed-angle/owner center fibers. Earlier
owner-cycle/Farkas boxes were individual exclusions, not an exhaustive
union. Exact contacts or parallel frames may not be assumed for arbitrary
near-sharp packings. This review does not claim that every older file has
been independently rechecked or that any unrestricted theorem is formalized.

## Gate 1 — One exact exhaustive domain: PASSED

Proof: `GATE1_ORDERED_RATIONAL_GLOBAL_MODEL.md`.

Every packing has a representative on the closed rational simplex

    z_1=0 <= z_2 <= ... <= z_8 <= 1,

where z_i is the half-tangent of a relative frame angle. The common
rotation gauge is removed; seven physical frame variables remain.
All 32 actual vertex constraints and all 28 eight-way SAT disjunctions
have explicit integer-coefficient polynomial forms with positive
cleared denominators. The proof covers both directions of representation,
frame ties, quarter-turn duplicates, separator tangencies, and compact
attainment below the fixed research ceiling.

This gate does not reduce the raw owner count or prove a radius bound.

## Gate 2 — Complete center-fiber alternatives: PASSED

Proof: `GATE2_COMPLETE_SPARSE_FIBER_ALTERNATIVE.md`.

For every fixed frame tuple and full true SAT-owner word:

* An infeasible directed separator system has a positive balanced-force
  witness supported on at most 15 edges (at most 2m-1 on m labels).
* Otherwise the radius minimum is attained and has an exact optimal dual
  supported on at most 17 total disk-vertex and separator constraints.
* Zero-anchor center forces are handled explicitly, with no division by
  zero or silently omitted linear term.
* Every strict fiber exclusion has rational, strictly positive disk-anchor
  multipliers valid on a relative open orientation neighborhood. The exact
  regularization estimate is D_epsilon >= (1-epsilon)D+epsilon/2.
* A local pose minimum propagates to its ENTIRE same-frame convex owner
  fiber, but not automatically to a positive-width angular neighborhood.

Finite-cover existence on a compact region is conditional on already
having a strict bound there. It is not a proof of global sharpness.
The 17-term optimal support bound need not survive positive-anchor
regularization; the two conclusions must not be conflated.

## Gate 3 — Exhaustive structural reduction: STILL OPEN

The raw 8^28 owner words are not an adequate hand-proof case list.
A sharp radius theorem cannot be assembled until an explicit exhaustive
and usable survivor classification has been proved.

### Gate 3A — owner-complete first reduction: PASSED

Proof: `GATE3A_CANONICAL_OWNER_FOUR_ORDERS.md`.

All eight signed true axes of a square pair have the same support sum.
Thus every packing, with every initial valid owner choice, can be
represented instead by **canonical maximum-projection owners**. This
keeps the exact centers, frames, disk, and radius, with ties retained.

A canonical normal n obeys n dot d >= |Jn dot d| for the true center
difference d. This gives four simultaneous rational projected-center
orders, using

    (12,5), (5,12), (-5,12), (-12,5).

The eight signed normal octants choose one of these four orders and an
arrow direction. Every resulting edge a->b in order k satisfies

    u_k dot (p_b-p_a) >= 7 w_ab >= 7.

Opposite octants are merged with reversed arrows; without that reversal
the claimed DAG restriction would be vacuous. Each order graph is
acyclic and, throughout R^2<=9789/2500<4, has no six-edge directed path.
Cross-order positive force balances reject entire coarse order families,
not isolated orientation boxes.

### Gate 3B.1 — four exhaustive frame-majority branches: PASSED

Proof: `GATE3B_FOUR_FRAME_MAJORITY_BRANCHES.md`.

Orientations live on the circle of circumference pi/2. Let M_i count
frames in the closed clockwise pi/4 window starting at square i's frame,
including i and all multiplicities. Each pair contributes to at least
one such count, so sum_i M_i>=8+28=36 and max_i M_i>=5.

Choose a maximizing anchor and normalize its frame to zero. The packing
then belongs to M5, M6, M7, or M8, according to how many frames lie in
[0,pi/4]. Call those labels L and the remainder H. The boundary condition
is exactly polynomial: 1-2z-z^2>=0 for L and <=0 for H in the closed cover.
Closed chambers deliberately overlap at pi/4; they do NOT by themselves
imply an exclusive exact count or that the chosen anchor is maximizing.
Retain those extra conditions explicitly whenever a later argument uses them.

Canonical octant labels can be chosen coherently by the owner square's
frame group: every L-L pair uses orders 0 or 2; every H-H pair uses
orders 1 or 3; mixed pairs may use any of the four orders. The two orders
within each group are orthogonal.

| Branch | L / H sizes | L-L pairs: orders 0/2 | H-H pairs: orders 1/3 | Mixed pairs |
|---|---|---:|---:|---:|
| M5 | 5 / 3 | 10 | 3 | 15 |
| M6 | 6 / 2 | 15 | 1 | 12 |
| M7 | 7 / 1 | 21 | 0 | 7 |
| M8 | 8 / 0 | 28 | 0 | 0 |

Each row accounts for all 28 pairs. This is an exhaustive MACROBRANCH
cover, not four already solved cases. M8 does not assume parallel frames:
its eight frames may vary across the entire 45-degree window. The sharp
candidate is retained in M8. No M5--M8 branch is excluded by this note.

### Gate 3B.2 — classify internal joint order families: ACTIVE, START WITH M5

The next precise target is:

> For every M5 packing under the radius ceiling, classify the jointly
> realized two-order L subsystem (10 pairs), two-order H subsystem
> (3 pairs), and 15 mixed pairs, with all actual canonical owners,
> octant memberships, and seven-angle square constraints attached.

A valid exit for this child is a proved structural exclusion or an
explicit further survivor decomposition with a parent-to-children
coverage proof. Work on M5 first, then M6, M7, and M8. Do not skip to
M8 just because the candidate family there is easier to recognize.

For each child:

1. Record the structural decomposition and valid symmetries, including
   all weak boundary and maximizing-axis ties.
2. Exclude whole subfamilies by exact joint force/disk inequalities or
   whole-square geometric obstructions. Record exact hypotheses.
3. Name every surviving continuous family and inherited constraints.

The projections must be realized by the SAME planar centers. Separate
DAG feasibility is insufficient. Even joint projection feasibility is
only a necessary relaxation, not a real square-packing witness.

**Exit 3B.2:** an explicit usable survivor list across all four branches,
with coverage implications. No such final list has yet been produced.

### Gate 3C — audit exhaustiveness and usability: WAITING

Prove that every feasible Gate 1 point belongs to one final listed
survivor or a proved-impossible family. Check frame coincidences,
quarter-turn boundaries, canonical ties, corner-only and double-side
statuses, and the genuine equality ring and its sliders.

**Exit:** a complete structural cover usable by Gate 4. An unfinished
generator, a convergence assertion, or 'all counterexamples are near the
candidate' does not meet it.

### Compatibility rule for canonical comparisons

Adding homogeneous canonical comparison inequalities to a fiber can
force equality in those rows. Do not reuse Gate 2's full strict-Slater
claim for that augmented system without an affine-hull argument. Original
fiber dual bounds remain sound on its canonical subset; the projected
positive-width systems have their separately proved force alternative.

## Gate 4 — Sharp inequalities for every survivor: WAITING

For each Gate 3 survivor prove q>=q_* throughout its entire continuous
domain. Use exact angular dual inequalities or whole-square geometry.
Invoke the local pose theorem only after its needed center and slider
hypotheses are uniformly established. Do not treat an angular box as a
pose neighborhood without a valid implication.

**Exit:** a finite dependency table with a proved bound for every survivor.
Numerical minima and individual PASS flags are not the final argument.

## Gate 5 — Unrestricted optimality: WAITING

Combine Gate 1 coverage, Gate 3 classification, and Gate 4 bounds, and
then the actual construction, to deduce R_8=R_*.
Audit all weak boundaries and noncircular dependencies.

**Exit:** a self-contained unrestricted lower-bound theorem with a closed
dependency graph. Do not call the research an optimality proof before it.

## Gate 6 — Equality and formalization handoff: WAITING

Trace equality through every global alternative, preserving genuine slider
freedoms and symmetry orbits. This is separate from proving the radius.
Only later prepare a Lean handoff if requested. No Lean compilation or CI
belongs to this task.

## Executed exact arithmetic audits

* `verify_ordered_rational_gate.py`: 3,672 exact signed SAT residual
  identities; vertex identities; tangencies; an eight-frame normalization.
* `verify_gated_fiber_and_canonical_owner.py`: exact regularization,
  zero-anchor guard, 11,696 canonical-cone instances, and a noncanonical
  negative control. All 32 vertices and 28 pairs checked for both the
  existing rational reference packing and its strictly separated
  eight-distinct-frame perturbation; both remain admitted.
* `verify_frame_majority_cover.py`: 503 exact eight-frame inputs,
  including coincident and exact 45-degree direction ties. All four
  maxima 5,6,7,8 occur; both actual n=8 packing regressions have maximum 8.

These are arithmetic/implementation regressions, not a global proof
oracle. Continuous coverage and inequalities are proved in the written
notes. Preservation of the exact sharp construction follows from the
universal theorems, not substituting a nearby rational regression.

## Stop and continuation rule

Resume at **Gate 3B.2 / M5**, with its 10 L-L, 3 H-H, and 15 mixed pairs.
Do not return to isolated cap constants or another single owner/angle
box unless it discharges a named child in this structural coverage proof.
