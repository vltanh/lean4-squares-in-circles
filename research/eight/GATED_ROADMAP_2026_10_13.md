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
| 3B | Explicit classification of surviving joint order/owner families | ACTIVE / OPEN |
| 3C | Exhaustiveness and usability of the survivor list | WAITING |
| 4 | Sharp bounds over every surviving continuous family | WAITING |
| 5 | Assemble unrestricted optimality | WAITING |
| 6 | Global equality and later formalization handoff | WAITING |

**The unrestricted lower bound R_8>=R_* is NOT proved.** Gates 1 and 2
close representation/certificate foundations. Gate 3A is a global
necessary structural reduction, not a classification of all survivors.

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
owner-cycle/Farkas boxes were valid individual exclusions, not an
exhaustive union. Exact contacts or parallel frames may not be assumed
for arbitrary near-sharp packings.

This review is not a claim that every older file has been independently
rechecked or that any unrestricted eight-square theorem is formalized.

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

`verify_ordered_rational_gate.py` was run locally: 3,672 exact signed SAT
residual identities, vertex identities, tangencies, and an eight-frame
normalization regression. These audit the formulas; the full-domain
proof is the written argument.

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

`verify_gated_fiber_and_canonical_owner.py` was run locally. It audits
regularization, the zero-anchor guard, 11,696 exact canonical-cone
instances, a noncanonical negative control, and all 32 vertices and 28
pairs for both the existing rational reference packing and its strictly
separated eight-distinct-frame perturbation. Both are retained.

The theorem preserves the exact sharp construction by universal coverage;
the nearby rational regression is not a substitute for that proof.

### Gate 3B — classify survivors: ACTIVE

The current explicit residual is:

> Four jointly realizable directed projection orders covering all 28
> pairs, each acyclic and without a six-edge directed path, satisfying
> the common bounded center-projection relaxation, together with actual
> canonical owner axes, their octant memberships, and the seven-angle
> rational square constraints.

The next work must classify this joint residual, not merely examine each
DAG separately. Necessary projection inequalities by themselves are a
relaxation, not an actual square-packing description.

Proceed in this order:

1. Record a structural parent-to-children decomposition of the JOINT
   order families, up to legitimate symmetries, with all boundary ties
   included. Keep actual owner and orientation compatibility attached.
2. Exclude whole children by exact cross-order force or disk inequalities,
   or by proved whole-square geometric obstructions. Record each child's
   exact hypotheses and its parent's coverage implication.
3. Name every surviving continuous family and its inherited inequalities.
   Do not assert a small case count until all children are accounted for.

**Exit 3B:** an explicit survivor list and a proved coverage implication.
No exhaustive enumeration or usable small list has yet been produced.

### Gate 3C — audit exhaustiveness and usability: WAITING

Prove that every feasible Gate 1 point belongs to one listed survivor or
a proved-impossible family. Check frame coincidences, quarter-turn
boundaries, canonical ties, corner-only statuses, double-side statuses,
and the genuine equality ring and its sliders.

**Exit 3C:** a complete structural cover usable by Gate 4. A generator that
has not finished, a convergence assertion, or 'all counterexamples are
near the candidate' does not meet it.

### Important compatibility rule

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

## Stop and continuation rule

Resume at **Gate 3B**, using the four jointly realized projection orders
and the actual canonical constraints. Do not return to isolated cap
constants or another single owner/angle box unless it discharges a named
child in this structural coverage proof.
