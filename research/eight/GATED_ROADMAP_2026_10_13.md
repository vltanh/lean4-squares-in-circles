# Sequential gates for the unrestricted n=8 proof

Date: 2026-10-13. Audited baseline: `ce35213455ad9d0715db88d7a732b380d6436f3d`.
Scope: PR #9, `research/eight/**` only. Pen-and-paper research; no Lean or CI.

This file replaces the *work queue*, not the earlier mathematical results.
Advance only after the current gate's exit theorem has been proved. A useful
lemma or one rejected box does not pass a gate about an entire domain.

## Target and baseline

Let q_* be the exact five-corner candidate squared radius defined by
`ANALYTIC_EXACT_CONSTRUCTION.md` and `HUMAN_FAMILY_CLOSURE.md`.
The research record establishes an actual eight-square construction at
R_* = sqrt(q_*) approximately 1.97877086534. The missing optimality theorem is:

> Every eight pairwise interior-disjoint unit squares contained in a disk
> of squared radius q satisfy q >= q_*.

Do not replace q_* by a rounded decimal or by the convenient larger ceiling
9789/2500. Equality classification is a separate later objective.

The latest dependency review finds:

* An exact candidate construction and a sharp conditional family theorem.
* A genuine **local pose** sharpness theorem, with independently varying
  frames, in `HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md`. It is not yet
  an explicit angular-box terminal valid for every possible center fiber.
* An exact fixed-angle/fixed-SAT-owner convex center problem and its dual,
  in `GLOBAL_SAT_ANGLE_FIBER_DUALITY.md`.
* Sound owner-cycle, rational-sector and Farkas exclusions, including
  positive-width orientation boxes. No exhaustive owner/angle union is covered.
* Explicit reasons not to assume exact contacts, frame alignment, or local
  candidate capture for arbitrary near-sharp packings.

These are research-proof inputs, not a claim that every old file has been
independently rechecked or that an unrestricted theorem is formalized.

## Gate 1 — One exact exhaustive domain

**Current status: ACTIVE.**

Prove a normalization and closed-domain theorem covering every packing,
including all orientation and SAT boundary cases, without assuming a
central square, a contact graph, or a common frame.

Deliverables:

1. Remove the global rotation gauge; only seven relative frame angles
   should remain, not eight independent physical angles.
2. Relabel by relative orientation and use one closed rational
   half-tangent simplex with all boundary duplicates retained.
3. Give explicit rational true-square vertices, all 28 eight-way SAT
   disjunctions, and positive-denominator polynomial forms.
4. Prove both directions: every packing has a representative, and every
   feasible representative is an actual packing. Retain a compact
   radius-ceiling domain and attainment.

**Exit:** a complete hand proof, not a discretization or a sampled roundtrip.
Arithmetic diagnostics can check formulas but are not premises.

## Gate 2 — Complete center-fiber alternatives

**Status: WAITING FOR GATE 1.**

For each fixed relative orientation and chosen full SAT-owner word, prove:

1. Either its directed separator system is infeasible, with an exact
   positive balanced-force certificate, or its radius minimum is attained
   and the vertex/separator dual is exact.
2. Handle zero disk-anchor weights explicitly; no division by zero and no
   silently discarded free-center linear force.
3. Establish finite support bounds for the certificates, and establish
   that a strict lower bound admits rational, positive-anchor, locally
   stable dual data. This distinguishes a complete rejection mechanism
   from a heuristic numerical oracle.
4. State precisely when a local pose theorem can propagate to a whole
   fixed-frame convex fiber; do not infer an angular neighborhood from a
   pose neighborhood without a center-capture argument.

**Exit:** prove these alternatives for *every* fiber. This does not mean
that all fibers have been proved to exceed q_*.

## Gate 3 — Exhaustive structural reduction of owner families

**Status: WAITING FOR GATE 2.**

This is the first unresolved *global geometric* bottleneck. The raw
8^28 owner words are not an adequate hand-proof case list.

Work in the exact Gate 1 domain, and derive a covering identity of the form

    all admissible angle/owner fibers under the radius ceiling
      subset of proved-impossible families union explicit surviving families.

Use the complete Gate 2 alternatives to discover and prove structural
reductions, rather than improving isolated cap constants or collecting
unrelated narrow boxes. The existing marker, central-square, cone-order,
and stress results are available only with their stated hypotheses.

**First subgate 3A:** produce one *owner-complete* structural family
reduction: it must quantify over every valid owner selection in the stated
geometric family, not merely a hand-picked word. State the family,
coverage proof, and survivors before numerical exploration.

**Subgate 3B:** extend these reductions to a demonstrably exhaustive,
explicitly indexed survivor list. Every branch must have a written
parent-to-children coverage implication, including weak inequalities,
frame ties, corner-only statuses, and double-side statuses.

**Subgate 3C:** prove that the resulting list is usable for Gate 4 without
an unbounded search or an assumed convergence/capture assertion.

**Exit:** an actual structural coverage theorem with explicit survivors.
A generator that has not finished, a finite-certificate existence claim
conditional on the desired sharp theorem, and 'all counterexamples are
near the candidate' do not pass this gate.

The genuine equality ring, its frame coincidences, and slider freedoms
must remain admitted throughout.

## Gate 4 — Sharp bounds on every surviving family

**Status: WAITING FOR GATE 3.**

Prove q >= q_* for each surviving family over its entire continuous domain.
Use exact angular dual inequalities or whole-square geometry. Near the
candidate, use the local pose theorem only after the necessary uniform
center and slider hypotheses have been proved.

**Exit:** a finite dependency table in which every Gate 3 survivor has a
proved sharp bound. Strict-margin interval computations may guide a hand
proof; a sampled minimum or a PASS flag is not the final argument.

## Gate 5 — Assemble unrestricted optimality

**Status: WAITING FOR GATE 4.**

Combine Gate 1 coverage, Gate 3 structural reduction, and Gate 4 bounds,
then combine with the actual construction to deduce R_8 = R_*.
Audit all strict/non-strict boundaries and verify that no hypothesis is
the desired theorem in disguise.

**Exit:** one self-contained unrestricted lower-bound theorem with a
closed dependency graph. Do not describe the research as optimality
before this gate passes.

## Gate 6 — Equality and subsequent formalization handoff

**Status: WAITING FOR GATE 5; separate from the lower-bound claim.**

Trace equality through all global alternatives, including nonunique
sliders and symmetry orbits. Only then prepare a Lean handoff if requested.
No Lean compilation or CI is part of the present task.

## Execution rule and current action

Work on Gate 1, then Gate 2, then 3A. Update this file after each proved
exit, with the proof file and what remains unproved. Do not jump to
Gate 4 because a promising local inequality is easier to obtain.

No gate is passed by this planning commit alone.
