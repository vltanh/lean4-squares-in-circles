# A pen-and-paper route to the eight-square theorem

Orientation date: 2026-10-10. Starting PR head:
`09e7c0eb5978874f8aaf4c71e646025c6be73607` (26 research commits).

The target is the least radius of a disk containing eight unit squares with
pairwise disjoint open interiors. Write `R8` for that infimum and `R*` for the
existing exact candidate, numerically `1.978770865339763...`.

## 1. What is already available

The original checklist in PROOF_TRACKER.md predates most of the PR. Its empty
boxes do not mean that candidate reconstruction still needs to start over.
The current evidence is:

| Result | Location | What its proof currently uses |
| --- | --- | --- |
| Five projected inequalities imply an exact scalar feasibility condition | FIVE_CORNER_REDUCTION.md, section 1 | A complete analytic argument using disk support and monotonicity |
| An exact algebraic stationary candidate exists | FIVE_CORNER_REDUCTION.md; EXACT_CONFIGURATION_AND_FREEDOM.md | A rational contraction certificate in a small root box |
| Eight squares fit at R*, with at least three independent sliders | EXACT_CONFIGURATION_AND_FREEDOM.md | Symbolic contact identities plus interval checks of strict margins |
| R* is optimal for the specified five-corner chain | FIVE_CORNER_OPTIMALITY.md | Interval verification of convexity and exclusion of the complement |
| Every eight-square packing has squared radius greater than 19/5 | GLOBAL_LOWER_BOUND.md | A complete-domain pair-marker certificate and a circle budget |
| At squared radius at most 98/25, a unique central square contains the closed radius-1/12 disk in its open interior | CENTRAL_CORE_CERTIFICATE.md | Another complete-domain pair-marker certificate |
| The other seven squares have ring gaps between 7/8 and 29/28 | SHARP_MARKER_RING.md | A pair-marker certificate, then elementary cyclic arithmetic |
| A state potential telescopes around a seven-cycle | SEVEN_CYCLE_POTENTIAL.md | An analytic abstract lemma; the needed sharp pair bounds are unproved |

The numerical values and the executed certificate results above are reports
of the existing PR. They are not new independent replays or new analytic
proofs. In particular, the current unrestricted sharp lower bound is OPEN.

## 2. Proof standard for this continuation

The present request is pen and paper, with no Lean proof yet. New positive
claims need displayed hypotheses and human-checkable reasoning. Exploratory
algebra may help discover identities; a sampled minimum, fitted label,
interval-box cover, or external PASS result will not close a continuous
argument in this continuation. Earlier computational results remain useful
evidence, explicitly labeled as such.

All new files and edits stay under `research/eight/`. Research commits include
`[skip ci]`. A candidate-radius theorem, a conditional theorem, and a theorem
about arbitrary packings must remain visibly distinct.

## 3. The actual missing implication

The existing conditional chain is

    (P2-P1).y >= 2,
    (P2-P3).x >= 3,
    (P3-P4).y >= 2,
    f dot (P4-P5) >= 1+sin(t),
    e dot (P1-P5) >= 2+cos(t),

where the five points lie in the packing disk, `0 <= t <= pi/4`,
`e=(cos(t),sin(t))`, and `f=(-sin(t),cos(t))`.

To use it globally one must prove that a hypothetical packing of radius
less than R* yields these inequalities, or prove a different sharp
inequality that covers all its alternatives. The seven-marker count
`(2,2,2,1)` does not imply that six square orientations agree or that the
horizontal projected span is 3. Neither assertion may be inserted as a
normalization.

The most useful target is an inequality or a reduction for an actual
minimizer. It is unnecessarily strong to demand that every packing below a
coarse ceiling already have the candidate's literal contact graph. Any use
of minimizers must first justify attainment and allowed deformations.

## 4. Work packages and their completion criteria

### A. Replace the conditional optimization certificate

Exploit the geometry of the five disk points before expanding the existing
nested radicals. For fixed tilt the problem is convex in the points and
radius. Derive its support dual with nonnegative multipliers, then allow the
multipliers to depend on the tilt. A fixed candidate stress is insufficient:
NEGATIVE_RESULTS.md records the failed frozen-stress experiment.

An alternative is to eliminate the tilt analytically from the scalar
condition and prove whole-interval convexity or monotonicity of the remaining
one-variable function. Split only where a genuine domain endpoint, a support
branch, or a stationary equation changes. The goal is a theorem covering all
`0 <= t <= pi/4` and the complete feasible ordinate interval, including
radicand-zero endpoints. Local Hessian positivity is insufficient.

**Completion criterion:** a human proof that the projected chain has minimum
R*, an exact root selection, and equality conditions for its five points.
This is valuable even before the global structural theorem is found.

### B. Establish an analytic structural starting point

Audit the central-square, central-core, and marker-ring reductions separately.
The numerical coefficients of the current markers do not provide a human
reason for their full-domain pair bounds. Either replace these bounds by
geometric support inequalities or use an independent structural route that
does not need them.

Start with compactness and fixed-orientation separating-axis geometry. Keep
the actual central square, all four possible separating axes per pair, and
all non-neighbor disjointness constraints. A supporting inequality may discard
constraints to give a necessary condition, but a construction or equivalence
argument must restore every omitted constraint.

**Completion criterion:** a rigorously justified small collection of geometric
possibilities for a minimizer, with no numerical mesh or assumed parallelism.

### C. Couple neighboring exterior squares to the central obstacle

The leading global task is a three-square inequality involving the central
square and two consecutive exterior squares, or a balanced sum of such
inequalities around the seven-cycle. Retain exterior-axis separators where
they occur. Seek a nonnegative weighted combination that cancels center
coordinates and leaves disk-support terms, as in the six-square method.

The odd length seven may matter: cheap alternating state transitions need not
close after seven steps. A state-potential argument is legitimate only after
its continuous pair bounds, the precise type domains, and all sharp equality
states are proved. Arbitrary numerical type cuts or a successful finite-state
fit do not establish that argument.

**Completion criterion:** either the five-corner obstruction is forced, or an
alternative sharp cyclic/support inequality covers every surviving case.

### D. Prove the construction and handle equality

Replace the remaining strict-margin interval checks by a small explicit
rational neighborhood with displayed elementary inequalities, or by direct
identities and monotonicity from the exact root specification. Preserve the
known sliders. Equality for the five-corner obstruction can be rigid while
some of the eight squares still move.

**Completion criterion:** an analytic construction at R* and a correct
description of the equality freedom actually proved. A maximal
classification is a further theorem; it must not delay a valid radius bound
or be inferred from one displayed three-parameter family.

### E. Assemble the unrestricted theorem, then prepare a later handoff

Combine the analytic structural statement with the sharp support inequality
and construction. Check the endpoint separately from the strict subcandidate
contradiction. Only after this mathematical dependency chain is closed should
Lean theorem interfaces or formal proof files be written.

**Completion criterion:** an unconditional theorem `R8 = R*` whose proof
contains no unproved structural assumption and no certificate-only premise.

## 5. Reductions already known to fail

Do not restart these as if they were available lemmas:

* Dropping the central square: seven exterior squares can fit below R*.
* Independently pushing every exterior square to circle contact: it can create
  overlap, even while preserving the core and ring necessary conditions.
* Requiring each central/exterior pair to separate on a central-square axis:
  an exact two-square counterexample uses only an exterior-square axis.
* Seeking a universal pair gap of `2*pi/7` from a single quarter-window state
  label: the exact two-pair obstruction already rules this out.
* Inferring a rigid eight-square equality configuration: the candidate has
  at least three independently variable positions.

The corresponding exact examples are in NEGATIVE_RESULTS.md,
RADIALIZATION_OBSTRUCTION.md, CENTRAL_PORT_NEGATIVE.md,
UNIFORM_HEPTAGON_MARKER_OBSTRUCTION.md, and
EXACT_CONFIGURATION_AND_FREEDOM.md.

## 6. Current work and reporting rule

The first parallel tasks are the analytic five-corner optimization, a global
structural reduction, and the central-aware seven-cycle route. New lemmas
will be committed as they become reviewable. A failed proposed inequality
will be recorded only when there is a precise counterexample or a useful
mathematical obstruction.

No completion of the unrestricted n=8 proof is claimed by this roadmap.

