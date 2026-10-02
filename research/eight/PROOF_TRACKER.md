# n=8 proof tracker

## Scope

This branch tracks research toward a human-readable proof for eight unit squares
in a circle.

- [x] Keep research artifacts under `research/eight/**`.
- [x] Do not change production Lean, public theorem statements, CI, metadata,
      or other research subtrees in this planning PR.
- [x] Reuse generic n=6/n=7 machinery where it genuinely applies.
- [ ] Do not promote a numerical candidate to a theorem statement until its
      exact contact equations and construction have been derived.
- [ ] Keep the substantive proof analytical: no interval-box cover, generated
      classification table, sampled minimum, or external PASS result as the
      reason a continuous case is true.

## Working objective

The project has two logically separate tasks:

1. reconstruct the best n=8 candidate exactly and prove it is a packing;
2. prove no packing can use a smaller radius, ideally with an equality/contact
   classification strong enough to explain the candidate.

The hard research question is expected to be the global structural reduction,
not the pairwise separation algebra.

## Reusable machinery from n=7

### Generic pair normalization and separating axes

These pieces should be treated as infrastructure, not reproved case by case.

- [ ] Generalize/reuse the canonical relative-state model for two rotated unit
      squares.
- [ ] Reuse the four separating axes of the two square frames.
- [ ] Reuse support sums in terms of:
      - relative phase;
      - center displacement in the first frame;
      - pair width
        `(1 + |cos d| + |sin d|)/2`.
- [ ] Reuse the reverse-pair/reflected-frame reduction.
- [ ] Make the generic pair lemma independent of the n=7 label definition
      where practical.

Relevant n=7 architecture:

```text
CanonicalPair
  -> canonical_has_separator
PairModel
  -> relativePhase
  -> centerDX / centerDY
  -> pairWidth
  -> pairSupport
  -> pair_support_axis_values
```

### Continuous-gap / leftmost-minimum method

- [ ] Identify whether the n=8 candidate supplies a natural critical angular
      gap or a small finite set of critical gap types.
- [ ] If so, prove the critical-gap inequalities first.
- [ ] Reuse the n=7 pattern:
      ```text
      endpoint/critical gap
        -> positivity near one end
        -> assume a first nonpositive point
        -> choose leftmost minimum
        -> cardinal-phase cases
        -> smooth stationary case
      ```
- [ ] Reuse the smooth sinusoid/stationary-corner machinery rather than
      subdividing a continuous angle interval.

### Convex state-region reductions

- [ ] When an active label/support branch produces a convex polygonal state
      region, reduce affine support expressions to its vertices.
- [ ] Keep finite cases only when they are geometric vertices, sign walls,
      contact types, or separating directions.

## Reusable machinery from n=6

### Weighted separator combinations

- [ ] Search for small cycles/paths of genuine separating inequalities whose
      weighted sum cancels nuisance center coordinates.
- [ ] Derive weights from the candidate contact geometry, not by numerical fit.
- [ ] Keep all weights nonnegative when they are used as dual multipliers.
- [ ] Explain every resulting support force geometrically.

This is a leading candidate for the final n=8 closure because the optimum may
not have the equal-gap rigidity available for n=7.

### Support-force cones

- [ ] Keep two-dimensional force vectors intact before scalar expansion.
- [ ] Prove force vectors lie in a simple cone.
- [ ] Derive one disk-support inequality valid on that cone.
- [ ] Use completed squares / Cauchy--Schwarz after the cone is visible.
- [ ] Avoid replacing a clean vector inequality with a large polynomial unless
      there is no simpler route.

### Whole-domain analytic reduction

For any remaining 2--4 parameter defect:

- [ ] derive its true domain from geometry;
- [ ] prove monotonicity in one variable where possible;
- [ ] prove concavity/convexity in another;
- [ ] split only at genuine sign walls or active-contact transitions;
- [ ] reduce to finitely many endpoints forced by those arguments;
- [ ] use exact Taylor/algebra only at those forced endpoints.

## Gate 1 — exact candidate reconstruction

Do not begin a full lower-bound formalization before this gate is understood.

- [ ] Recover a high-precision candidate configuration from a reliable source or
      independent numerical reconstruction.
- [ ] Determine its symmetry group.
- [ ] Identify every square-square contact.
- [ ] Identify every active circle contact.
- [ ] Identify which square orientations are equal by symmetry.
- [ ] Count the true degrees of freedom after quotienting translation/rotation.
- [ ] Write the minimal contact equation system.
- [ ] Eliminate auxiliary coordinates enough to obtain an exact algebraic
      characterization of the candidate radius.
- [ ] Determine whether the radius satisfies a manageable polynomial.
- [ ] Prove the selected algebraic root is the geometrically relevant one.
- [ ] Record exact or algebraic coordinates/orientations suitable for Lean.

Deliverable:

```text
research/eight/CANDIDATE.md
```

with an exact contact graph and equations, not only decimal coordinates.

## Gate 2 — construction

- [ ] Define the exact candidate configuration.
- [ ] Prove every object is a unit square.
- [ ] Prove pairwise disjoint interiors from the contact graph / separating
      axes.
- [ ] Prove containment in the candidate circle.
- [ ] Prove at least one vertex/contact reaches the boundary, so the stated
      radius is exact for the construction.
- [ ] Package a proposed Lean construction theorem.

Deliverable:

```text
research/eight/CONSTRUCTION_PROOF.md
```

## Gate 3 — choose the global structural invariant

Test several routes before committing to one.

### Route A — marker / angular budget

- [ ] Define candidate-derived marker(s) for an exterior square.
- [ ] Determine whether one marker type is enough or whether the tilted and
      near-axis states need different marker branches.
- [ ] Prove a pairwise marker-gap inequality from canonical separation.
- [ ] See whether the full circle budget forces the candidate cyclic pattern.
- [ ] If gaps have different types, derive a mixed budget such as
      `m*alpha + k*beta = 2*pi` at equality.
- [ ] Reject this route if the resulting gap theorem is too weak to force the
      contact graph.

### Route B — contact/separator graph

- [ ] Use four-axis pair reduction to associate each relevant pair with a
      geometric separating/contact type.
- [ ] Prove every sufficiently small packing has enough active/near-active
      separators to force a small list of planar contact graphs.
- [ ] Eliminate graphs conceptually using degree, cyclic order, support budget,
      or disk geometry rather than exhaustive graph enumeration.
- [ ] Show the surviving graph is the candidate graph.

### Route C — large near-axis scaffold

- [ ] Test whether a sufficiently small n=8 packing must contain a large
      subsystem of squares with nearly common orientation.
- [ ] If yes, rigidify that subsystem using n=5/n=6 style polygon/tangent
      arguments.
- [ ] Treat the remaining tilted squares as defects/insertions constrained by
      the scaffold.
- [ ] Determine whether this reduces the problem to one or two tilt parameters.

### Decision gate

- [ ] Select the route with the shortest conceptual global argument.
- [ ] Document why the discarded routes fail or are weaker.

Deliverable:

```text
research/eight/STRUCTURAL_REDUCTION.md
```

## Gate 4 — n=8 state and label model

Only after the candidate/contact structure is understood:

- [ ] Choose sorted local state coordinates for an exterior square.
- [ ] Write the exact containment region at the candidate radius.
- [ ] Derive support/marker branches from actual candidate contacts.
- [ ] Define a label as the minimum of those geometrically meaningful branches,
      if a single label is useful.
- [ ] Prove branch-transition loci exactly.
- [ ] Identify capped/convex regions and their true vertices.
- [ ] Avoid introducing branches solely because a numerical estimate changes
      quality there.

Deliverable:

```text
research/eight/STATE_MODEL.md
```

## Gate 5 — critical pair inequalities

For every pair type required by the structural reduction:

- [ ] state the exact support inequality;
- [ ] reduce disjointness to one of the four separating axes;
- [ ] exploit sign/active-label symmetry;
- [ ] use disk support, weighted separators, or force cones;
- [ ] use monotonicity/concavity on the full continuous sector;
- [ ] record equality/contact conditions, not merely nonnegativity;
- [ ] avoid Bernstein/coefficient-vector positivity unless it is only final
      transparent bookkeeping after a human sign argument.

Maintain a table:

| Pair/contact type | Separator axis | Active branches | Human inequality | Equality |
| --- | --- | --- | --- | --- |
| TBD | | | | |

Deliverable:

```text
research/eight/PAIR_INEQUALITIES.md
```

## Gate 6 — global lower bound

- [ ] Assemble the pair inequalities into the chosen structural invariant.
- [ ] Prove every packing below the candidate radius contradicts either:
      - the angular budget;
      - the forced contact/separator graph;
      - or a weighted global support inequality.
- [ ] Keep the lower-bound endpoint independent of numerical search artifacts.
- [ ] State clearly which portions are strict below the candidate radius and
      which extend to equality.

Deliverable:

```text
research/eight/LOWER_BOUND_PROOF.md
```

## Gate 7 — equality and uniqueness / classification

Do not assume uniqueness in advance.

- [ ] Determine numerically/geometrically whether the optimum appears isolated
      or has continuous degrees of freedom.
- [ ] Classify zeros/equality cases of every support inequality used above.
- [ ] Recover the contact cycle/graph at equality.
- [ ] Reconstruct centers and orientations from contacts.
- [ ] Identify any continuous family of optimal packings.
- [ ] Formulate the correct congruence/classification statement.

Deliverable:

```text
research/eight/EQUALITY_PROOF.md
```

## Gate 8 — Lean handoff

Research code remains separate until the mathematics stabilizes.

- [ ] Implement generic reusable lemmas under `research/eight/lean/**`.
- [ ] Give exact theorem interfaces matching eventual production needs.
- [ ] No `sorry`, `admit`, external success premise, or generated finite
      classifier in the final research proof path.
- [ ] Add dependency checks excluding any exploratory certificate machinery.
- [ ] Compile locally before proposing production integration.
- [ ] Only after the proof stabilizes, hand off production integration as a
      separate change.

## Immediate next tasks

1. [ ] Reconstruct the candidate and contact graph.
2. [ ] Decide whether the two-square canonical/support model can be factored
       into a generic reusable research module without n=7 labels.
3. [ ] Test the candidate contact graph against:
       - marker-gap budget;
       - weighted separator cycles;
       - near-axis scaffold rigidity.
4. [ ] Derive the first exact structural lemma before writing large Lean files.

## Human-proof standard

A successful n=8 proof should read schematically as

```text
candidate contact geometry
  -> generic separating-axis reductions
  -> small number of candidate-derived state/contact types
  -> global structural theorem
  -> whole-domain support/monotonicity/concavity
  -> forced equality graph
  -> candidate radius and classification
```

not as

```text
many angle boxes
  -> generated rows / sampled minima
  -> acceptance by exhaustive computation.
```
