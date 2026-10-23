# Pending geometric reductions — source-only handoff

**Branch:** `formalize/eight-uncompiled-draft` (PR #10).  
**Starting head:** `3281f5f6568696256428bbb9f13185a185892e82`.  
**Status:** research handoff; **not** a claim that the proposed deletions are active or kernel-verified.

The previous geometric-replacement session identified two further changes to
connect before the n=8 proof can be considered free of large case tables. The
workspace holding the unpublished edits was not retained. This file records
what can actually be recovered from the committed branch, the precise
interfaces, and the outstanding work. It does not silently delete cases or
substitute a finite statement for its mathematical proof.

## 1. Global exclusion of adjacent core centers

A proof source already exists in
`SquaresInCircles/Eight/Candidate/GeometricCoreCycle.lean`:

- `GeometricCoreCycle.NoAdjacentCore` is the geometric assertion
  `∀ i, ¬ (C.a i ≤ 7/12 ∧ C.a (next i) ≤ 7/12)`.
- `GeometricCoreCycle.coarse_no_adjacent_core` derives it from the **same**
  selected affine labels and the coarse cyclic charged inequality, provided
  the stronger original-label budgets hold.
- `GeometricCoreCycle.NoAdjacentCore.outer_pair` transfers that assertion
  to any two actual covering arcs: one is outer.
- `GeometricOuterCoverage.chargedBound` is a same-interface charged-bound
  constructor that only dispatches to retained outer-endpoint rows.

The numerical heart is a single-core/core cost **strictly greater than**
`9/10` and a lower bound `89727/100000` on each of the other six
edges. The resulting cyclic lower bound is

```
9/10 + 6 * (89727/100000) = 314181/50000 > 2π.
```

The stronger core/core bound uses the existing original-marker proof in
`GeometricCoreMarker` and keeps one consistent marker at each vertex;
it is not a fresh estimate using independently chosen labels.

**Outstanding integration:** construct and statically validate the stronger
core marker budget for the coarse metadata, invoke
`coarse_no_adjacent_core` after the coarse cyclic stage, thread the
result into the subsequent charged-bound stages, and change their coverage
predicate to `GeometricOuterCoverage.NumericValid` and
`GeometricOuterCoverage.chargedBound`. Regenerate only the rows for which
both endpoints are core; preserve all original outer rows, chain endpoints,
signed axes, and source labels. The previously estimated saving is
**26,258 rows across five later affine tables**, a target requiring a new
static count rather than a completed deletion.

**Dependency caution:** deriving `NoAdjacentCore` from a later, already
pruned table would be circular. It must be derived from the original coarse
stage before specializing *any* later row coverage. The coarse proof itself
must retain all cases required for its own derivation.

## 2. Eight remaining quarter-owner patterns

The currently retained source patterns are

```
![0,g,0,0,0,2,e]
g ∈ {0,1}, e ∈ {0,1,2,3}
```

and are explicitly checked by
`Generated.Owner.QuarterPattern`,
`Generated.Owner.quarter_pattern_complete` and the eight
`Owner.Quarter004`–`Quarter007` and
`Owner.Quarter016`–`Quarter019` modules.

The previously published geometric restrictions already show:

1. Every feasible D-to-E axis is one of the intended quarter axes
   (`GeometricOwnersDoubleComplete.D_quarter_owners`).
2. Every residual forbidden B-to-T axis with G-to-A axis 2 or 3
   is impossible (`GeometricOwnersQuarter` and
   `GeometricOwnersForbiddenB`).
3. Therefore only G axes 0 and 1 with forbidden B and intended D
   remain to be ruled out, uniformly across all four feasible E axes.

The necessary nominal edge inequalities remain those in
`GeometricOwners`, `GeometricOwnersQuarter`, and
`GeometricOwnersTiltCone`. Any new geometric exclusion must use the
original feasible axes and the **single shared** mismatch budget
`S ≤ 3/200`, not a separate budget for each edge. It must apply on both
tilt signs and at endpoints and ties.

**Outstanding integration:** obtain a complete all-four-E-axis circle
stress/primary-span contradiction for each of G axes 0 and 1, expose it as a
theorem with the same geometric hypotheses as `quarter_owners`, then
remove the eight generated modules from `OwnerData`, the corresponding
lookup and selector from `OwnerCompleteness`, and the generator manifest.
Do not retire these modules merely because numerical exploration suggests
such a contradiction.

## 3. Active work after these two reductions

At the starting head the imported source inventory is:

- 576,828 generated affine rows across ten tables.
- 8 quarter-owner modules / 345 quartic row certificates.
- 15 mixed-owner modules / 729 row certificates.
- 41 positive-tilt bundles / 861 row certificates.
- 1,120 individual recursive word certificates.
- 5,376 fixed scalar-box checks and 49 local stationary formula
  certificate declarations.

The next *structural* priorities remain the complete role-dependent
two-state charged inequality (roadmap G2.3), remaining owner/positive-tilt
circle stresses, and the non-core word-pair inequalities. A source-row
deletion is an auditable dependency improvement, **not** a measured
compilation speedup.

## 4. Verification discipline

No Lean compilation, Lake build, CI, or certificate replay was authorized
for this pass. All work in this document is a source handoff until proofs are
connected with unchanged hypotheses and the regenerated dependency
inventory confirms actual removal. Each implementation commit should
retain `[skip ci]` and preserve the public n=8 theorem and equality family.
