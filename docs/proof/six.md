# Six squares: analytical proof supplement

[Back to the proof contents](README.md)

This chapter documents the current **analytical hand-proof route** for six unit
squares. It is a supplement to the older numbered chapters rather than a
renumbering of them.

The repository also retains an earlier self-contained Lean route based on
finite exact classification. The two approaches are compared explicitly in
[the n=6 approaches note](../../research/six/lean/APPROACHES.md). The public
n=6 source now uses the analytical route.

The analytical source is complete at the theorem level but has not yet been
compiled or kernel-audited on the current head. This chapter therefore
describes the intended mathematical proof, not an executed validation result.

## 1. The candidate

The optimal model has five axis-parallel squares and one square rotated by
$45^circ$. The exact algebraic constants are defined in
`SquaresInCircles/Six/Candidate.lean`; the model itself is the unchanged
`Six.model`.

The construction proof shows that this model packs the disk of radius
`Six.radius`. The hard direction is to show that every six-square packing
needs at least this radius and that equality forces this model.

## 2. Normalize an arbitrary candidate-sized packing

Assume a packing has squared radius at most `Six.qStar`. The normalization
puts it into a canonical frame with:

- a central square containing the disk centre;
- exterior squares labelled E, N, W, D, S;
- exact radial/transverse coordinates;
- narrow angular windows;
- a canonical choice between an OWN central separator and the matching
  cardinal separator.

The result is `Normalization.NormalizedPacking R`. No extra hypothesis is
added to the original `Packing` predicate.

The detailed normalization argument is recorded in
[`ANALYTIC_NORMALIZATION_PROOF.md`](../../research/six/lean/ANALYTIC_NORMALIZATION_PROOF.md).

## 3. The analytical reduction problem

After normalization, the radius proof needs a small package
`ReductionHypotheses P`. Its substantive geometric content is:

1. the W--D pair uses the candidate W-sourced separating inequality;
2. the D--S pair uses the candidate S-sourced separating inequality;
3. the two fixed-pair angle domains hold;
4. the diagonal angle is at least $1/2$.

The old proof route supplied this package using finite exact classification.
The current route proves it analytically.

`Analytic/ReductionInterface.lean` exposes the logical frontier. After the
independent lower OWN-S tail and derived OWN-W tail are accounted for, the
remaining mathematics reduces to:

- exclude `MissingWestWing`;
- exclude `MissingSouthWing`;
- prove the OWN-S upper tail $sle 11/25$.

All three are now represented by analytical source proofs.

## 4. Excluding the missing south wing

The south analysis is split according to the canonical W separator.

### 4.1 Cardinal W

For cardinal W, the final difficult region has large positive OWN-S angle.
The proof combines the actual CW, CS, WD and D-sourced DS inequalities with
weights $4,10,3,3$.

The resulting support defect is handled on the entire continuous domain:

- the diagonal variable is monotone;
- the south variable is reduced by concavity;
- the west variable is reduced by concavity on the two genuine sign intervals;
- six geometrically forced endpoint inequalities remain.

Those endpoints are proved with exact rational Taylor inequalities. There is no
angle grid or sampled minimum.

See
[`ANALYTIC_CARDINAL_SOUTH_PROOF.md`](../../research/six/lean/ANALYTIC_CARDINAL_SOUTH_PROOF.md)
and `Analytic/CardinalSouthTail/`.

### 4.2 OWN W

The remaining OWN-W cases require sharper shared-center and support estimates.
The proof uses separate modules for ordered and west-dominant OWN configurations
and for the cardinal-S cone. Whole-interval curvature estimates reduce the
continuous domains to exact endpoints.

The combined result is the unconditional analytical exclusion
`Analytic.not_missing_south`.

## 5. Excluding the missing west wing

A D-sourced west separator is first forced into a narrow high-diagonal region.
The proof obtains, among other restrictions, a phase gap larger than one radian
and then sharper reserves for the remaining OWN cases.

The branches are handled by:

- cardinal-S mixed-west support;
- OWN-W/cardinal-S support;
- OWN-W/OWN-S support;
- reflected scalar arguments for the last two-OWN configurations.

The reflection is applied to scalar inequalities only after proving the
corresponding reflected domain. It is not assumed that reflecting the packing
preserves the original normalization window.

The result is `Analytic.not_missing_west`, and together with the south
exclusion it yields `Analytic.candidate_diagonal_separators`.

## 6. The final OWN-S upper tail

Once both candidate D separators are known, the last independent condition is

[
s < rac{11}{25}
]

for a canonical OWN south square.

The proof in `Analytic/SouthOuterTail/` separates cardinal W and OWN W.

### 6.1 Cardinal W

A single polynomial majorant bounds the square root appearing in the west
resultant over the entire argument interval. Its squared error is an explicit
nonnegative polynomial. Derivative bounds prove concavity, so only physical
endpoints remain.

### 6.2 OWN W

A naive rectangular scalar bound has one bad endpoint, so the proof does not
claim it is positive everywhere.

Instead, it keeps the actual diagonal coordinates while reducing the two wing
angles. Three corners use the ordinary vertex support. At the exceptional
OWN/OWN corner the proof derives a narrow cone for the diagonal force and then
uses a completed-square radial support estimate. The remaining one-variable
expression is monotone and closes at an exact endpoint.

This repaired argument is documented in
[`ANALYTIC_SOUTH_TAIL_PROOF.md`](../../research/six/lean/ANALYTIC_SOUTH_TAIL_PROOF.md).

The normalized theorem is
`SouthOuterTail.normalized_own_south_upper_tail`.

## 7. Complete reduction and radius equality

`Analytic/CompleteReduction.lean` combines the candidate separators and the
south upper tail through `ReductionInterface`:

```lean
theorem complete_reduction {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P
```

The fixed-pair and corrected diagonal inequalities then show that a normalized
packing at or below the candidate ceiling must have exactly the candidate
radius.

The diagonal scalar proof is described in
[`ANALYTIC_DIAGONAL_PROOF.md`](../../research/six/lean/ANALYTIC_DIAGONAL_PROOF.md).

## 8. Equality and uniqueness

The equality proof retains the actual selected separating sources instead of
forgetting them after obtaining a scalar bound.

At equality:

1. the fixed-pair and diagonal work vanish;
2. the helper angles become the candidate angles;
3. the retained sources give eight contact inequalities;
4. exact disk support makes all eight tight;
5. the five exterior centres are uniquely determined;
6. opposite central contacts determine the central centre;
7. open and closed square point sets are reconstructed;
8. the recorded normalization reflection is absorbed by an actual symmetry of
   the candidate.

This is implemented by `Analytic/SelectedPairWork.lean`,
`Equality/ContactCoordinates.lean`, `Equality/AnalyticContacts.lean` and
`Equality/AnalyticReconstruction.lean`.

Thus `Six.uniqueness` proves congruence to `Six.model` using the unchanged
public `Congruent` relation.

## 9. The current endpoint path

The advertised source route is now

```text
Packing
  -> normalize_of_candidate
  -> complete_reduction
  -> fixed-pair / diagonal radius closure
  -> retained-source eight-contact reconstruction
  -> lower_bound / uniqueness / optimum
```

`Six/LowerBound.lean` and `Six/Uniqueness.lean` do not import a
`Classification` module. The old finite-classification files remain in the
repository as a historical alternative, not as premises of this endpoint.

## 10. Validation status

The analytical route is source-complete. The following have not yet been run
on the current analytical head:

- full Lean compilation;
- Comparator;
- the final axiom audit;
- an elaborated transitive dependency audit;
- independent kernel/Palomar replay.

Until those succeed, the correct description is **source-complete analytical
proof**, not **kernel-verified analytical proof**.
