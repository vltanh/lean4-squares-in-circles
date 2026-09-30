# n=6 proof status: analytic normalization source closed

**The analytic normalization source is complete and connected.**
The completed endpoint is `Normalization.normalize_of_candidate`, exported by
`SquaresInCircles/Six/AnalyticNormalization.lean` and the isolated analytic
entry point. It starts from the original Packing predicate and the candidate
radius bound; pins, sectors, the small central box and separator choices are
not added assumptions on the caller.

**The complete unrestricted human-analytic n=6 theorem is still unfinished.**
The remaining work is the separate downstream D-edge/tail classification and
common pair-envelope conversion, followed by reconnection and validation of
the existing final stress/equality/public endpoints.

Compilation and kernel/axiom acceptance remain deferred. Source completion is
not reported as an executed Lean proof check.

## Normalization completed in this continuation

The strong-core forbidden-marker proof was already analytic. The remaining
normalization dependencies have now been replaced and connected:

1. A universal sixty-degree two-pin covering lemma from one completed-square
   far-corner obstruction, plus the western-flank completed-square argument.
2. OWN east/west profiles and broad windows from trigonometric concavity and
   explicit endpoint inequalities.
3. Cardinal cap-facing directions and fixed pins from geometric quadrant
   cases, exact cap support and the actual open piercing point.
4. Five-pin covering and the finite bijection on actual interiors. Unique pin
   assignment itself rules out the wrong primary locations and gives every
   labelled window; no separate numerical window check is used.
5. Allowed central axes directly from the fixed pin coordinates and strong-core
   secondary exclusion. Both the original and reflected PinPacking constructors
   now use these analytic results.
6. The existing analytic OWN moving-pin and W/D four-axis arguments are fully
   connected to those analytic broad-window inputs.
7. Appendix A's eight finite checks are replaced by whole-domain projection
   reductions to two forward secondary sources, both using one multiplier
   triple. W-secondary uses an affine radical majorant; D-secondary uses the
   explicit radical second derivative and concavity. Both reduce to the seven
   geometric vertices of the order/sign domain.
8. The actual force, norm and support identities connect those positive bounds
   to the geometric contradiction. D is canonically OWN. Both core-exclusion
   inputs are explicit at the Appendix A call site.

The D-secondary W-force norm has the positive mixed term
`53/200 + (9/40)*sin(u-t)`. An intermediate erroneous sign/dominance argument
was corrected and removed; the completed source uses the separate curvature
proof, not that intermediate claim.

The resulting interface retains the strong/coarse box, side-nearest chart
bounds, genuine affine markers, fixed/moving pins, windows, cyclic order,
cardinal-preferred two-choice rule, one helper per cardinal side, N25+, both
opposite-cardinal budgets and D-own. The exact candidate-radius central box and
budget refinements are exported with both cardinal hypotheses intact. The one
possible global diagonal reflection remains explicitly recorded.

## Entry points, companion and review

- `SquaresInCircles/Six/AnalyticNormalization.lean`: normalization and its
  refinements, independent of downstream computational classification.
- `SquaresInCircles/Six/Analytic.lean`: includes that normalization together
  with the earlier analytic diagonal remainder and constant results.
- `SixNormalizationAxiomAudit.lean`: configured deferred audit commands, not
  executed output.
- `ANALYTIC_NORMALIZATION_PROOF.md`: human-readable argument, including the
  two completed squares, the pin/window deductions, correct force formulas,
  curvature identity and positive endpoint reserves.
- `NORMALIZATION_DEPENDENCIES.md`: exact scope of the import/call-site review.
- `ANALYTIC_PROGRESS.md`: active completion ledger.

The reviewed manually recorded Six-only import graph reaches 82 modules with
124 Six-to-Six edges and no cycle or listed computational module. This static
review is not a Lean elaboration/axiom audit, nor a fresh audit of the existing
Common, Seven, Geometry or Mathlib libraries. The legacy Certificates namespace
in PinData contains only ordinary real constants and finite label data.

Local exact algebra reviewed 34 explicitly displayed polynomial/rational
comparisons, including the forced endpoint values. No numerical search,
interval subdivision, certificate replay or generated-table verification was
used in this normalization conversion. These calculations are development
checks only, never inputs to the Lean theorems. No GitHub runner, remote
computation or Lean compiler was used.

## Remaining analytic proof work outside normalization

The diagonal remainder inequality and its unique zero are analytic on their
explicit domain. The present reduction of every packing to that later, tighter
domain still uses the fixed D-edge classification and tails. Those large-row
arguments need conceptual whole-domain replacements. The common adjacent-pair
lower envelope also still uses outer and derivative covers that must be
replaced.

Existing LowerBound, Uniqueness, equality reconstruction and public Optimum 6
source must be reconnected through those analytic-only dependencies. They are
not accepted as the finished human-analytic unrestricted theorem merely because
normalization is now converted. Final compilation and transitive kernel/axiom
checking are an additional deferred validation requirement.

Historical UPLOAD_AUDIT and mirror/build logs concern the old computer-assisted
route. Their old counts and hashes do not validate this source checkpoint.
The original Packing and Congruent predicates and public problem statements
were not changed during this normalization completion.
