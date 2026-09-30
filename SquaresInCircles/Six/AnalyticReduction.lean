import SquaresInCircles.Six.Analytic.ReductionInterface

/-!
# Analytic secondary-reduction checkpoint

This entry point collects the whole-domain pair and corrected diagonal bounds,
full secondary-source selection, the double-D exclusion, the sharper pi/4
phase restrictions, signed transverse budgets, and the shared-center OWN-wing
bound. It also proves exactly which parts of ReductionHypotheses follow from
the already established normalization.

The remaining tasks are NOT inhabitants of this checkpoint:

* exclude MissingWestWing (indices 6,6, including the historical 53-cell case);
* exclude MissingSouthWing (indices 2,2);
* prove the three conditional OWN-wing tail inequalities in OwnWingTailBounds.

ReductionInterface proves an equivalence with these obligations. It does not
assert their truth, nor obtain them from the old fixed tables. Consequently
radius_of_edges_and_own_tails is a conditional theorem, not the unrestricted
lower bound. The old unrestricted endpoint modules are not imported here.

The new proof bodies contain no admissions or numerical-success premises.
Compilation and the actual kernel/declaration dependency audit are deferred;
the source checkpoint is not a record of Lean acceptance.
-/
