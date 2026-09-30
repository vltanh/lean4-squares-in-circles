module
public import SquaresInCircles.Six.Analytic.CardinalWingClosure
public import SquaresInCircles.Six.Analytic.CanonicalSouthSign
public import SquaresInCircles.Six.Analytic.OwnWingFrontier

@[expose] public section

/-!
# Analytic secondary-reduction checkpoint

The active target is a completely analytic hand proof. This checkpoint exports
the whole-domain pair and corrected diagonal bounds, full secondary-source
selection, the double-D exclusion, and the shared-center/transverse budgets.
The lower OWN-S tail is proved, with the stronger positive-deviation result
in CanonicalSouthSign. The OWN-W outer tail follows from candidate D edges.

CardinalWingClosure closes both mixed sources when W and S are cardinal.
CardinalSouthTail now excludes MissingSouthWing for every cardinal W, including
the formerly unresolved large positive OWN-S case. Its four-edge argument uses
weights 4,10,3,3 and whole-domain monotonicity/concavity, not a stress table.

CoupledWingBudgetSharp proves s-w<24/25 for two OWN wings. In a missing-west
configuration, OwnWingFrontier combines this with the one-radian W/D gap to
obtain d-s>1/25. All these bounds hold in the unchanged normalized frame.

The remaining unrestricted analytic tasks are:
* exclude MissingWestWing with at least one OWN wing and d>3/5;
* exclude MissingSouthWing with W OWN;
* prove the canonical OWN-S upper tail s<=11/25.

ReductionInterface states the exact three obligations without inserting them
into Packing. No old fixed-table theorem supplies them here. The public
endpoints still use Classification.Reduction and its internal finite checks;
those endpoint modules are deliberately not imported by this checkpoint.

These are source proof bodies, not records of executed compilation or kernel
acceptance. The hand argument for the new closure is written in
research/six/lean/ANALYTIC_CARDINAL_SOUTH_PROOF.md. STATUS.md is the live ledger.
-/
