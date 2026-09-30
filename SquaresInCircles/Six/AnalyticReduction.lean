import SquaresInCircles.Six.Analytic.CardinalWingClosure
import SquaresInCircles.Six.Analytic.CanonicalSouthSign

/-!
# Analytic secondary-reduction checkpoint

This entry point includes the whole-domain pair and corrected diagonal bounds,
full secondary-source selection, the double-D exclusion, phase restrictions,
and the shared-center/transverse budgets. The lower OWN-S tail is now proved;
CanonicalSouthSign gives the stronger positive-deviation result.

The two mixed source configurations are analytically excluded when W and S
are cardinal. CardinalWingClosure constructs ReductionHypotheses and proves
radius equality in that complete central-bit branch. The mixed-south argument
also applies with W cardinal and any S choice when s<=12/25.

The remaining unrestricted tasks are still substantive:
* finish MissingWestWing with at least one OWN wing (including the old hard region);
* finish MissingSouthWing with W OWN, or W cardinal and s>12/25;
* prove the negative OWN-W and positive OWN-S outer tails.

ReductionInterface states those remaining premises without inserting them into
Packing. No old fixed-table theorem supplies them here. The unrestricted
endpoint modules are deliberately not imported by this checkpoint.

All results here are source proof bodies, not records of executed compilation
or kernel acceptance. See research/six/lean/STATUS.md for the single live ledger.
-/
