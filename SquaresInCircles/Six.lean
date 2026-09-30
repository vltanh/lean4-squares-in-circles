module
public import SquaresInCircles.Six.Uniqueness

@[expose] public section

/-!
# Six-square proof entry point

This entry point exports the exact candidate construction, unrestricted radius
lower bound, uniqueness, and Optimum 6 source declarations. Both endpoint paths
now use the analytic fixed-pair bound and the eight-contact equality argument.
The legacy BalancedClosure, pair-envelope checker, and its derivative-cover
proofs are not used by those endpoints.

The remaining internal finite classification is deliberately isolated in
Classification.Reduction. Replacing that boundary by the three open analytic
geometric facts would remove the remaining fixed-row/ExactCover dependencies;
this entry point does not claim that replacement has already happened.

No external script's success is a theorem premise. Source declarations have
not been compiled or kernel-audited in this continuation. The current state
and remaining work are recorded in research/six/lean/STATUS.md and
EXTERNAL_DEPENDENCY_REMOVAL_CHECKLIST.md.
-/
