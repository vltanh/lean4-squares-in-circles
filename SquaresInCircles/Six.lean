import SquaresInCircles.Six.Uniqueness

/-!
# Six-square proof entry point

This entry point exports the exact construction, unrestricted radius lower
bound, uniqueness and Optimum 6 source declarations. Both endpoint paths use
Analytic.CompleteReduction directly: analytical missing-wing exclusions give
the candidate D edges, the final tail argument supplies the pair domains,
and the analytic fixed-pair/diagonal closure and eight-contact reconstruction
finish the radius and equality arguments.

The former Classification.Reduction boundary is now only a compatibility
adapter and is not imported by the public endpoints. The legacy fixed-row,
ExactCover, pair-envelope and BalancedClosure sources remain in the repository
as historical material, not as premises of this proof path.

No external script's success is a theorem premise. These source declarations
have not been compiled or kernel-audited in this continuation. Source-level
completion and execution evidence are kept separate in
research/six/lean/STATUS.md. The human proof is organized in docs/proof/six.md
and its linked analytical companions.
-/
