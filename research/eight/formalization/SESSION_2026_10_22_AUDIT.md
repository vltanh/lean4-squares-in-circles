# PR10 source audit — 22 October 2026

This audit does not claim Lean compilation or proof closure.

## Verified source inventory

The negative second-word edge-two source already has `original_scalar` over all four physical owners and both signs of the quarter deviation (`SecondOuterNegativeTwo.lean`). Its `actual` cycle bridge is in `SecondOuterNegativeTwoCycle.lean`.

The negative edge-three source has original owner lemmas for the first and upper halves (`SecondOuterNegativeThreeFirstOwners.lean`, `SecondOuterNegativeThreeUpperOwners.lean`) and actual zero-target, diagonal-source and diagonal-target contact estimates. These local lemmas do not by themselves prove the global signed-cycle dispatcher.

The public `GeometricModel/SharpAssembly.lean` still uses `Candidate.capture`; the unconditional table-free `SharpSourceEntry` is not established. Do not change the public import until the original-owner source cases and equality recovery are discharged.

## Remaining obligations

1. Finish far EH1/TD2 and negative DE/EH–positive BT3 signed mass concentrations, including their actual original-owner adapters.
2. Assemble exhaustive signed original-owner dispatcher with no extra selected-owner assumptions.
3. Connect global normalization to the source theorem, then derive untouched-source equality and five-parameter rigidity.
4. Compile and kernel-check in a separate authorized verification pass.

Historical checklists may be stale; verify theorem signatures rather than treating their gate labels as proofs.
