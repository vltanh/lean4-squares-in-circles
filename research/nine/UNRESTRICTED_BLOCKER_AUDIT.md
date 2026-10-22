# n=9 unrestricted closure: audited blocker and handoff (2026-10-22)

The unrestricted theorem **has not been proved**. No source in this branch establishes the implication from an arbitrary nine-square `Packing` to a four-anchor stress certificate or a complete set of alternative terminal cases.

## Verified exact oblique witness

For the two rotated upper squares with centers `(-11/20,19/16)` and `(11/20,19/16)`, side frame `u=(99/101,20/101)`, `v=(-20/101,99/101)`, and `q*=1105/256`, direct exact rational evaluation of

`q* - (|c|² + 1/2 + |c·u| + |c·v|)`

gives, respectively, `42573/80800` and `22173/80800`. Both are strictly positive. This verifies the disk-containment calculation in NO_GLOBAL_ORTHOGONAL_FRAME.md. The document's other separation and anchor conditions are logically distinct and must also be retained.

## Actual remaining proof obligations

1. **G2.C4.2c:** eliminate all coordinate-separable four-chain zigzag packings in the remaining 4×3 rank rectangle, using all five nonchain squares. The existing cap and rank lemmas do not prove this.
2. **G2.C4.3:** prove a sharp obstruction for the coherent-side four-chain branch without enumerating an unbounded collection of numerical subfamilies.
3. **G2.O2/O3:** handle pairs separated only along oblique edge normals. The exact witness above disproves global coordinate-separability, so this is essential even for equality.
4. **G2.X:** assemble a truly exhaustive theorem from unrestricted Packing, including every origin-incidence state. Neither the four-chain nor the four-anchor terminal hypothesis is currently known to follow universally.
5. **G4/G5:** only after G2.X, establish the global lower bound and the complete unrestricted equality family. G5.S classifies only the stratified subfamily.
6. **G6–G8:** independent full hand-proof audit, Lean kernel formalization, and public integration.

## Discipline

Do not mark the project completed merely because all *named* conditional terminal lemmas are closed. The missing global quantifier is the theorem. Do not treat small exact checks, numerical feasibility searches, or a draft Lean file as a proof of G2.X. A credible next advance must either close an entire structural branch or supply a precise counterexample forcing a new global invariant.

No Lean build, CI, or kernel replay is claimed in this checkpoint.
