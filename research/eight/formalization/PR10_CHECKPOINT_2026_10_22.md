# PR #10 continuation checkpoint — 2026-10-22

Branch at inspection: `formalize/eight-uncompiled-draft`, `ef0c742f4f317e6b94591865c3967e07800d50ae` (22:03:52 UTC).

## Verified from current source
- The genuine negative EH1 / positive TD2 source and scalar assemblies are already present, including far-low and far-high files. Earlier handoff entries calling them absent are stale.
- The negative DE3 / positive BT3 branch has source data, tilt, ranges, blocks and original stress, but source-level closure still needs the scalar inequality and global dispatch.
- The negative EH1 / positive BT3 branch has data and polynomial files and an original signed-block decomposition, but requires scalar assembly and source-level contradiction.
- The final global source/equality pullback must import and apply the two BT3 exclusions, then prove the last source dispatcher without assuming a case away.

## Immediate gates
1. Complete the DE3/BT3 scalar certificate and source exclusion from the *actual* TD0/DE3/EH0 edges.
2. Complete EH1/BT3 scalar and source exclusion retaining the original EH multiplier and D block.
3. Integrate both into global owner case analysis and equality/uniqueness pullback.
4. Audit all imported lemmas and compile under the standard Lean kernel in a separate validation pass.

Do not mark the proof complete merely because the hand arguments or uncompiled declarations exist. No Lean compilation or CI was run in this continuation. Avoid sampled-angle grids, new axioms, and claims of verified closure before checking the source chain.
