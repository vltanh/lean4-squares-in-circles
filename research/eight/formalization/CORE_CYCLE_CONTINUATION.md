# Restored pending core-cycle proof

Continuation from published PR #10 head `3281f5f6568696256428bbb9f13185a185892e82`.
The pending `GeometricCoreCycle` source and selected-label coverage interfaces
were recovered from the previous work record. The previous runtime checkout
itself was not available. This checkpoint publishes the recovered argument;
no Lean compilation or CI was run.

## Actual geometric conclusion

Under the coarse E/G/T cuts, every adjacent pair has at least one primary
coordinate greater than 7/12. This concerns the actual coordinates, not the
chosen radial tag. If an outer chart contained a point with both unsigned
coordinates at most 7/12, its circle equation would imply q <= 169/72,
contrary to the coarse radius. Thus a small-primary point belongs only to
core charts in any coherent coarse selection.

The existing core-marker inequalities imply a charged cost strictly above
9/10 at a core/core edge. The seven exact reserves over 9/10 are
24263/1500000, 139/750, 263/1500000, 310763/1500000,
21263/1500000, 148763/1500000, and 121/750. These have been checked with
Python Fraction arithmetic; the corresponding Lean decision remains unrun.

Keep exactly the same selected label at each vertex. On the other six
edges use the original cost greater than 89727/100000. Cyclic telescoping
then contradicts

    9/10 + 6*(89727/100000) - 710/113 = 2453/5650000 > 0,
    2*pi < 710/113.

The charged width sum is nonnegative. The contradiction covers every
original feasible axis and all closed chart junctions. The result transports
to every subsequent state cover, allowing all its core/core angle chains
to be omitted without estimating that later cover's marker functions.

## Publication boundary

This checkpoint adds the coarse conclusion and the later outer-only
coverage interface. The five downstream table adapters and row filters
must be connected before their row deletions are claimed. The earlier
reported 26,258 downstream-row count is not independently re-counted in
this checkpoint. The separate pending eight-quarter-pattern source was
not recovered as a complete file; its closure is not claimed here.
