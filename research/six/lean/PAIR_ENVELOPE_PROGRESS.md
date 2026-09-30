# Analytic pair-envelope continuation

Baseline: `d78adbcb044c211782f8fe0e97f63e19ac7b16c7`, PR #7.
Compilation remains deferred. Checked source items do not assert kernel acceptance.
The existing `ANALYTIC_PROGRESS.md` remains the overall completion ledger.

## Intended replacement

Use central edge multipliers equal to one and the exact candidate outer
multipliers r and m. Bound the resulting central-force excess explicitly by
the candidate central box. A smooth upper support gives a lower minorant.
Its only nonsmooth walls are n=0, w=0 and n=w. Prove coordinate and diagonal
concavity on the geometrically determined sectors, then evaluate their actual
boundary vertices. No interval subdivision or generated stress-table checker
may be a mathematical premise.

The bit-dependent helper rectangle used by the proposed replacement is an
explicit input until the separate analytic candidate-domain reduction proves
it for arbitrary packings. Writing the pair inequality must not silently
mark that classification/domain obligation complete.

## Checklist

- [ ] Recover and review the five attached fixed-pair/rotating-length source files.
- [ ] Supply their pure candidate-constant and root-derivative dependencies.
- [ ] Prove positive radicands and uniform harmonic curvature bounds.
- [ ] Prove the opposition sign needed for the alternate source.
- [ ] Assemble coordinate and diagonal concavity on every geometric sign sector.
- [ ] Prove the finite endpoint reduction dictated by the rectangle and the three walls.
- [ ] Prove all resulting endpoint inequalities by visible rational/Taylor/root algebra.
- [ ] Obtain the common lower bound and identify the equality-compatible sources.
- [ ] Connect the fixed stress and central-force correction to an actual packing.
- [ ] Adjust the diagonal remainder and equality argument to the fixed-pair linear bound.
- [ ] Derive the required bit-dependent domains without computational classification.
- [ ] Reconnect the unrestricted lower-bound/uniqueness endpoints and audit dependencies.

The original variable-weight `PairLowerBound` still has computational
dependencies. It is not replaced until the appropriate new theorem is proved
and its actual call sites are switched.
