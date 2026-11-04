# Solver-free ordinary rounds for already certified shared bounds

The helper adds no row family, source theorem, propagation rule or terminal
kind. It uses only rows returned by the existing domain-bound context on
the untouched caller, and only names in an explicit shared-source prefix
allow-list. The independent source/domain checks remain those of the
existing row adapter. No LP is solved by this step.

For any accepted row `a·z<=b` whose exact canonical coefficient vector is
an existing objective `c`, use the single integer multiplier `2^40` in the
normal certificate format, whose denominator is `2^40`. Thus the weighted
coefficient vector is exactly `c`, the summed right side is exactly `b`,
and every coefficient residual and residual correction is zero. The usual
upward `2^-20` grid rounding gives `U>=b`, so `c·z<=U` is certified by the
unchanged exact round checker. A lower endpoint uses the ordinary negative
objective, so `-c·z<=U` gives `c·z>=-U`. The normal improvement threshold
`1/2000` is preserved after rounding.

The helper enumerates the same396 objectives as the diagonal engine: both
signs of54 original coordinates/scalars, both signs of two Cartesian
components on36 original center pairs, and both signs of both diagonals on
those pairs. It imports no source-specific auxiliary interval or selected
physical predicate. The18 slope rows of a414-row source remain available
to the ordinary model; a slope row that itself is an exact unit objective
is harmlessly eligible for that same canonical objective.

All printed rows are used. The resulting positions/scalars/differences/
diagonals then pass the existing interval-empty checks, original physical
frame inference and analytic scalar intersection, in exactly the engine's
order. No new rejection witness is introduced. The record retains the
ordinary before/propagated/proposals/after format, so existing old and new
rounds can be merged and replayed without changing any adapter or core.
After such a round, numerical discovery must obtain a fresh phase point.

The exact terminal-contract controls use the frozen independent diagonal
core. Six algebraic fixtures cover signed grid bounds, empty scalar boxes,
the last-bad-pair Cartesian and diagonal witnesses, frame contradiction,
and analytic scalar contradiction. Twelve corrupted certificates or
terminal witnesses are rejected, and the prefix allow-list is exercised.
These fixtures are schema/arithmetic tests, not original-cell proofs.

The real Cb882 component1 seed has also passed a full physical replay using
its unchanged existing checker. One such round proves158 improved endpoints
from158 already accepted whole-original bound rows, with zero numerical
solves. The frozen checker freshly repeats the whole-original source and
its archived physical ancestry. Its report is
`CB882_DIRECT_SHARED_BOUND_FIRST_EXACT_REPLAY.json`, SHA256
`da2b6bcf09dd746f748920c0995aab9708b3b2af67c8411871fc5a0562b3c8b1`.
The one-node component remains OPEN and grants zero original or mask credit.

The producer is `direct_shared_bound_round.py`, SHA256
`be5a16d1106d37a47b1e21591a47b3f90dcf50839ebbf81ed30d0b74a8187d25`.
The separate control receipt is
`DIRECT_SHARED_BOUND_ROUND_EXACT_CONTROLS.json`, SHA256
`ab9a5b3de9bcee638ff41dc4dc9c84689e80455bcaf9c6def45be9e823d470db`.
