# Affine tables

A table module proves the charged bound of one affine table (`charged_bound`) from finite
facts, each checked by the kernel (`decide +kernel`) on a Boolean function with a soundness
theorem:

- every row satisfies its claim (`AffineTableRow.Claim`): `checkRow` in
  `Arithmetic/RowCheck.lean`, with `checkRow_claim`. After the axis reversal of
  `PreparedRow.core`, each inequality of a row is `c₀ + c₁ u + c₂ sin u + c₃ cos u > 0` (or `≥ 0`)
  on its angle interval, decided by a Bernstein test of degree six, then ten (`TrigLin.lean`).
  Circle rows bound the norm by `√V ≤ (V / h + h) / 2` on pieces of the interval. The quarter
  `k ≤ 3` of a row gives `sin φ` and `cos φ` as `± sin u` or `± cos u`.
- the rows cover every required angle of every arc pair, axis and half: `coverBlock` in
  `Arithmetic/RowCover.lean`, a walk over the sorted rows for a block of source arcs, with
  `coverBlocks_sound` for blocks that cover all arcs; the pairs and axes that no feasible
  separator has (`ExcludedArcs`) are skipped, and in the tables written with `--core` also the
  pairs of two core arcs;
- the arc boxes enclose the exact arcs of `Meta.lean` (`boxesRange`, `TableCtx.valid_of`); the
  arctangent endpoints are valid and every tangent value of an arc has one (`atanRange`,
  `atanFoundRange`, `endpointsValid_of_blocks`); the fixed-point arctangent intervals of the
  arcs enclose theirs (`alphasRange`, `CoverCtx.valid_of`); the state chains close
  (`StateChains.NumericValid`).

All arithmetic is in fixed point, integers over `10 ^ 24` with outward rounding
(`Arithmetic/Fixed.lean`); the decimal data are exact in it.

The data of a table `NAME` are integer text files `data/eight/affine/NAME.rows`, `.arcs` and
`.atan`, read by the elaborators `nat_rows%` and `int_rows%` of `Eight/IntRows.lean` as terms
with raw literals. `scripts/eight/affine_rows.py` writes them from the table's JSON; it checks
every row and the coverage with the same integer algorithm and chooses the circle pieces. With
`--lean MODULE` it also writes the modules

- `MODULE/Meta.lean`: the exact arcs, cuts, word, charges, targets and axes of the table;
- `MODULE/Context.lean`: the arc boxes, the endpoint lookups and the arctangent intervals (120
  arcs a theorem), the scalars, the state chains and the coverage data;
- `MODULE/AtanNN.lean`: the arctangent endpoints, 12 a theorem;
- `MODULE/RowsNNN.lean`: a chunk of 2000 rows, 100 a theorem;
- `MODULE/Data.lean`: the list of chunks;
- `MODULE/CoverNN.lean`: the coverage walks, each over sources with at most 8000 arc pairs,
  axes and rows; a walk starts at its first row by the chunk index and an offset, so that the
  kernel does not walk through the rows before it;
- `MODULE.lean`: all row claims, the coverage and `charged_bound`;
- `MODULE/Enhanced.lean` (with `--enhance`): the bound for targets raised by given margins.
  The rows are checked against the raised targets, and the claims for the table's own targets
  follow by monotonicity (`AffineRow.claim_of_target_le`).

With `--core markers` (the coarse table) the costs of two core arcs follow from rational bounds
of the markers of the core arcs at their tangent endpoints (`markers_valid`, `budgets_valid`,
`Candidate/GeometricCoreMarker.lean`), and the same bounds with the target `9/10` show that no
edge joins two core squares (`no_adjacent_core`). With `--core free` (the tables used after the
coarse stage: `HLowerAffine`, `DUpperAffine` and the three mismatch tables) `charged_bound`
assumes `NoAdjacentCore`.

The generator records the hashes of the input and of the data files in `generation_index.json`,
since Lake does not track the data files. The blocks keep the kernel's memory for each theorem
below about 1.5 GB.
