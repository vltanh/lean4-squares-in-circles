# Affine tables

A table module proves the charged bound of one affine table (`charged_bound`) from finite
facts, each checked by the kernel (`decide +kernel`) on a Boolean function with a soundness
theorem:

- every row satisfies its claim (`AffineTableRow.Claim`): `checkRow` in
  `Arithmetic/RowCheck.lean`, with `checkRow_claim`. After the axis reversal of
  `PreparedRow.core`, each inequality of a row is `c₀ + c₁ u + c₂ sin u + c₃ cos u > 0` (or `≥ 0`)
  on its angle interval, decided by a test of degree three, then by Bernstein tests of degree six
  and ten (`Arithmetic/TrigLin.lean`). Circle rows bound the norm by `√V ≤ (V / h + h) / 2` on
  pieces of the interval. The quarter `k ≤ 3` of a row gives `sin φ` and `cos φ` as `± sin u` or
  `± cos u`.
- the rows cover every required angle of every arc pair, axis and half: `coverBlock` in
  `Arithmetic/RowCover.lean`, a walk over the sorted rows for a block of source arcs, with
  `coverBlocks_sound` for blocks that cover all arcs; the pairs and axes that no feasible
  separator has (`ExcludedArcs`) are skipped, and in the tables written with `--core` also the
  pairs of two core arcs;
- the arc boxes enclose the exact arcs of `Meta.lean` (`boxesRange`, `TableCtx.valid_of`); the
  tangent endpoints of the arcs have the arctangent intervals of the integer bounds of
  `Arithmetic/AtanBounds.lean` (`atanEnds`, `endpointsValid_atanEnds`); the fixed-point
  arctangent intervals of the arcs enclose theirs (`alphasRange`, `CoverCtx.valid_of`); the state
  chains close (`StateChains.NumericValid`).

All arithmetic is in fixed point, integers over `10 ^ 24` with outward rounding
(`Arithmetic/Fixed.lean`); the decimal data are exact in it.

The data of a table `NAME` are integer text files `data/eight/affine/NAME.rows` and `.arcs`,
read by the elaborators `nat_rows%` and `int_rows%` of `Eight/Certificates/Readers.lean` as terms with raw
literals. `scripts/eight/affine_rows.py` writes them from the table's JSON; it checks every row
and the coverage with the same integer algorithm and chooses the circle pieces. With
`--lean MODULE` it also writes the modules

- `MODULE/Meta.lean`: the exact arcs, cuts, word, charges, targets and axes of the table;
- `MODULE/Context.lean`: the arc boxes and the arctangent intervals of the arcs (120 arcs a
  theorem), the scalars, the state chains and the coverage data;
- `MODULE/RowsNNN.lean`: 10000 rows each, 200 rows a theorem;
- `MODULE/Data.lean`: all rows, as the list of their parts;
- `MODULE/CoverNN.lean`: the coverage walks, twelve a module, each over sources with at most
  8000 arc pairs, axes and rows; a walk starts at its first row by the part index and an
  offset, so that the kernel does not walk through the rows before it;
- `MODULE.lean`: all row claims, the coverage and `charged_bound`;
- `MODULE/Enhanced.lean` (with `--enhance`): the bound for targets raised by given margins.
  The rows are checked against the raised targets, and the claims for the table's own targets
  follow by monotonicity (`AffineRow.claim_of_target_le`).

With `--core markers` (the coarse table) the costs of two core arcs follow from rational bounds
of the markers of the core arcs at their tangent endpoints (`markers_valid`, `budgets_valid`,
`Candidate/GeometricCoreMarker.lean`), and the same bounds with the target `9/10` show that no
edge joins two core squares (`no_adjacent_core`). With `--core free` `charged_bound` assumes
`NoAdjacentCore`.

The ten tables and their options:

| module | JSON input | options |
| --- | --- | --- |
| `CandidateCoarseMismatch` | `CANDIDATE_COARSE_MISMATCH.json` | `--enhance 15,13,18,12,15,23,6 --core markers` |
| `HLowerAffine` | `H_LOWER_AFFINE.json` | `--core free` |
| `DUpperAffine` | `D_UPPER_AFFINE.json` | `--core free` |
| `Mismatch026To01Affine` | `MISMATCH_026_TO_01_AFFINE.json` | `--core free` |
| `Mismatch01To015Affine` | `MISMATCH_01_TO_015_AFFINE.json` | `--core free` |
| `Mismatch015To001Affine` | `MISMATCH_015_TO_001_AFFINE.json` | `--core free` |
| `TLowerAffine` | `T_LOWER_AFFINE.json` | |
| `TUpperAffine` | `T_UPPER_AFFINE.json` | |
| `GLowerAffine` | `G_LOWER_AFFINE.json` | |
| `GUpperAffine` | `G_UPPER_AFFINE.json` | |

for example `python3 -I scripts/eight/affine_rows.py PATH/T_UPPER_AFFINE.json --lean TUpperAffine`.
The JSON inputs are not part of the repository; `generation_index.json` records their hashes and
those of the data files, since Lake does not track the data files.
