# Affine certificates: single-source representation

The ten table modules use the original exact JSON files under
`research/eight/*HAND_DATA.json`. These files were already part of the hand-proof
base; this refactor adds no duplicate data archive. The metadata files retain
the original labels, cuts, axes and edge targets unchanged.

`Eight/AffineDataReader.lean` reads only constructor data. The shared
`Arithmetic/AffineCertificate.lean` computes proposed root brackets,
arctangent endpoints and closed-cover chains. `RowsValid` and
`AffineCover.NumericValid` still check them against the real row semantics.
A malformed input or failed decision is an error, not an assumed lemma.

The removed `ChunkNNN`, `ProofNNN`, `Prepared`, and expanded cover witnesses
are recoverable at `archive/eight-expanded-draft-741c78b`. Do not run the old
expanded generators on this source layout.

This is source deduplication, not elimination of the 660,370-row finite
argument. It does not establish that any decision succeeds or fits a practical
resource limit. No Lean compilation or CI was run. Changes to an external
JSON input require rebuilding its importer; automatic dependency tracking for
those files has not been established.
