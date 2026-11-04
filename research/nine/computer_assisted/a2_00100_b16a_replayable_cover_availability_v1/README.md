# B16a: preserved replayable-cover evidence

The current reproducible cover has **11 excluded I quarters and five pending
quarters**. The six published complete quarters and five freshly reconstructed
quarters are separately identified in `B16A_REPLAYABLE_COVER_RECOVERY_NOTE.md`.
I20, I21, I22, I31 and I33 remain pending. B16a itself remains OPEN.

This checkpoint preserves the exact evidence records, including all five new
terminal records, the three OPEN prefixes, the current sixteen-tile inventory
and the historical I32 publication. It distinguishes the old fourteen-quarter
claim from the currently available replayable inputs. It does not invalidate
the earlier mathematics or change any original-cell or mask ledger.

The single archive part has SHA-256
`a5e0e136334079483dbe67b3069a57a13a923e9e7af5eed1e75a641040831fac`.
It is a complete xz tar of 1,034,956 bytes; extract it directly with `tar -xJf`.
The archive root is `b16a_replayable_cover_availability_v1`. Its 30 regular
members include 26 unique evidence inputs. `MEMBER_MANIFEST.json` pins every
member other than itself, which is pinned by `ARCHIVE_READY.json`.

Root independently checks xz integrity, every member and its source bytes,
all sixteen rational grid rectangles, the exact eleven/five status split and
the unchanged original path. This publication repeats no arithmetic proof.
`CHECKPOINT.json` names the four required published complete masters and
249 native reconstruction replay input/provenance hashes; dependencies
marked absent must be supplied for a fresh mathematical replay. The archive
is an availability checkpoint, not a self-contained new proof package.

The original register remains **221 CLOSED / 10 OPEN** and the mask register
**8 CLOSED / 24 OPEN**. All nine original squares, 36 corners, 36 physical
pairs, five center cones and exact marked conditions remain required by the
eventual complete B16a proof. No Lean, Lake or CI was run.
