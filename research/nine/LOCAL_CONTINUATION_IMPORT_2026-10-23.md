# n=9 — imported local continuation proof sources (2026-10-23)

**Import verified:** 2026-10-23 22:38 UTC. Six previously conversation-local UTF-8 files were uploaded to existing research branch `research/nine-tablefree-hand` using the GitHub connector. Every fetched remote file was compared character-for-character with its locally mounted source, including its trailing newline: **all six matched**. These are new GitHub **contents-API commits**, not a transfer of the original local Git commit objects.

**Research status:** neither the unrestricted n=9 optimal-radius theorem nor all equality packings are proved. The two manuscripts are hand arguments awaiting independent full audit and Lean verification. The two exact-check programs are regression tests, not universal geometric proofs.

## Source and new remote commit mapping

| Repository file | New GitHub commit | Role |
|---|---|---|
| [TWO_COLUMN_SIX_BODY_CAPACITY.md](TWO_COLUMN_SIX_BODY_CAPACITY.md) | [f97d21b](https://github.com/vltanh/lean4-squares-in-circles/commit/f97d21b47f5e9d235593734721b229cf6f65366e) | Alternative full six-body two-column arbitrary-orientation completion argument |
| [TWO_LOADED_COMPONENT_RIGIDITY.md](TWO_LOADED_COMPONENT_RIGIDITY.md) | [7c0cb90](https://github.com/vltanh/lean4-squares-in-circles/commit/7c0cb908313e15b1c713a7487b7bc0624d4dc285) | Independent virtual-work derivation of existing two-loaded rigidity |
| [check_two_loaded_rigidity.py](check_two_loaded_rigidity.py) | [51755b3](https://github.com/vltanh/lean4-squares-in-circles/commit/51755b357b78a66141d16716fc8a053e036a5f5b) | Finite exact arithmetic and physical-stress regression |
| [check_two_column_capacity.py](check_two_column_capacity.py) | [d100213](https://github.com/vltanh/lean4-squares-in-circles/commit/d10021366cacc9910ee8fba8b89e7b359b140c7d) | Finite cap/column completion regression |
| [TWO_LOADED_EXACT_CHECK.json](TWO_LOADED_EXACT_CHECK.json) | [7004a33](https://github.com/vltanh/lean4-squares-in-circles/commit/7004a33759506c5b6f9ad18de42b4f2db9dc37e5) | Historical pinned test report |
| [TWO_COLUMN_CAPACITY_EXACT_CHECK.json](TWO_COLUMN_CAPACITY_EXACT_CHECK.json) | [af6d03a](https://github.com/vltanh/lean4-squares-in-circles/commit/af6d03a164e1af445c3e5675077af5dba0285723) | Historical pinned test report |

The original local draft had last reported local commit `2e109974`. The source-commit fields in historical reports (`08c985ffb8741680293b89b5b417f0c449cc5a1f` and `fa9677fe72331e31691bc479182e4f007176865f`) refer to **local** Git objects; they are not the new GitHub commit IDs. The source-code Git **blob** hashes remain exact and match the published file blobs:

- Two-loaded checker: `014d5a31ab7f2d31c9c73dcd9e85ef6394646fc6`.
- Two-column checker: `9548f96ca5f2602deed6327d575fa621b4a3f86a`.

The source SHA-256 values in the JSON reports match the locally rerun, now-published scripts. The existing JSON timestamps are retained unchanged; importing them does not retroactively change when the original checks were executed.

## Additional run during import

Both source scripts were rerun on the mounted local copies before upload, without writing into repository files:

- `check_two_loaded_rigidity.py`: **PASS**, **23,143** exact assertions; source SHA-256 `1d0194aa4230e3d75a8f6d67689f25b3cc33adac5201ca7669a6a19f1301047f`.
- `check_two_column_capacity.py`: **PASS**, **27,752** exact assertions; source SHA-256 `25204f040cd5a6f601cb37fa5cc68b3269ad500bbae623467dbd12b64a0c0323`.

These assertions exercise exact identities and finite examples, not every continuous square packing.

## Dependency and completion accounting

The remote branch already contained [SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md), giving its own completion proof of the six-body two-loaded case, and [FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md), reducing the five-body case to P. Therefore importing `TWO_COLUMN_SIX_BODY_CAPACITY.md` is an **independent alternative hand derivation**, **not a second new gate closure**. Likewise `TWO_LOADED_COMPONENT_RIGIDITY.md` is an alternative derivation of the already committed global two-load rigidity.

Still **OPEN**: P.ALL, Y.ALL, the remaining noncollinear multi-loaded cyclic/full-completion branch, unrestricted sharp n=9 lower bound, global equality necessity and sufficiency, independent full manuscript audit, Lean kernel formalization and public integration. Do not tick these gates merely because the alternative files have been pushed.

The local manuscripts' historical last sentences saying no remote push had yet occurred are preserved verbatim as snapshot provenance; this import log records their actual GitHub publication.
