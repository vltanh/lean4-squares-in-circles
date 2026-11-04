# Native progress checkpoints for exact shared bounds

This release preserves two separately scoped pieces of verified progress. It gives no additional original-cell or mask credit and contains no live search frontier.

| Checkpoint | Included actual native gate | Scope |
|---|---|---|
| Direct shared bounds and C readers | Cb882: 158 exact copied bounds; C887: 181 copied bounds within a four-round record | Both saved domains remain OPEN; the Cb fixture is conditional on height component 1 |
| A c744 POST-A1 bounds | 39 weighted uses of the new 414-row family within a five-round record | Only the exact component 3 domain; the original and component remain OPEN |

The large proofs already published for the original A base, C height consequences and complete A1 exclusion are referenced by exact commit, archive digest and input inventory. The original Cb882 eight-domain archive is also pinned in the outer publication notes as the transitive C height prerequisite. Every other referenced native prerequisite is explicitly marked as not bundled. Native absolute path strings and all mathematical/source bytes are retained.

These are source and native-evidence checkpoints, **not self-contained cold proof packets**. The two included audit receipts rehash the bundled files and compare their original, domain and counting headers against the frozen records. They do not repeat weighted arithmetic or reconstruct omitted ancestry. The saved native exact receipts are the evidence for the earlier arithmetic runs.

`READY.json` identifies the two frozen inner inventories and their outer audit receipts. `RELEASE_INVENTORY.json` pins all files in this release except itself. The exact replay inputs are read-only; locally hardlinked records must not be edited. The outer source bindings record the preparation and byte/header-checking scripts. No numerical solver, Lean, Lake, CI, full proof rerun, register update or Git mutation is performed by this release preparation.
