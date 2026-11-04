# Native evidence for exact shared bounds

This checkpoint preserves three successful native exact replay results, their
actual frozen records, source code, controls and explicit dependency maps.
All three saved domains remain OPEN. The accepted original register remains
**222 CLOSED / 9 OPEN out of 231**, and whole masks remain **8 CLOSED /
24 OPEN out of 32**. This publication adds no original, mask, positional-root
or roadmap closure. The full-mask target retains strict-radius scope.

| Saved gate | Exact native result | Applicability |
|---|---|---|
| Cb882 direct shared bounds | 158 deductions and 158 weighted source rows in one round | Only the saved component-1 domain |
| C887 direct shared bounds | 181 direct deductions within four rounds, 390 total deductions and 532 premise rows | The unchanged original C887 caller |
| A-c744 POST-A1 bounds | 39 weighted uses within five rounds, 546 deductions and 1,245 premise rows | Only the identical component-3 predicate; not the whole original |

The helper puts previously certified original-variable bounds into the
existing exact round format, using ordinary rational rounding and propagation.
The saved C records exercise the bounded-memory readers on actual records;
the Cb result agrees with its earlier eager reader on the listed mathematical
fields. The A3 source family has 414 conditional rows and cannot transport
its component predicate or auxiliary choices to another component.

The [unchanged native release](native_evidence/README.md) contains the full
source and dependency explanations. Every one of its 100 inventoried files
and its inventory are preserved byte for byte. The independent
[root publication review](NATIVE_PROGRESS_CHECKPOINTS_ROOT_PUBLICATION_REVIEW.md)
rehashes all release members and 75 native source occurrences, checks all
three saved domain/count/hash attachments, and recovers the referenced
publication manifests from their exact commits. Its JSON receipt and
review source are included beside the hand review.

These are **native evidence checkpoints, not self-contained cold proofs**.
Published A-base, C-height, complete A1 and transitive Cb882 archive identities
are explicit. Other referenced native prerequisites are marked as not
bundled. Original absolute paths, historical pending flags and exact record
bytes remain unchanged. The new outer identity review does not repeat
weighted arithmetic or reconstruct the omitted transitive ancestry.

For a read-only check of either inner package's bytes and saved headers, run
its bundled standard-library checker from this directory, for example:

```sh
python -B -S native_evidence/outer_publication_notes/verify_native_checkpoint_inventory.py native_evidence/direct_shared_bounds_and_C_lazy_readers_native_v1
python -B -S native_evidence/outer_publication_notes/verify_native_checkpoint_inventory.py native_evidence/A_c744_component3_POST_A1_bounds_native_v1
```

Those commands perform identity and header checks only. Actual future cold
proofs require all frozen dependencies and the separately reviewed transport.
No live search frontier is copied or changed; no solver, Lean, Lake or CI
is run by publication. `PUBLICATION_MANIFEST.json` pins every file in this
wrapper except itself, without modifying the frozen inner release.
