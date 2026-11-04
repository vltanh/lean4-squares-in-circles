# Two exact conditional B angle unions

This is a compact, zero-credit checkpoint. It contains two complete
conditional angle covers and their source-bound native exact reports.
It excludes neither whole original. See PHYSICAL_COMPLETE_COVER_ATTACHMENT.md.

Reuse the published B340 and I32 archives identified in CHECKPOINT.json.
Extract those and this delta into one dedicated directory. The following
checks input hashes, published-byte reuse, report bindings and the literal
closed angle/reserve table, without repeating the full exact arithmetic:

```sh
python3 -B b_angle_policy_checkpoint/code/replay_b_angle_policy_checkpoint.py \
  --b340 b340_complete_original_package \
  --prior b16a_I32_complete_H_checkpoint --output fresh_transport_check
```

To repeat both complete restricted proofs, add `--replay` and choose a
new output directory. This uses the published independent exact checker,
not the numerical producer. No extra arithmetic replay was launched for
packaging this checkpoint. Source-bound native replay results are under
reports/. A transport receipt is explicitly distinguished from a fresh
arithmetic receipt. All new original and mask credits remain zero.
