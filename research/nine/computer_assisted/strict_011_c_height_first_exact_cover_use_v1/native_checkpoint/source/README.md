# Prepared C-height complete-tree and discovery attachment

This package is a separate version of the reviewed strengthened strict
`011/00` checker. It adds the explicit union kind
`strict011_C_height_four_way_v1`, tied to the frozen C-height design
`06aba6fc518e44d1b859bccb9cc81b6ab57ef5b2df91970f654ba9fe8ab3fd79`.
No frozen checker, driver, foundation source or active proof tree is edited.

The base state format and the complete 4/8/2 dispatch remain unchanged.
`height_context_adapter.py` reconstructs a separate inherited record envelope,
binds its originating node and exact certified parent state, and admits only
the selected fixed height row. The complete checker requires every context
to equal its ancestor-derived expectation and starts the accepted scalar
checker before its first height child. A second height union on a path is
rejected.

`height_discovery_attachment.py` provides proposal-only current rows, exact
child construction and a fresh atomic store. It imports the accepted rational
and atomic core unchanged, calls no optimizer, and offers no unverified
arbitrary-tree resume operation. It does not declare a full caller covered.

## Observed preparation

`fresh_controls/PREPARATION_CONTROLS.json` records exit-zero preparation:

- two complete exact replays of one-node roots without height unions;
- four exact local conditional height-bound rounds with positive hand-chosen
  weights and zero residuals;
- a five-node first-use candidate and a 19-node mixed height/4/8/2 candidate;
- 32 rejections covering malformed unions, parent/context mismatches,
  unrestricted height rows, lost ordinary-child inheritance, arbitrary child
  narrowing, a second height union, and reused scalar output;
- injected ENOSPC preserving the old atomic manifest and exact whole root.

No valid complete height cover has been replayed yet. No scalar process or LP
has been started by these controls. Local conditional arithmetic is labeled
separately from global cover acceptance. `HEIGHT_CONTEXT_COMPLETE_TREE_HAND_PROOF.md`
explains the physical implication, induction, state/domain distinction and
the held first-use gate.

## Held first actual global cover use

`run_first_use_gate.py` is an exact-only launcher. After source review it will
verify every frozen packet member, run the five-node candidate in a fresh
`python -B -S` checker, require the fresh universal scalar and all four exact
bound rounds, and rehash the sources. It has no numerical optimizer requirement.
The candidate necessarily remains OPEN; no ledger increment is made.

The outer `HELD_FIRST_USE.json` contains the concrete source binding and argv.
It must not be executed before the root source review authorizes that gate.
The separate strengthened corner pilot remains unchanged and has its own
real-LP positive-weight requirement.

## Reproduce only the preparation controls

Use new, absent output locations. The scalar-parent location must be outside
all frozen source packages; its child output locations are only reserved or
used for explicit rejection controls, not for a valid scalar replay.

```bash
python -B -S -u global_work/strict011_c_height_tree_v1/check_height_preparation.py \
  --foundation global_work/strict_011_rebuilt_v3 \
  --corner-folder global_work/strict011_four_product_layer_v2 \
  --guard-folder global_work/strict011_universal_021_applications_v2 \
  --height-folder global_work/strict011_c_height_complement_note_v1 \
  --output-folder NEW_HEIGHT_PREPARATION_FOLDER \
  --scalar-parent NEW_EXTERNAL_SCALAR_RESERVATION_FOLDER
```

The source transformation records every change from the accepted strengthened
wrapper and verifies unchanged helper and old-dispatch ASTs. The frozen source
binding makes the pending actual-use boundary explicit.
