# Fresh strict `011/00`: complete-tree exact checker

This is a small preparation packet. The full mask remains **OPEN**. It adds
complete 4-way original-inset, 8-way physical SAT, and 2-way closed-angle
assembly to the independently reviewed fresh unnormalized root model. It
does not import any old `001/00` root, registered cell path, normalization,
conditional theorem, optimizer, or numerical discovery result.

Read `COMPLETE_COVER_HAND_PROOF.md` for the induction, exact physical covers,
and the one manually derived conditional exclusion. The fresh model and
independent adapter remain frozen in the sibling `strict_011_full_root_v2`
folder. `SOURCE_BINDING.json` pins every local source, fixture, and control
receipt plus the exact external arithmetic dependencies.

## Recorded controls

`exact_controls_v1/COMPLETE_TREE_CONTROLS.json` records five successful complete
cover replays and 18 damaged-input rejections. The fixtures are:

| Fixture | Nodes | Excluded leaves | OPEN leaves |
| --- | ---: | ---: | ---: |
| Full fresh root | 1 | 0 | 1 |
| Complete AB inset union | 5 | 1 | 3 |
| AB inset union, inherited bound, D angle union | 7 | 1 | 4 |
| Complete H/I physical SAT union | 9 | 0 | 8 |
| Complete D angle union | 3 | 0 | 2 |

The AB negative-x branch has an exact four-row contradiction with positive
reserve `99516432383215/70368744177664`. This closes one conditional domain;
the other AB alternatives remain explicit OPEN leaves. There is no whole-mask
or registered-original credit.

## Replay in a fresh output directory

From the shared workspace, with the sibling frozen model and pinned `b_work`
arithmetic helpers present:

```sh
python -B -S global_work/strict_011_complete_cover_v1/check_complete_tree_controls.py \
  --workspace /workspace/scratch/f9f48fcfb253 \
  --output-directory /tmp/strict011_complete_controls_fresh
```

The command refuses to reuse an existing output directory. It performs exact
rational controls and does not start a numerical solver. Choose a new empty
output pathname for each replay. Do not use `python -O`; the entry point
explicitly rejects it before import dispatch.

To replay one existing tree without creating duplicate fixture inputs:

```sh
python -B -S global_work/strict_011_complete_cover_v1/verify_strict_011_complete_tree.py \
  global_work/strict_011_complete_cover_v1/exact_controls_v1/complete_AB_proxy_union/manifest.json \
  /tmp/strict011_ab_proxy_fresh_report.json \
  --workspace /workspace/scratch/f9f48fcfb253
```

The output file must not already exist. The expected result for this fixture
is `PASS_COMPLETE_STRICT011_COVER_WITH_OPEN_DOMAINS`, with one excluded and
three OPEN leaves. Only a future complete exact tree with zero OPEN leaves
could return `PASS_COMPLETE_STRICT011_PHYSICAL_TREE`; publication and mask
acceptance remain separate gates.
