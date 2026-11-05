# Three exact C887 terminal leaves in the complete retained cover

The fresh independent terminal replay excludes C887 leaves **29, 30 and 64**.
It retains the complete published 91-node cover, including every other parent
and leaf. The result is **3 excluded and 70 OPEN leaf domains**. Original
`negative-887236b78100baf3`, mask `001/00`, remains OPEN. This checkpoint adds no
original-cell or mask credit.

All three leaves lie under the same complete eight-way D/G separation cover.
The accepted original geometry requires the selected D/G separating normal to
have positive vertical component. Leaf 29 selects `+u_D` while its certified D
slope is in `[-1,0]`; leaves 30 and 64 select `-v_D` and `-v_G`, whose vertical
components are negative. The unchanged existing terminal rule excludes all
three, including the closed zero-angle face.

## Fresh checks and explicit proof reuse

`EXACT_REPLAY.json` records the observed successful run of the unchanged
independent record core on the three new terminal records. It also freshly
checks all 91 parent/child states and the nine complete proxy covers, six
complete SAT covers and three closed angle covers. Twelve damaged
original/path/terminal/status controls are rejected. The 88 other node payloads
are byte-identical to the published source, and the new manifest is checked
against the exact permitted three-leaf delta.

The complete accepted old C887 proof is explicitly reused. Its 57 weighted
rounds, 8,780 deductions and original/source ancestry are **not repeated** by
this continuation. The gate rehashes its exact report, full packet inventory,
543 recursively named source/decoder identities and all 91 original payloads.
This is a new exact continuation of an accepted proof, not a fresh replay of
every historical weighted deduction. No numerical optimizer, new row family,
Lean, Lake or CI is used.

The fresh report SHA256 is
`ab1f2aac0ad99539365df036ce3c884b6af2f7ebecc5c890fdd8b35df5f3a51a`.
The complete new manifest SHA256 is
`276bae5827e64c8e9cabd1c5907d5047b26cde6cabc68fee9440a44f067f7e09`.
`OBSERVED_EXECUTION.json` distinguishes the observed exact-checker exit 0 from
the earlier build process whose exit was not recovered after a context change.
The independent gate checks that builder's entire output.

## Published dependencies and the thin continuation

`continuation/` contains the new complete manifest and exactly three changed
node payloads. `PUBLISHED_DEPENDENCIES.json` gives all 88 unchanged node paths
and hashes in the already published C height packet. It also identifies the
accepted native and portable reports. The old packet is required; this folder
does not duplicate its large ancestry or claim to replace it.

The published package is
`research/nine/computer_assisted/c_original_height_consequences_v1`.
The exact outer archive/input/portable-receipt metadata and reproduction README
are copied under `published_dependency_metadata/`. Its two delta archive parts
and the published A/Cb base archives materialize the old packet with input
manifest SHA256
`06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b`.

The new `code/` sources and their source binding are immutable. The copied
historical helper also contains unused routines from an earlier center-row
experiment. The terminal gate calls only its hash/source/state/parent-cover
validation helpers; no center-family routine supplies a terminal premise.

## Reproduction

Use Python 3.12 with assertions enabled. Start with the exact materialized old
packet, for example `/tmp/recovered_c_height_packet_064e4aa`, and fresh output
paths. The historical transport requires the replay source, tree and output
to be outside `/workspace`, so first copy `code/` to a fresh `/tmp` directory.

```sh
python3.12 -B -S verify_packet.py \
  --historical-packet /tmp/recovered_c_height_packet_064e4aa

cp -R code /tmp/c887_terminal_sources_fresh

python3.12 -B -S /tmp/c887_terminal_sources_fresh/build_continuation.py \
  --packet /tmp/recovered_c_height_packet_064e4aa \
  --tree /tmp/c887_terminal_tree_fresh

python3.12 -B -S /tmp/c887_terminal_sources_fresh/verify_continuation.py \
  --packet /tmp/recovered_c_height_packet_064e4aa \
  --tree /tmp/c887_terminal_tree_fresh \
  --output /tmp/c887_terminal_replay_fresh
```

The builder reconstructs all 91 exact payloads from the old packet and the
three literal terminal replacements. The exact gate performs the substantive
new terminal and complete-cover checks. `verify_packet.py` by itself is a
byte/header/alias consistency check; it does not repeat arithmetic.

## Separate diagnostic

The initial center-coordinate proposal improved a saved endpoint but did not
improve its unchanged independently propagated current box. The exact scan of
all 63 proposed endpoint improvements likewise found no improvement on the
existing dyadic bound grid among the 36 nonterminal current leaf states. It
also identified these three existing terminal leaves. This negative finding
is preserved under `diagnostic/`; it is not a premise for the three exclusions
and makes no claim about more general combinations of center inequalities.

No active numerical tree, driver, source checker, ledger or mask definition is
changed by this checkpoint.
