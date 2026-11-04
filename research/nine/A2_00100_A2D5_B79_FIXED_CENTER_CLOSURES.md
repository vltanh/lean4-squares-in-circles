# Two complete original cells: A2d5 and B79

November 4, 2026. These complete finite-cover proofs advance the unchanged
231-cell register from **202 CLOSED / 29 OPEN to 204 CLOSED / 27 OPEN**.
The remaining original families are **A4, B12, C8, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal `100/00`,
A.2, the unrestricted lower bound and global equality remain OPEN.

[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Source-bound packets and root fresh replays](computer_assisted/a2_00100_a2d5_b79_complete_covers_manifest.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

## Complete proofs and accounting

| Original cell | Complete final rectangles | Exact terminal types | New bound deductions | Checked local rows |
|---|---:|---|---:|---:|
| `positive-2d5aba857f2f7602` | 65 | 37 interval, 28 affine | 1,372 | 3,271 |
| `negative-79cdbfcbed2f1fac` | 16 | 4 interval/frame, 11 affine, 1 quadratic | 1,776 | 4,896 |
| Total | 81 | All final rectangles excluded | 3,148 | 8,167 |

The [A2d5 hand proof](A2_00100_A2D5_FIXED_CENTER_COVER_CLOSURE.md) uses
nine direct I-center terminals and seven full H2-by-4 subcovers, with
fifteen exact local bound rounds across seven members. Every positive
terminal reserve exceeds 1/1024. The numerical pose-graph experiment
is not a premise of the proof.

The [B79 hand proof](A2_00100_B79_FIXED_CENTER_BOUND_PSD_CLOSURE.md) uses
all sixteen closed I-quarter products without H subdivision. Nine members
have direct affine or interval contradictions. Seven require twelve
local bound rounds: six end in affine or interval/frame contradictions,
and the seventh has a rational quadratic certificate. The final certificate
reconstructs 47 RLT antecedents and 24 explicit negative rational squares.
Its exact paid reserve exceeds 1/2048. All twelve derived product
coordinates in B79's affine ancestors use the original path's actual
C–D and D–G separating axes; the final quadratic variables retain the
same original frames.

The row totals in the table include the local bound-premise rows and
final terminal rows, excluding separately replayed unchanged ancestors.
Only the two entire original cells receive closure credit. The 81 internal
rectangles do not become original cells or positional roots.

## Full physical caller and closed-face coverage

Every member retains nine independent original square frames, all 36
original corners and 36 original pairs, all five marked center-cone
comparisons, actual AB/BC/EF/FG and strictly weak CD, at every q below
1105/256. The accepted low-gap normalization and fixed H/I order remain
unchanged. Each proof checks the original immutable path and the exact
closed partition of a single certified ancestor state. Shared faces,
orientation endpoints and contact remain included.

The complete-cover checkers require every leaf to use the same exact
ancestor prefix hash. They derive every quarter, half and inherited
interval from that freshly replayed state. Both independent assemblies
passed again from relocated source-frozen packets, with external workspace
reads and numerical producer imports rejected.

The strengthened B79 assembly also explicitly compares the prefix hashes
of closed bound leaves, the quadratic prior and its OPEN bound-state prior.
A [separate identity audit](computer_assisted/a2_00100_B_complete_cover_ancestor_identity_audit.json)
confirms that all actual leaves in the preceding B0e4, B6ad, B5d7 and B265
packets already use their respective cover's exact prefix. Their frozen
packets are unchanged. The audit adds no closure credit.

This is independent rational arithmetic plus a complete written physical
argument. No human or proof-kernel verification is claimed. No Lean,
Lake or CI was run. No mask, positional-root or roadmap-gate status changes.

## Portable replay

Run these commands from `research/nine/computer_assisted`, with the ordered
archive parts and manifests present. The full archive hashes are recorded
in the manifest above. Root fresh replay reports are stored separately;
they are generated outputs, while the archived source/certificate inventories
identify the immutable mathematical inputs.

### A2d5

```sh
cat a2_00100_a_2d5_fixed_cover_checkpoint.tar.gz.part01 a2_00100_a_2d5_fixed_cover_checkpoint.tar.gz.part02 > a2_00100_a_2d5_fixed_cover_checkpoint.tar.gz
printf '%s  %s\n' ec274c70c7ad20dad907dbd7b327795f8060a0a3eb877c12acabbee9f02943a8 a2_00100_a_2d5_fixed_cover_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_a_2d5_fixed_cover_checkpoint.tar.gz
cd a_2d5_fixed_cover_package
python -B -S verify_a_fixed_cover.py
```

### B79

```sh
tar -xJf a2_00100_b_79_bound_checkpoint.tar.xz
cd b_79_bound_package
python -B -S verify_all.py
```
