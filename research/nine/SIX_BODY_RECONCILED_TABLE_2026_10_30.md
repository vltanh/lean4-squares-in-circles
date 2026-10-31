# Six-body exterior table: exact original-status reconciliation

Date: 2026-10-30. Input commit: `71d385e75adc1f5183d35a92dbe18c208dc32f2a`.
Original roadmap blob: `77cf80fd377d7f6a400a15a00fe22e9b66d4b355`.

## Result

The 38 exterior-hexagon representatives split into **18 original checked rows and 20 original open rows**. The previous 25 `UNRECONCILED` labels split into **7 already checked and 18 already open**. The two previously identified open D02 rows are only two of the twenty.

This is a literal reconciliation with the unchanged original `DEEP_GATED_ROADMAP.md`, not new mathematical closure and not a fresh review of an earlier proof. No original fine/coarse identifier or checkbox changes. In particular the canonical totals remain **2373/2513 fine checked and 37/58 coarse closed**. The original six-body parent `C1.6.b0` stays open.

The script `../../scripts/n9_six_body_table.py` now records each exact original ID and its pinned status. Run:

```sh
python scripts/n9_six_body_table.py --check-roadmap research/nine/DEEP_GATED_ROADMAP.md
python scripts/n9_six_body_table.py --json
```

The first command reconstructs all graph/load orbits and checks every one of the 38 literal status flags against the original roadmap. The JSON includes the input commit/blob, original gate IDs, masks, face screens and original checked flags. A status mismatch fails explicitly instead of silently changing a flag.

## Exact original rows

`CHECKED` below means precisely that the original source checkbox is checked. It is not a claim of Lean verification. All inherited radius/frame/owner/mean/circle-mask/force/torque/three-extra obligations remain part of each original row.

| Chords | Loads | Exact original gate | Original flag |
| --- | --- | --- | --- |
| `none` | `024` | `M6.B6.C6.THREE_ALTERNATING` | CHECKED |
| `none` | `0124` | `M6.B6.C6.FOUR_ZERO_DISTANCE2` | CHECKED |
| `none` | `0134` | `M6.B6.C6.FOUR_ZERO_DISTANCE3` | CHECKED |
| `none` | `01234` | `M6.B6.C6.FIVE` | CHECKED |
| `02` | `014` | `M6.B6.HEXAGON.D02.L014` | CHECKED |
| `02` | `134` | `M6.B6.HEXAGON.D02.L134` | CHECKED |
| `02` | `135` | `M6.B6.HEXAGON.D02.L135` | OPEN |
| `02` | `0134` | `M6.B6.HEXAGON.D02.L0134` | CHECKED |
| `02` | `0135` | `M6.B6.HEXAGON.D02.L0135` | CHECKED |
| `02` | `0145` | `M6.B6.HEXAGON.D02.L0145` | CHECKED |
| `02` | `1345` | `M6.B6.HEXAGON.D02.L1345` | OPEN |
| `02` | `01345` | `M6.B6.HEXAGON.D02.L01345` | CHECKED |
| `03` | `014` | `M6.B6.HEXAGON.D03.L014` | OPEN |
| `03` | `024` | `M6.B6.HEXAGON.D03.L024` | OPEN |
| `03` | `124` | `M6.B6.HEXAGON.D03.L124` | OPEN |
| `03` | `0124` | `M6.B6.HEXAGON.D03.L0124` | OPEN |
| `03` | `0125` | `M6.B6.HEXAGON.D03.L0125` | OPEN |
| `03` | `0134` | `M6.B6.HEXAGON.D03.L0134` | CHECKED |
| `03` | `1245` | `M6.B6.HEXAGON.D03.L1245` | OPEN |
| `03` | `01245` | `M6.B6.HEXAGON.D03.L01245` | CHECKED |
| `02+03` | `124` | `M6.B6.HEXAGON.D0203.L124` | OPEN |
| `02+03` | `125` | `M6.B6.HEXAGON.D0203.L125` | CHECKED |
| `02+03` | `1234` | `M6.B6.HEXAGON.D0203.L1234` | OPEN |
| `02+03` | `1235` | `M6.B6.HEXAGON.D0203.L1235` | OPEN |
| `02+03` | `1245` | `M6.B6.HEXAGON.D0203.L1245` | OPEN |
| `02+03` | `12345` | `M6.B6.HEXAGON.D0203.L12345` | CHECKED |
| `02+04` | `125` | `M6.B6.HEXAGON.D0204.L125` | CHECKED |
| `02+04` | `135` | `M6.B6.HEXAGON.D0204.L135` | OPEN |
| `02+04` | `0135` | `M6.B6.HEXAGON.D0204.L0135` | OPEN |
| `02+04` | `1235` | `M6.B6.HEXAGON.D0204.L1235` | OPEN |
| `02+04` | `1245` | `M6.B6.HEXAGON.D0204.L1245` | OPEN |
| `02+04` | `12345` | `M6.B6.HEXAGON.D0204.L12345` | CHECKED |
| `02+35` | `0134` | `M6.B6.HEXAGON.D0235.L0134` | OPEN |
| `02+35` | `0145` | `M6.B6.HEXAGON.D0235.L0145` | CHECKED |
| `02+03+04` | `12345` | `M6.B6.HEXAGON.FAN.L12345` | CHECKED |
| `02+03+35` | `1245` | `M6.B6.HEXAGON.CHORD_PATH.L1245` | OPEN |
| `02+04+24` | `135` | `M6.B6.HEXAGON.CENTRAL_TRIANGLE.L135` | OPEN |
| `02+04+24` | `0135` | `M6.B6.HEXAGON.CENTRAL_TRIANGLE.L0135` | OPEN |

## Consequences for the next proof attempt

All four surviving bare-C6 rows in this table were already checked, as was the entire fan graph. The additional checked rows missing from the former conservative allowlist are:

- Bare C6 with loads `024`, `0124`, `0134`.
- `03/0134`.
- `02+03/125` and `02+04/125`.
- `02+35/0145`.

Thus `03/0134` should not be presented as a new no-hole completion target. The other three rows singled out by the primitive triangle/three-boundary-four-ring screens remain open: `02+03+35/1245`, `02+04+24/135` and `02+04+24/0135`.

Six further original open rows already have **all bounded faces empty** by the established opposite-boundary four-ring theorem, a stronger input than the primitive screen implemented in the script:

| Graph | Loads | Original retained consequence |
| --- | --- | --- |
| `03` | `024`, `0124` | All three actual extras are exterior. |
| `02+03` | `1235` | All three actual extras are exterior. |
| `02+04` | `0135`, `1245` | All three actual extras are exterior. |
| `02+35` | `0134` | All three actual extras are exterior. |

Consequently there are **nine explicitly identified open original rows** sharing the all-extras-exterior completion frontier. A joint exterior-capacity theorem, at the full chorded-graph scope and with every actual force/mean retained, could cover several of them at once. This is an application target; empty bounded faces alone do not exclude the three exterior extras.

## Compact Lean drafts prepared in parallel

`LeanDrafts/GraphCover.lean` contains a compact finite Boolean formulation of the nine graph/load covers, all twelve dihedral actions, full graph stabilizers, and the 40-to-38 table count. Each proposed coverage theorem is an ordinary `by decide` proof over 64 load masks. The necessary predicate uses a simple relaxation of the original loaded path-forest and connected-complement conditions, avoiding a large generated proof expansion. Its physical caller and the separate nine-graph planar classification remain obligations.

`LeanDrafts/CenterCapacity.lean` contains proposed ordinary proof terms for:

1. A finite cover by k sets of squared diameter below one contains at most k pairwise unit-separated centers; overlap and nonconvexity are allowed.
2. The squared-diagonal bound for two points in one rational rectangle.
3. Exact robust perturbation identities for reference-center and convex-combination witness certificates.
4. The concrete east/south cover from the five-core Type II certificate: split the south rectangle at x=-3/8 to obtain three rectangles with squared diagonals 3085/3600 and 14089/14400, all strictly below one.

**Both Lean files are uncompiled drafts.** The available editing environment has no Lean/Lake executable; no build, axiom output, Comparator or independent-kernel result is claimed. They contain no `sorry`, custom axiom or `native_decide`. They do not change any original mathematical gate and are not substitutes for the missing global D02 root cover.
