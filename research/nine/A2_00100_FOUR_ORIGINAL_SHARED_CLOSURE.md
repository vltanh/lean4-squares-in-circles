# Four complete originals finish two existing 001/00 branches

November 3, 2026. **197 of the same 231 original cells are CLOSED; 34 remain OPEN.**
This continuation starts at commit `198c3d19d04f34697e6034f112fa8e3100a4204e`
(193 CLOSED / 38 OPEN) and closes exactly four previously OPEN originals.
It completes two existing prefixes without introducing any new subdivisions.
The full-mask ledger remains **8 CLOSED / 24 OPEN**. Neither `001/00` nor
its reversal `100/00` is proved by this continuation.

## Exact original caller and coverage

Every result retains the complete original-nine predicate in Sections 2–3
of [the coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md): all nine
independent unit frames, 36 original corners, 36 physical pairs, the five
marked center-cone comparisons, actual AB/BC/EF/FG, strictly weak CD, and
every `q<Q=1105/256`. The accepted low-gap exclusion and the certified
large-gap cover are unchanged. Every immutable ID retains its exact path.
No extra frame, ordering, height or separation hypothesis is assumed.

## The four complete proofs

| Unchanged original ID | Complete argument | Prior deductions | New deductions | Printed rows | New splits |
|---|---|---:|---:|---:|---:|
| `positive-2dcf3464c0e0dafb` | Shared 22-row whole-parent terminal | 46 | 1,047 | 1,612 | 0 |
| `positive-3bf14a18887cabaf` | Same shared 22-row terminal | 35 | 1,062 | 1,727 | 0 |
| `negative-e9388ab13ca6220a` | 37-row whole-parent terminal | 36 | 1,224 | 2,855 | 0 |
| `negative-2ee3f4820947eb83` | Original G unit-frame contradiction | 34 | 1,371 | 2,946 | 0 |
| **Total** | **Four complete terminal domains** | **151** | **4,704** | **9,140** | **0** |

### A: the entire existing inward-row child-8 prefix

The [two-A hand/table proof](A2_00100_A_INWARD_CHILD8_SHARED_CLOSURE.md)
derives one common 22-row cancellation with weights having denominator
65536. Each fully paid exact reserve exceeds `1/200`. The physical
argument combines the A/H/I altitude and endpoint-distance constraint
with original I/G support, point-incircle and G-frame rows. Both complete
originals are proved by six whole-parent bound rounds; no descendant is
left open. The exact prefix map contains 26 original register cells:
24 were already CLOSED, and these two are the remaining originals.
Its previously proved baseline terminal descendants remain part of the
exhaustive cover. Thus the complete existing prefix is now excluded.

### B: the entire existing vertical-extra-pair prefix

The [two-B hand/table proof](A2_00100_B_VERTICAL_EXTRA_PAIR_CLOSURE.md)
finishes the existing sixteen-condition prefix ending in the vertical
H/I inset alternative. Its seven original register cells had five
complete proofs already; these two finish the entire prefix.

The first terminal has 37 rows and fully paid reserve greater than
`2/125`. For the second original, ten bound rounds imply

```
alpha_G <= 489247/524288,
|beta_G| <= 92115/262144.
```

The same original unit frame must satisfy `alpha_G^2+|beta_G|^2=1`, but

```
alpha_G^2+|beta_G|^2
 <= 273303319909/274877906944
 = 1 - 1574587035/274877906944
 < 1 - 1/200.
```

This is a direct contradiction. The final producer record contains no
post-contradiction angle state. The independent terminal adapter preserves
that raw certificate, replays the preceding nine complete rounds, checks
all 233 final-round deductions and then applies the exact unit identity.
No fabricated after-state or numerical infeasibility assertion is used.

## Independent replay and immutable evidence

The [aggregate manifest](computer_assisted/a2_00100_four_original_shared_manifest.json)
binds both original archives, hand proofs, certificate inventories and
fresh root replay reports. Each archive was extracted into a separate
fresh directory and its complete `verify_all.py` run with standard-library
Python (`python -B -S`). Both finished with
`PASS_ALL_COMPLETE_ORIGINAL_PARENTS`. Reconstructed physical rows, original
paths, acyclic bound inductions, rational sums, unit-frame guards and
complete existing-prefix maps all passed.

- [A packet manifest](computer_assisted/a2_00100_inward_child8_manifest.json)
  and [fresh root report](computer_assisted/a2_00100_inward_child8_root_replay.json).
- [B packet manifest](computer_assisted/a2_00100_b_vertical_pair_manifest.json)
  and [fresh root report](computer_assisted/a2_00100_b_vertical_pair_root_replay.json).

The immutable packet manifests were written before the additional root
runs and retain their original `root_additional_replay: PENDING` fields.
The aggregate manifest and linked fresh reports record their completion;
neither frozen packet has been rewritten. This distinguishes source
identity, independently reconstructed arithmetic and the written argument.
No human or proof-kernel audit is claimed. No Lean, Lake or CI was run.

## Remaining obligations

The same register now has A5, B17, C8 and D4 OPEN. These are full original
predicates; necessary inequalities and partial internal alternatives do
not discharge them. The remaining 24 whole masks, 2,077 historical open
positional roots, all 15 roadmap IDs, unrestricted lower bound, global
equality classification and final manuscript retain their prior statuses.
The exact global counts and accepted evidence are in the
[current handoff](HANDOFF_A2_FIXED_CLOSURE.md) and
[unchanged-ID register](gates/A2_00100_FIXED_FRONTIER.json).
