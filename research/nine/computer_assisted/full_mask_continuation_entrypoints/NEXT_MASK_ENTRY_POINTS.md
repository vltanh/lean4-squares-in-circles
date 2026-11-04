# Full-mask continuation entry points and exact boundary diagnostics

This is a recovery and routing index for PR #11. It adds no cell or mask
closure. The current `001/00` original-cell proof retains its existing
premises; none of the transfers below is installed into that proof by this
note. The recovered files are byte-verified against immutable Git head
`8ac1db9d311ab0319105cd35ce46d2b002216330`, using each Git blob SHA from the
published tree. `SOURCE_BINDINGS.json` gives portable relative-file hashes,
original repository paths, and the two fresh exact boundary replay reports.

## 1. Direct all-nine discovery entry point

`emit_fixed_mask.py` is the small, generic physical QF_NRA emitter. For
example, from this directory:

```bash
python emit_fixed_mask.py --mask 011/00 --radius strict --n 9 --output full_01100_strict.smt2
```

Its API is `emit(mask, radius, n)`, with every mask `abc/de`, radius
`strict` or `closed`, and `n=9` for the proof target. It retains nine
independent canonical unit frames, all 36 original corners, all 36 original
physical pair separating-axis disjunctions, all five directed center-cone
links, and the exact five mask bits. Bit 0 means an actual horizontal gap
at least the support sum; bit 1 means a strictly smaller gap. The strict
corner target is exactly squared radius less than `1105/256`.

The emitter does not call a solver. `z3_ctypes.py` supplies the existing
`run(smt_text)` discovery adapter for an installed Z3 shared library. A
bounded call can prepend `(set-option :timeout 20000)` and append
`(get-info :reason-unknown)` to the emitted text. Such a solver result is
discovery data and does not supply an independently checked exclusion.

**Do not treat `run_full_mask.py` as a generic batch driver.** It hardcodes
`000/01`, strict radius, nine squares, and a 20-second limit, and writes to
fixed filenames next to itself. Its recovered output is `unknown` with
reason `timeout`, not a proof. The recorded Z3 control report has five
expected SAT/UNSAT controls and zero global mask closures.

`test_emit_fixed_mask.py` independently evaluates the emitted expressions
on exact rational controls. `test_z3_fixed_mask_controls.py` runs only the
five pinned solver controls. Neither test is an all-mask proof.

The separately recovered `FULL_PHYSICAL_TRIANGLE_SYSTEM_2026_11_01.md`
describes a force/torque system for an unloaded contact triangle. Its five
exit-identity roots are a different downstream theorem target. That
document is not a replacement mask model and reports no mask exclusion.

## 2. Exact full-nine equality obstructions that must remain

Fresh integer/Fraction replays of both recovered boundary packets pass,
including all 36 physical corners, all 36 owned physical pair separators,
complete nine-label permutations, exact mask rows, and five damaged-input
controls per packet. Their report files are
`FRESH_FOUR_BOUNDARY_REPLAY.json` and `FRESH_11100_BOUNDARY_REPLAY.json`.

| Full mask | Exact closed-radius provenance | Marked-inequality details |
|---|---|---|
| `101/11` | `four_full_nine_mask_closed_q_boundary_witnesses.tar.xz` | Strict weak bits; one displayed cone equality. The actual BC reserve is strictly positive. |
| `111/01` | Same four-mask packet | Strict weak bits; actual EF and two cones can be equalities. |
| `111/10` | Same four-mask packet | Reversed mixed-short witness, retaining strict weak bits and allowed actual/cone equality faces. |
| `111/11` | Same four-mask packet | All five designated weak bits are strict; some cones are equalities. |
| `111/00` | `mask_11100_full_nine_closed_q_boundary.tar.xz` | **All five cones, both actual bits, and all three weak bits are strict.** |

Every row is a genuine nine-square configuration at exactly
`Q=1105/256`. None is a packing below Q. They therefore obstruct a proof
that the corresponding entire closed-Q predicate is empty, while leaving
the requested strict-radius exclusions open. In particular, requiring
strict marked cones and strict bit margins does not remove the `111/00`
boundary packing. The remaining equalities are circle containment and
permitted physical contacts.

The four-mask archive has SHA-256
`5050e8116c072bc5de59137fb06bda73bb1f726153a04de15240f6741a86598c`.
Its direct checker is
`four_full_nine_mask_closed_q_boundary_witnesses/four_mask_closed_q_boundary/verify_closed_q_boundary_witnesses.py`.
The `111/00` archive has SHA-256
`4a528e37e978b6dae7d5d5b4c784fab14719d03c5861a8ff82a582a05046d7fa`.
Its checker is
`mask_11100_full_nine_closed_q_boundary/mask_11100_closed_q_boundary/verify_11100_boundary.py`.
Each publication manifest binds every extracted member, including the
hand/table derivation and original physical-domain contract. Both fresh
replays checked those source bindings again.

For these five masks, the next proof architecture must explicitly handle
the strict-radius target, an adequate sharp equality theorem, or a proved
global routing theorem. A positive-reserve contradiction for the whole
closed-Q predicate cannot succeed. No strict terminal or new routing
theorem is claimed here.

## 3. Seven originals alone do not exclude any remaining mask

`seven_original_all_open_masks_table.json` and
`verify_seven_original_table.py` give 14 rational representative packings
of **seven** originals, covering all 24 presently unresolved masks under
chain reversal. Their squared containing radius is less than `17/4`,
with `Q-17/4=17/256`. All selected physical pairs, cones, and mask-bit
margins are strict. The published exact checker records 882 rational
assertions. The accompanying hand note is
`SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md`.

These controls show why an unconditional exclusion based only on A–G
cannot close the remaining full predicates. They are not nine-square
counterexamples. H and I must remain in the full-mask search, and a proof
that discards their constraints needs a separate justified geometric
reduction.

## 4. Exact work sharing and useful accepted local reductions

Simultaneously reverse both selected chains and negate both witness-frame
vectors. This preserves the complete physical caller and maps
`abc/de` to `cba/ed`. Thus the 24 masks form the following 14 reversal
classes; these are work-sharing classes, not new proof credit.

| Representative | Partner |
|---|---|
| `001/00` | `100/00` |
| `001/01` | `100/10` |
| `001/10` | `100/01` |
| `001/11` | `100/11` |
| `011/00` | `110/00` |
| `011/01` | `110/10` |
| `011/10` | `110/01` |
| `011/11` | `110/11` |
| `101/00` | itself |
| `101/01` | `101/10` |
| `101/11` | itself |
| `111/00` | itself |
| `111/01` | `111/10` |
| `111/11` | itself |

The published package
`research/nine/computer_assisted/original_row_mask_transfer` is the
source-bound entry point for the original ABCD specialization of the
accepted opposite-endpoint theorem. For a short-`00` caller, opposite
endpoint signs and total ABCD height variation at most `23/100` give a
sharp row terminal. Its full complement retains eight signed-height
halfspaces and two same-sign angle conjunctions. The local pointer note
`../ORIGINAL_FOUR_ROW_MASK_TRANSFER_AND_CLOSED_ESCAPE_COVER.md` explains
the label map and the separate original-weak-bit equality blocker.

For `001/00` and `011/00`, the accepted near-horizontal replacement-row
theorem additionally applies to each original extra X in `{H,I}` under
its own order and `1/8` adjacent-height guards. The `011/00` optional
four-main-height by six-H-escape by six-I-escape cover contains 144
domains; it does not exclude those domains. Reversal gives the
corresponding outer-weak `100/00` and `110/00` versions.

Neither transfer supplies an actual EF/FG chain when a short bit is one.
Also `001/00` does not imply `011/00`: their exact BC predicates differ.
For other short-bit callers, an actual-three-chain extraction or a new
proof is still needed before using any theorem that requires that chain.

## 5. Where to start after the current original-cell closure

1. Keep the fixed full-nine mask predicate emitted above as the caller.
   Use reversal once, with the entire frame and all labels explicitly
   transferred, to avoid duplicate work.
2. `011/00` has the closest available accepted row reductions. Its full
   untouched physical model is available immediately through the emitter;
   its optional escape covers still need certificates on every member.
3. Reuse the universal original-corner, unit-frame four-product corner,
   owned-pair Gram, and owner-free support inequalities in a new exact
   caller adapter where their source premises hold. The existing D821
   adapter is specific to its original `001/00` path and cannot be used
   unchanged as an all-mask ancestry proof.
4. Preserve the five exact boundary masks above as mandatory feasibility
   controls for any proposed global closed relaxation. Keep selected-seven
   controls separate from full-nine tests.

No new full-mask numerical solve was run during this recovery. The work
here makes the existing entry points, exact obstructions, and accepted
transfer boundaries concrete; it does not widen the current proof domain.
