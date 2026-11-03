# Six complete originals and three existing-domain assemblies

## Result and fixed accounting

This continuation excludes exactly six further original A2/00100 cells.
The preceding two published checkpoints established 185 CLOSED and
46 OPEN cells in the same fixed register of 231 originals. These six
distinct complete proofs give 191 CLOSED and 40 OPEN. The global mask
ledger remains 8 CLOSED and 24 OPEN; no new whole-mask conclusion follows.

| Original ID | Proof | Earlier deductions | New deductions | Printed rows | Terminal domains |
| --- | --- | ---: | ---: | ---: | ---: |
| `positive-d9e959003493b8f1` | Complete fixed I-center grid | 31 | 457 | 1,339 | 64 |
| `positive-8e41311b61c89e61` | Complete fixed I-center grid | 33 | 653 | 1,355 | 64 |
| `positive-5edcabd77ec2e38b` | Complete fixed I-center grid | 32 | 411 | 1,204 | 64 |
| `positive-b4a9a3bc15e37620` | Whole-parent exact contradiction | 36 | 691 | 1,037 | 1 |
| `negative-daf08b7f35b70b9a` | Complete H-center grid and rectangle | 30 | 750 | 1,524 | 63 |
| `negative-99f578b7bbedf013` | Complete H-center grid and rectangle | 38 | 766 | 1,544 | 59 |
| **Total** | **Six complete original cells** | **200** | **3,728** | **8,003** | **315** |

The new deductions comprise 2,906 whole-parent implications and 822
implications on the two complete H rectangles. The finite tables cover
all 320 closed grid tiles. Their 312 static terminal domains, two
complete rectangles, and one whole-parent terminal are internal proof
domains, not new original IDs or mandatory child gates.

## 1. Physical hand/table proofs

Every proof keeps its literal original path, the same nine physical
unit-square frames, all 36 corner conditions, all 36 physical pair
constraints, marked cones, the exact strict CD bit, and the strict-radius
caller. Proved relational bounds remain attached to those same originals.

- [The three A fixed grids](A2_00100_THREE_A_FIXED_GRID_INTERVAL_CLOSURE.md)
  give exact exclusions of all 192 I-center tiles. Previously unresolved
  diagnostic exceptions are replaced by explicit rational contradictions
  between inherited pair differences and physical propagation on the
  whole tile. Those exceptions themselves provide no proof.
- [The high-F A original](A2_00100_A_HIGH_F_WHOLE_PARENT_CLOSURE.md)
  closes its entire unchanged parent after four implication rounds. Its
  sixteen-row terminal includes a guarded D/I/H altitude row and the
  physical E-frame chord, with a fully paid positive rational reserve.
- [The two H-center covers](A2_00100_H_FIXED_CENTER_COVER_CLOSURE.md)
  exclude 120 outside static tiles and two complete remainder rectangles.
  The center-cover argument is valid for any selected original. Here
  the target is the actual H, at indices 14 and 15; the I proofs use
  indices 16 and 17. No H/I exchange occurs, and `x_H <= x_I` is retained.

Every bound is an exact consequence of the preceding proved state.
All original-parent inductions, physical row guards, residual payments,
frame refinements, grid faces, and final contradictions are independently
replayed. Numeric optimization supplies proposed tables only.

## 2. Completed existing prefixes

The scope maps below use the accepted certified baseline tree and its
original coverage contract. That baseline already excluded terminal
descendants outside the fixed 231-cell register; those exclusions remain
part of every prefix assembly. The machine-readable maps enumerate the
remaining fixed original descendants inside that register. Closing all
of those registered descendants, together with the inherited exclusions
outside the register, closes the specified existing domain.

The [exact entailment maps](computer_assisted/a2_00100_shared_center_remainder_scope_entailment_maps.json)
list every registered original ID and its source of closure. The portable
checker reconstructs those maps from the immutable register, the two
preceding checkpoint manifests, and the six newly replayed proofs.

### 2.1 A inward-row child 7

The exact existing prefix is

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[7])
```

It has 16 remaining fixed-register descendants. Fifteen were already
CLOSED in the immutable 174/57 input register; b4 was the only OPEN
registered descendant. Its complete proof finishes this existing
inward-row child, with the baseline's already excluded descendants also
retained.

### 2.2 A inward-row child 6, low F, F-H child 6

The exact existing prefix is

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[6])
position_cut(11,1/2,0)
f_side_escape(5,7,[6])
```

It has 33 remaining fixed-register descendants. Twenty-nine were already
CLOSED in the immutable input register. The first checkpoint proved
`positive-3da90694b58b6ef7` and `positive-8f760b2d708ad21d`; this packet
proves `positive-8e41311b61c89e61` and `positive-d9e959003493b8f1`.
Those four complete proofs finish the registered remainder of this
existing prefix, while preserving the inherited excluded terminal
branches outside the register.

The broader prefix obtained by removing the final F-H routing step is
still OPEN: `positive-768264ad71bc8152` remains an OPEN registered
original there. The low-F inward-child-6 domain is therefore not claimed
closed.

### 2.3 F-H routing child 5 across every F height

Under the common prefix

```text
angle(3,0)
angle_cut(0,0,0)
```

the two exact original paths append the closed F-height children
`y_F <= 1/2` and `y_F >= 1/2`, respectively, followed by the same routing
step `f_side_escape(5,7,[5])`. Daf and 99f are exactly those two original
cells. Their complete proofs cover every F height, including the shared
face, and establish the whole existing child-5 routing under this prefix.
The original H/I order is not changed. This does not close the other
F-H routing children or the whole family B.

## 3. Frozen replay package

The deliverables are

- `computer_assisted/a2_00100_shared_center_remainder_checkpoint.tar.gz`;
- `computer_assisted/a2_00100_shared_center_remainder_manifest.json`;
- the exact scope-map JSON linked above.

After extraction, run

```bash
python shared_center_remainder_checkpoint/verify_all.py
```

Only the Python standard library is required. The archive contains the
unchanged accepted original geometry, independent physical-row checker,
separate I-static and H-cover verifiers, complete bound and terminal
tables, all required coordinate prefixes, and exact source bindings.
The corrected `daf_nineteen_row_exact_terminal_v2.json` is also checked:
all nineteen positive rational weights cancel twenty-one coefficients
exactly and leave reserve greater than 29/50.

Both earlier archive/manifest pairs are preserved byte-for-byte. Their
manifests identify the eleven prior closures, and the new six IDs are
checked to be distinct from them. Replay output is kept separate from
immutable accepted evidence. The final SHA-256 manifest binds every
immutable delivered file.

No Lean, Lake, CI, proof-kernel verification, global equality
classification, or unrestricted theorem is claimed. Mask 001/00, its
reversal 100/00, and the remaining all-mask obligations stay open.
