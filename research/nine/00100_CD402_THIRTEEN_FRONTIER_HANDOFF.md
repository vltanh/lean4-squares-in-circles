# Cd402 handoff: 13 unresolved physical domains, classified by H/I

**Status: OPEN. No whole original-cell closure is claimed or credited.**
This is a handoff of the existing, verified finite frontier for the exact
original cell `negative-d4021ade840b985c` of mask `001/00`.
It adds no new numerical proof, no new registered original, and no new gate.
The frozen original accounting remains **224/231 CLOSED, 7 OPEN**; full
masks remain **8/32 CLOSED**.

## Exact fixed caller

The source is the original-nine `D_001/00^lt` predicate from
[A.2's coverage contract](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/A2_COVERAGE_AND_CLOSURE_CONTRACT.md).
Retain all nine independently oriented original unit squares A–I, all
36 original pairwise interior-disjointness conditions, all 36 corner
containment inequalities at squared radius `q<Q=1105/256`,
the five selected center cones, actual AB/BC/EF/FG projection
comparisons, strictly weak CD, and both unrestricted extras H and I.

The immutable Cd402 original path is

```text
["angle",3,0]
["angle_cut",[0,"0"],1]
["alternate_four_escape",[1,7],[2]]
```

with the accepted normalization `y_D-y_C>2/3`,
`x_H<=x_I`, D's nonpositive canonical tilt, and A's nonnegative
canonical tilt. The literal escape rows were decoded and reviewed in
[Cd402's original-model proof](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/a2_00100_cd402_fresh_original_checkpoint_v1/CD402_FRESH_ORIGINAL_MODEL_HAND_PROOF.md).
No convenient orientation, equality face, endpoint order or new mask
bit is imposed.

## The saved frontier

The archived [C-family exact checkpoint](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/A2_00100_C_FINITE_FRONTIERS_CHECKPOINT.md)
reports a freshly exact-replayed **507-node** Cd402 continuation with
**351 excluded terminal leaves and 13 explicitly OPEN leaves**. The
associated 507-node manifest is in the archived
`research/nine/computer_assisted/a2_00100_c_finite_frontiers_v2/covers/cd402_opposite_507/MANIFEST.json`.
The remaining node indices, which are **internal nodes of this one original
cell** and *not* 13 new original-cell IDs, are

```text
42, 44, 45, 47, 48, 51, 468, 480, 495, 498, 499, 502, 506
```

An independent complete cover and exact arithmetic replay of all
substitutions is still required for any new closure claim. Later
[Cd402 eight-terminal substitutions](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/a2_00100_cd402_eight_terminal_delta_v1/HAND_TABLE.md)
refer to an earlier 25-pending manifest, remove eight such pending
entries, and retain 17 pending there. Those counts must **not** be
subtracted from these 13 stopped leaves: the two frontiers are not
identical disjoint sets.

## Physical compression of the 13 domains

Let `g_S=1/(4h_S)` be the halfwidth of the original square S's
contained centered aligned inset. A saved `proxy(i,j,[1,1])` means
`y_j-y_i >= g_i+g_j`; `proxy(i,j,[1,-1])` means
`y_i-y_j >= g_i+g_j`; and `proxy(i,j,[0,1])` means
`x_j-x_i >= g_i+g_j`. These are retained original-pair *necessary*
physical alternatives, not actual projection separation for arbitrary
pairs of squares.

**Every one of the 13 stopped paths** starts (after the three immutable
parent choices) with

```text
["proxy",[1,7],[1,1]]
```

and hence satisfies the same physical necessary inequality

\[
                 y_H-y_B\ge g_B+g_H.               \tag{1}
\]

The only next H/I physical-inset alternative, for each recorded open
path, is exactly one of these three:

| H/I relation | Stopped node IDs | Count |
|---|---|---:|
| `x_I-x_H >= g_H+g_I` | 42, 44, 495, 498, 499, 502, 506 | 7 |
| `y_H-y_I >= g_H+g_I` | 45, 47, 48 | 3 |
| `y_I-y_H >= g_H+g_I` | 51, 468, 480 | 3 |
| **Total** | All thirteen IDs above | **13** |

The fourth H/I alternative, `x_H-x_I >= g_H+g_I`, is
incompatible with the retained `x_H<=x_I`; its historical branch
was also excluded.

The remaining path distinctions concern physical F/I or F/H inset
separations, a zero-angle cut for H, an E/H inset choice, an owned
D/G separator, and closed height-difference cuts. **None has been
dropped.** The three displayed rows organize the union of the saved
unproved leaves; they are not a replacement domain defined by
inequality (1) and the three H/I cases alone.

## Stopping rule and next exact proof obligation

To close the frozen **Cd402 original**, a single manuscript/table must
discharge every one of these thirteen saved complete path predicates
(or prove a valid uniform terminal covering them), retain all previously
verified closed siblings, and give a complete induction over the unchanged
original-cell parent. A common physical obstruction involving the two
extras H,I and the true F/G and C/D constraints is preferred over
further open-ended angle refinement. If a table is used, all rational
weights, necessary physical rows, strictness and the closed child unions
must be printed or attached with independent exact arithmetic checking.

The selected-seven relaxation alone cannot suffice: the archived
[selected-seven obstruction](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md)
exhibits strictly subcritical configurations for this mask.
No feasible numerical relaxation should be represented as a genuine
original-nine packing or as an equality family. The strictly weak CD
inequality and the sharp-radius boundary must be retained; a positive
closed-Q margin is not assumed.

## Related recent hand results

The current branch already contains
[the endpoint-height/Cb882 hand bounds](00100_SHARP_A_HEIGHT_AND_CB882_DEEP_B.md)
and [C887's conditional transfer](00100_C_BOUNDARY_DOMINANCE.md).
Those results are **not** an exclusion of Cd402. If Cd402 is eventually
proved empty, the C887 transfer can then be applied, but neither original
is to be marked CLOSED before the complete proof is checked.

**No Lean compilation, Lake, CI, new numerical search or certificate
replay was run for this handoff.** The 507-node facts are read from
the archived checkpoint and its source manifest. This text is a
scope-preserving consolidation, not an independent review of all prior
arithmetic.
