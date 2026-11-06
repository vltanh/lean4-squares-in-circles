# A full nine-square 111/00 witness at Q with every marked inequality strict

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/A2_11100_CLOSED_Q_BOUNDARY_HAND_PROOF.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

November 4, 2026. Exact boundary classification, separate from the frozen
four-mask boundary packet. No Lean, Lake, or CI.

## Statement

The unchanged full-nine predicate (D_{111/00}^{\le}) is nonempty at
(Q=1105/256). Moreover, its displayed witness has **all five cone
comparisons strict, both actual bits strict, and all three weak bits
strict**. No marked equality face is essential. The physical packing
still has allowed contacts and corners on the (Q)-circle.

This is not a strict-subcritical counterexample. It closes zero strict
masks and zero original cells. Together with the separate four-mask
packet, it shows that all four short-bit variants of main `111`, and
also `101/11`, require strict-radius reasoning rather than an assertion
that their complete closed-(Q) predicates are empty.

## 1. All nine original centers and frames

Use physical coordinates (X,Y). The following centers are exact:

| Original | Center | First axis (u_i) | Largest squared corner norm |
|---|---|---|---:|
| 0 | ((-3/2,1/16)) | ((1,0)) | (1105/256) |
| 1 | ((-1/2,1/16)) | ((1,0)) | (337/256) |
| 2 | ((1/2,1/16)) | ((1,0)) | (337/256) |
| 3 | ((3/2,1/16)) | ((1,0)) | (1105/256) |
| 4 | ((-1,-15/16)) | ((1,0)) | (1105/256) |
| 5 | ((0,-15/16)) | ((1,0)) | (593/256) |
| 6 | ((1,-15/16)) | ((1,0)) | (1105/256) |
| 7 | ((-3/5,19/16)) | ((99/101,20/101)) | (2524789/646400) |
| 8 | ((3/5,19/16)) | ((99/101,20/101)) | (2675189/646400) |

In every row the second physical axis is
(v_i=(-u_{i,y},u_{i,x})). The two tilted frames are exactly unit because
(99^2+20^2=101^2). The table's maximum is obtained by evaluating all
four original corners (c_i+(s u_i+t v_i)/2), (s,t\in\{-1,1\}).
Every maximum is at most (Q), and four originals attain (Q).

All 36 original physical pairs have disjoint open interiors:

- The first four aligned squares have horizontal center gaps at least
  one within their row; the next three have the same property.
- The vertical gap between those two rows is one, so their original
  vertical open projections are disjoint.
- Each tilted top square has physical coordinate halfwidth (119/202).
  Its vertical gap from the four-square row is (9/8), whereas the
  corresponding halfwidth sum is (110/101). The reserve is
  (9/8-110/101=29/808>0). The gap from the lower row is even larger.
- The two top squares have horizontal center gap (6/5), exceeding their
  halfwidth sum (119/101) by (11/505>0).

The independent checker additionally verifies one explicitly printed
**owned physical axis** for each of the 36 pairs, using the full original
corner projections. No proxy-only separation is substituted.

## 2. A frame strictly inside the marked angular region

Choose

\[
 e=\frac{(20,7)}{\sqrt{449}},\qquad
 f=\frac{(-7,20)}{\sqrt{449}}.
\]

Both axes have unit norm and zero dot product. The full original-label
permutation is

\[
 (A,B,C,D;E,F,G;H,I)=(4,1,2,3;0,7,8;5,6).
\]

All nine original squares are retained. The main and short chains are
disjoint, and the two extras remain genuine physical originals.

For an aligned original the witness halfwidth is
(27/(2\sqrt{449})). For either tilted original it is

\[
 \frac{|20\cdot99+7\cdot20|+|-20\cdot20+7\cdot99|}
 {202\sqrt{449}}
 =\frac{2413}{202\sqrt{449}}.
\]

All entries of the following table have been multiplied by the same
positive denominator (sqrt{449}). Thus no inequality direction is
changed when comparing them. Write (d=\sqrt{449}\,\Delta x),
(v=\sqrt{449}\,\Delta y), and
(w=\sqrt{449}(h_i+h_j)).

| Edge | Original pair | (d) | (v) | (w) | Cone reserve (d-|v|) | Required bit reserve |
|---|---|---:|---:|---:|---:|---:|
| AB | 4→1 | 17 | (33/2) | 27 | (1/2) | weak: 10 |
| BC | 1→2 | 20 | −7 | 27 | 13 | weak: 7 |
| CD | 2→3 | 20 | −7 | 27 | 13 | weak: 7 |
| EF | 0→7 | (207/8) | (81/5) | (2570/101) | (387/40) | actual: (347/808) |
| FG | 7→8 | 24 | (-42/5) | (2413/101) | (78/5) | actual: (11/101) |

For weak bits the listed reserve is (w-d>0); for actual bits it is
(d-w>0). Consequently the literal mask is exactly `111/00`.

The minimum cone reserve is (1/(2\sqrt{449})>0); the minimum actual-bit
reserve is (11/(101\sqrt{449})>0); and the minimum weak-bit reserve is
(7/\sqrt{449}>0). Therefore none of the five marked cone faces or bit
faces is at equality. By continuity, the same selected labels and exact
five bits persist on a nonempty open interval of nearby witness angles.

The initially discovered event direction was proportional to ((3,1)),
where the first cone is at equality. The present ((20,7)) direction
removes that equality, and the proof uses the strict table above.

## 3. Radius scope and replay

The packing's largest squared corner norm is exactly (Q), not less.
Thus its existence obstructs a whole closed-(Q) contradiction for
`111/00`, while leaving the intended strict-radius exclusion OPEN.
The strictness of the marked inequalities does not remove the circle
equalities or the original physical touching contacts.

From this packet run:

```text
python verify_11100_boundary.py --directory . --negative-controls
```

The standard-library checker reconstructs every original frame, all 36
corners, all 36 owned physical separators, the orthonormal witness frame,
the complete nine-label permutation, all five exact rows, and their
strict margins. It reads no discovery program or solver output. Integer
and `Fraction` arithmetic suffice because the one square-root denominator
is known positive and common to all comparisons.

The manifest binds the checker, literal table, complete rational control,
this hand proof, and the unchanged domain contract; every bound file is
rehashed at completion. Five optional damaged controls check omitted
originals/pairs, an invalid edge order, a corrupted actual reserve, and
the forbidden strict-subcritical claim. Existing four-mask proof sources
are unchanged and are not runtime dependencies of this supplement.
