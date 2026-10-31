# Independent review of the centered-block marker exclusion

**Result: PASS for the stated conditional theorem.** The eight finite
branches exhaust every unit-square separator from the block and every
failure of the associated marker to belong to the square's open interior.
An independently implemented rational interval replay verified all 1,445
leaves. This is a hand-proof and exact-arithmetic audit, not Lean kernel
verification or an unrestricted four-core exclusion.

## Mathematical checks

- The square/block separating-axis theorem gives precisely the two normal
  ownership types used. Dihedral symmetries of the block map an own-square
  separator to the first octant. For a block separator, they first map the
  signed normal to `ex`; square-frame quarter turns and reflection in the
  `x` axis then give `0<=theta<=pi/4` while preserving that normal.
  Reflecting or relabeling a square frame leaves its physical square intact.
  Every transformation preserves the four-marker set.
- In the own-axis branch, the block support is `c+s`, the unit-square
  support is `1/2`, and the center projection is `a`. In the block-axis
  branch these quantities are respectively `1`, `(c+s)/2`, and `ca-sb`.
  Both separator formulas are correct.
- The marker `(3/2,0)` has frame coordinates `(3c/2,-3s/2)`, so the four
  weak signed displacement inequalities include marker boundary points.
  Excluding them proves membership in the **open** square.
- The maximum corner norm squared is exactly
  `a^2+b^2+|a|+|b|+1/2`. Its lower bound `r^2+r+1/2` justifies the initial
  center box. The rational half-angle chart includes every frame endpoint.
  On the full initial interval `[0,5/12]`, cosine decreases and sine
  increases, so the frame intervals remain valid even in boxes straddling
  the admissible chart boundary.
- The union of the four block squares is the whole closed block. Any open
  intersection of another square with the block's open interior contains
  a point off the two internal grid lines, so the block-level separator
  follows from physical pairwise interior disjointness.
- A shared marker would be a shared interior point, so four markers allow
  at most four completion squares. The translated-radius calculation is
  correct: `U+9/100+1/2500=49917/10000<4999/1000`, using `sqrt(U)<9/4`.
  Thus block-center displacement at most `1/50` is covered exactly as stated.

## Independent certificate replay

`replay_block_marker_cover.py` does not import the generator. It implements
its own `Fraction` interval operations, reconstructs every closed midpoint
split from the root box, validates the serialized schema and exact branch
set, and checks each claimed leaf reason independently. It rejects missing
or duplicate branches and inconsistent statistics. It uses explicit runtime
checks rather than Python assertions for certificate acceptance.

Command:

```text
python replay_block_marker_cover.py
```

Verified totals: **2,882 nodes; 1,445 leaves; maximum depth 43**. Leaf
reasons were 707 separator contradictions, 433 corner-radius contradictions,
and 305 marker-displacement contradictions. The reported per-branch counts
match the manuscript and serialized certificate. No frame-chart rejection
was needed in this particular tree.

## Reviewed SHA-256 digests

| Artifact | SHA-256 |
| --- | --- |
| `CENTERED_BLOCK_OBSTRUCTION.md` | `f1b2a6f511e40aee4a34c3b53a0206dfbbfb9facaf26dee955f85bfaa480e1a8` |
| `block_marker_certificate.py` | `c1c0c896874042aca58105f0428a177f30347cea5317f07871ff6d327a361b3a` |
| `BLOCK_MARKER_COVER.json` | `487537d7cc84ad3cbccedd69cc504ff97641051c337c3eb093e7ca41d41088fc` |
| `replay_block_marker_cover.py` | `fac63d15189b08b11e0e50786c475d145f5ab80ea4c3e0f55705da532407fe86` |

Arbitrary deformations, independent frame rotations, and blocks displaced
farther than `1/50` remain outside this certified branch. The audit does not
infer that every four-core configuration belongs to it.
