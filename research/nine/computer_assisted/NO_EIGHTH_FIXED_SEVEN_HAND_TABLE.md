# Exact no-extension certificate for the rational seven-square 000/01 control

This is a rigorous **fixed-pose** continuous geometric exclusion, NOT an unrestricted nine-square proof, an A.2 closure, or a new canonical root exclusion. Computation discovered 58 rational boxes; every bound can be replayed using exact fractions. This records a working computer-first-to-hand-table pilot.

The original seven centers and first axes (unit second axes are their counterclockwise perpendiculars) are:

| Square | Center | First axis |
|---|---|---|
| M0 | (-3/2,0) | (1,0) |
| M1 | (-1/2,-1) | (1,0) |
| M2 | (1/2,-1) | (1,0) |
| M3 | (3/2,0) | (1,0) |
| L | (-11/12,1) | (1,0) |
| P | (1/12,25/112) | (1,0) |
| R | (79/84,121/112) | (4/5,3/5) |

All 21 pair interior-disjointness tests hold; all 28 corners have squared norm strictly less than 273/64<Q=1105/256. The two displayed disjoint center-cone chains have mask 000/01.

**Theorem.** With the seven above unchanged, no eighth independently oriented physical unit square can be inserted into the closed disk of squared radius Q=1105/256.

**Center constraints.** Any Q-contained unit square has center norm <rho=91/60, because its maximum squared corner norm is at least |c|^2+|c|+1/2 and rho^2+rho+1/2-Q=31/57600>0. Two squares whose open interiors are disjoint have center distance >=1, since each contains its open centered radius-1/2 disk.

**Exact box cover.** Begin with [-rho,rho] × [-rho,rho]. Repeatedly bisect the LONGER coordinate interval at its midpoint (tie: x). Digit 0 denotes left/bottom and digit 1 right/top; both halves retain common boundaries. Every terminal rectangle has one of the following rational contradictions:

* outer: min squared norm over box is >=rho^2;
* center_i: max squared distance to the fixed center of square i over box is <1;
* cap: entire box lies in [-1/12,1/12] × [4/3,rho].

The table is prefix-free, contains 58 terminal rows and 57 binary internal nodes, and has maximum depth 13. There are no missing children. For [x0,x1] × [y0,y1], evaluate exact bounds as

    min |c|^2 = max(x0,-x1,0)^2 + max(y0,-y1,0)^2;
    max |c-(a,b)|^2 = max(|x0-a|,|x1-a|)^2 + max(|y0-b|,|y1-b|)^2.

**Cap terminal.** For R center (79/84,121/112), axes u=(4/5,3/5),v=(-3/5,4/5), the absolute projections of a center in the cap obey

    |u·(c-c_R)| <= 1121/1680,
    |v·(c-c_R)| <= 289/300.

Hence squared distance from c to the actual closed R-square is at most

    (1121/1680-1/2)^2+(289/300-1/2)^2
      = (281/1680)^2+(139/300)^2
      = 1/4-518311/70560000 < 1/4.

The new square contains an open disk of radius 1/2 about c, so it necessarily intersects the interior of R, irrespective of its orientation. This disproves the cap. Every possible eighth center falls into one of the listed contradictions. QED.

| Binary path | Terminal reason |
|---|---|
| `000000` | `outer` |
| `0000010` | `outer` |
| `0000011` | `center_1` |
| `00001` | `center_1` |
| `00010` | `center_0` |
| `000110` | `center_1` |
| `000111` | `center_0` |
| `0010` | `center_1` |
| `001100` | `center_1` |
| `00110100` | `center_1` |
| `00110101` | `center_0` |
| `0011011` | `center_5` |
| `001110` | `center_1` |
| `001111` | `center_5` |
| `01000` | `center_0` |
| `010010` | `center_0` |
| `010011` | `center_4` |
| `0101` | `center_4` |
| `0110` | `center_5` |
| `01110` | `center_4` |
| `011110` | `center_4` |
| `0111110` | `center_4` |
| `01111110` | `center_4` |
| `011111110` | `center_4` |
| `01111111100` | `center_4` |
| `011111111010` | `center_4` |
| `011111111011` | `cap` |
| `011111111100` | `center_4` |
| `0111111111010` | `center_4` |
| `0111111111011` | `cap` |
| `01111111111` | `cap` |
| `1000` | `center_2` |
| `100100` | `center_2` |
| `100101` | `center_5` |
| `100110` | `center_2` |
| `100111` | `center_5` |
| `10100` | `center_2` |
| `101010` | `outer` |
| `1010110` | `center_2` |
| `1010111` | `outer` |
| `101100` | `center_2` |
| `101101` | `center_3` |
| `10111` | `center_3` |
| `1100` | `center_5` |
| `110100` | `center_5` |
| `11010100` | `center_6` |
| `110101010000` | `center_6` |
| `110101010001` | `cap` |
| `11010101001` | `center_6` |
| `11010101010` | `cap` |
| `11010101011` | `center_6` |
| `110101011` | `center_6` |
| `1101011` | `center_6` |
| `11011` | `center_6` |
| `111000` | `center_3` |
| `111001` | `center_6` |
| `11101` | `center_3` |
| `1111` | `center_6` |

The independent Fraction-only verifier reconstructs every rectangle from its path, verifies all 58 terminal inequalities, checks that the binary trie is complete and nonoverlapping as a path list, checks the original seven square poses, and checks the cap margin. Deleting or corrupting rows is rejected. An optional generator regenerates the path list. No floating-point proof comparisons enter this certificate.

**Strict limitation.** The full nine-square mask allows all seven selected poses and both remaining squares to move. The no-extension theorem for the ONE fixed seven-square arrangement cannot be used to mark 000/01 closed or to update the 7,915-root counter. The global strict-radius nonlinear nine-square formula still has no verified UNSAT certificate. Lean, Lake and CI remain deferred.
