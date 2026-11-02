# The surviving double-weak outward fork occurs strictly below Q

November 2, 2026 UTC / November 1 America/Chicago. Exact hand
construction. One bounded 24-start numerical direction check suggested
testing this shape; neither its numerical output nor its program is
proof evidence. Every coordinate, separator, and corner comparison
needed for the present example is printed and verified below.
No Lean, Lake, or CI was used.

Put Q=1105/256. Three units are coordinate-aligned, with centers

\[
 E=(-5/4,-1/2),\qquad F=(-1/4,1/2),\qquad T=(0,3/2).
\]

Two units are 45-degree diamonds, with common side axes
(1,1)/sqrt(2) and (1,-1)/sqrt(2), and centers

\[
 C=((1+\sqrt2)/4,-\sqrt2/4),\qquad
 D=((1+3\sqrt2)/4,\sqrt2/4).
\]

## 1. All ten physical pairs

The pairs E,F and F,T have actual coordinate gaps one. The pair E,T
has horizontal gap 5/4>1. The remaining axis-separated mixed pairs
have support sum 1/2+1/sqrt(2), and satisfy the following comparisons:

| Pair | Actual separating coordinate and center gap |
|---|---|
| E,C | x: 3/2+sqrt(2)/4 |
| E,D | x: 3/2+3sqrt(2)/4 |
| F,D | x: 1/2+3sqrt(2)/4 |
| T,C | y: 3/2+sqrt(2)/4 |
| T,D | x: 1/4+3sqrt(2)/4 |

All five gaps exceed the support sum. For the smallest final
comparison the excess is (sqrt(2)-1)/4>0; the other comparisons
are immediate positive differences as well.

For F,C the center difference is (p,-p), where
p=(2+sqrt(2))/4. Its projection on the actual diamond normal
(1,-1)/sqrt(2) is

\[
                       \sqrt2p=\frac12+\frac1{\sqrt2},
\]

exactly the sum of the two physical support halfwidths. For C,D,
the center difference is (1/sqrt(2),1/sqrt(2)); its projection on
(1,1)/sqrt(2) is one, exactly the support sum of the two diamonds.
These verify the remaining two pairs and all ten interior-disjointness
conditions.

## 2. The exact fork and marked links

E to F has center difference (1,1), so it is an actual diagonal
comparison in both coordinates. The successive differences F to C
and C to D have equal absolute coordinate gaps, respectively
p and 1/sqrt(2), and positive x-gaps. They are cone comparisons.
Both are weak: p<1/2+1/sqrt(2), and 1/sqrt(2)<sqrt(2).
Finally F to T has difference (1/4,1), so F\prec_y T.

Thus E,F,C,D is a completed four-chain with marked pattern (011),
and the additional y-cone successor of F is present. The central
branch square C has h_C=1/sqrt(2)>8/15, exactly as required by
`DIAGONAL_ACTUAL_TIE_BRANCH_TILT_HAND_PROOF.md`.

## 3. Exact subcritical containing disk

The maximum squared corner norms are

| Square | Maximum squared corner norm |
|---|---:|
| E | 65/16 |
| F | 25/16 |
| T | 17/4 |
| C | (21+6sqrt(2))/16 |
| D | (53+10sqrt(2))/16 |

For the two diamonds, the center has larger horizontal magnitude
than vertical magnitude, so the farther horizontal vertex is the
farthest corner. This gives the two displayed expressions directly.
Using sqrt(2)<3/2, both are strictly less than 17/4. The aligned
corner calculations are immediate from (|x|+1/2)^2+(|y|+1/2)^2.

Every square is therefore contained in the closed disk of squared
radius 17/4, with exact reserve

\[
                          Q-17/4=17/256>0.
\]

This five-square example does not supply the remaining four squares
or the full six row/column cone chains of the nine-square first-birth
normal form. It shows that eliminating the surviving outward (011)
branch requires those extra geometric constraints or another genuine
global consequence. No numerical infeasibility assertion is made.
