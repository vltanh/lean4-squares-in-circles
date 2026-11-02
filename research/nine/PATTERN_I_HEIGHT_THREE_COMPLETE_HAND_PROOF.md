# Pattern I is closed when both original projection heights are at most three

November 2, 2026. Complete hand proof of the stated one-exception branch.
No mathematical script, numerical enumeration, Lean, Lake, or CI is used.

This note synthesizes the previously reviewed rank reductions and separating
direction estimates, and closes the final missing-top-left diagram. It proves
the sharp lower bound \(q\ge1105/256\) under the stated hypotheses.
It does not assert an unrestricted two-direction-cover theorem or an
unrestricted equality classification.

## 1. Exact scope and the normalized nine-square arrangement

There are nine physical unit squares with disjoint open interiors in a disk
of squared radius q. Fix perpendicular axes for which every pair except a
genuine exceptional pair is separated in x- or y-projection. Assume both
original actual projection orders have height at most three.

The preceding augmented-order and width-five reductions route any remaining
strict subcritical configuration into Pattern I. The completed rank reductions
in
[PATTERN_I_NINE_SQUARE_CONTINUATION.md](PATTERN_I_NINE_SQUARE_CONTINUATION.md)
then give a common three-row rank diagram:

| Actual y-rank | Squares, in increasing actual x-rank |
|---|---|
| 3 | Two squares, with one of the three columns absent |
| 2 | A,B in column one; C in column two; D in column three |
| 1 | L in column one; M in column two; R in column three |

These are longest-chain rank cells, not physical center coordinates.
All row comparisons except A,B are actual. All within-column comparisons
except A,B are actual y-comparisons. In particular,
\[
 B<_xC<_xD,\quad L<_xM<_xR,\quad
 L<_yA,B,\quad R<_yD.                                  \tag{1}
\]
With the chosen fat x-direction,
\[
 d:=x_B-x_A\ge g_A+g_B,\qquad
 g_S=\frac1{4h_S},\quad \frac12\le h_S\le\frac1{\sqrt2}.
\]
Set
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad c_0=\frac{59}{60},\quad b_0=\frac1{60}.
\]
We may work at q≤Q and aim either at an already proved sharp terminal
q≥Q or at a strict contradiction. Every center has norm below ρ, and
\[
 x_A<-c_0-g_A,
 \qquad x_B+h_B<b_0.                                   \tag{2}
\]
If T is the first of the two actual top-row squares, far-endpoint
uniqueness proves the actual comparison B<_yT. Hence
\[
                          y_B+h_B<\frac{61}{60}.        \tag{3}
\]

## 2. The completed separating-direction cover when V<2

Write
\[
                         V=|y_A-y_B|+h_A+h_B.           \tag{4}
\]
The following results are already proved in the linked hand notes:

| Owned physical separating normal | Proved outcome |
|---|---|
| Any upward normal | Strict contradiction at q≤Q, by `PATTERN_I_STEEP_UPWARD_HAND_PROOF.md` together with its small-slope cap |
| Downward slope at most 18/25 | Strict contradiction, by `PATTERN_I_DOWNWARD_OWNER_EXTENSION_HAND_PROOF.md` |
| Either sign, slope from 18/25 through 15/4, assuming V<2 | Strict contradiction, by Section 10 of `PATTERN_I_NINE_SQUARE_CONTINUATION.md` |
| A owns a downward slope at least 21/10 | Strict contradiction, by `PATTERN_I_STEEP_DOWNWARD_HAND_PROOF.md` |
| B owns a downward slope at least 13/4 | Strict contradiction, by the same steep-downward note |

Here owned means parallel to a physical side normal of one of the two
squares. Such a separating direction exists by the elementary square
separating-axis theorem. Section 10 of the rank continuation proves that
every separating normal points right: fat x gives
\(d\ge g_A+g_B\ge k_A+k_B\), which excludes a left-pointing normal
by the genuine overlap of the pair's y-projections. A horizontal normal
would be an actual x-separation and is likewise impossible for the genuine
exception.

Thus the table is exhaustive whenever V<2. For a downward owned normal,
the low range ends at 18/25, the middle range extends through 15/4, and
the appropriate large-slope range begins at 21/10 or 13/4, both below
15/4. There is no uncovered endpoint or slope interval. Consequently
\[
                  \boxed{V<2\quad\Longrightarrow\quad
                         \text{strict contradiction at }q\le Q.}       \tag{5}
\]
This implication uses all the actual normalized comparisons, rather than
asserting a terminal for an arbitrary seven-square weak-chain core.

## 3. The two diagrams with an occupied top-left cell

If the top-left cell is occupied by F, the first column gives
\[
                        L<_yA,B<_yF.
\]
Hence
\[
                       y_F-y_L\ge h_L+h_F+V.           \tag{6}
\]
One of the other columns is a disjoint actual y-three-chain. If V≥2,
(6) and that chain provide the long and short physical endpoint spans
of the established four-plus-three terminal, yielding q≥Q.
If V<2, (5) gives a contradiction.

Therefore both top-left-present diagrams reach the desired lower bound.

## 4. Reduce the missing-top-left diagram to an actual upper three-chain

The only other rank diagram is
\[
\begin{array}{ccc}
 \text{missing}&T&U\\
 A,B&C&D\\
 L&M&R.
\end{array}                                             \tag{7}
\]
Its two full columns give
\[
                  M<_yC<_yT,\qquad R<_yD<_yU,
\]
and the top row gives T<_xU. We already know B<_yT.

If A<_yT as well, L and T are actual lower and upper neighbors of
both exceptional squares. When V≥2, they supply the long vertical
endpoint span; the disjoint right column R,D,U supplies the short one.
This yields q≥Q. The V<2 alternative is excluded by (5).

It remains to consider A not actually below T. The reverse y-comparison
is excluded by their actual y-ranks; the reverse x-comparison is excluded
by x-ranks. Since A,T are not the exceptional pair, the original cover
therefore forces
\[
                           A<_xT<_xU.                  \tag{8}
\]
We will show V<2 directly in this last case, completing the proof by (5).

## 5. A universal bound on the outer square's upper edge

For every square A satisfying the weak-chain bound in (2),
\[
                           y_A+h_A<\frac{11}{8}.        \tag{9}
\]
This assertion is independent of the normal's owner and its vertical sign.

Write the center as \((-X,Y)\), with X>c_0+g, and put
\(h=h_A\), \(k=\sqrt{1/2-h^2}\). Suppose instead Y+h≥11/8.

If its upper-left vertex offsets are \((-h,k)\), the horizontal
magnitude of that vertex exceeds c_0+g+h≥119/60, and its y-coordinate is
\[
 Y+k\ge\frac{11}{8}-(h-k)>\frac23,
\]
using \(h-k\le1/\sqrt2<17/24\). Therefore
\[
                         q>\left(\frac{119}{60}\right)^2+
                                  \left(\frac23\right)^2>Q.
\]

In the other orientation, its upper-left vertex is \((-k,h)\), and
its lower-left vertex is \((-h,-k)\). If h≤27/40, then
\[
 g\ge\frac{10}{27},\qquad k>\frac{21}{100},\qquad
 X+k>\frac{25}{16}.
\]
The upper-left vertex gives
\[
                     q>\left(\frac{25}{16}\right)^2+
                              \left(\frac{22}{16}\right)^2
                       =\frac{1109}{256}>Q.
\]
If h≥27/40, the functions h+1/(4h) and −(h+k) increase. Since
\(k(27/40)=\sqrt{71}/40<17/80\),
\[
                     X+h>\frac{81}{40},\qquad h+k<\frac{71}{80}.
\]
The lower-left vertex consequently has
\(Y-k>11/8-71/80=39/80\), and
\[
                   q>\left(\frac{81}{40}\right)^2+
                            \left(\frac{39}{80}\right)^2
                     =\frac{27765}{6400}=Q+\frac7{320}>Q.
\]
All orientations contradict containment, proving (9).

## 6. Shifted inscribed corners and a lower bound on L's upper edge

The following useful bound follows directly from the inscribed g-square.
If a physical unit has left edge at least ℓ and bottom edge at least v,
and 1+ℓ,1+v are nonnegative, its inscribed upper-right corner has
coordinates at least \((1+\ell,1+v)\), because h+g≥1. Thus
\[
                         q\ge(1+\ell)^2+(1+v)^2.       \tag{10}
\]
Independent coordinate reflections give all four versions. The offsets
ℓ,v themselves may be slightly negative; positivity of the shifted
coordinates is the only needed sign condition.

Section 2 of `PATTERN_I_STEEP_UPWARD_HAND_PROOF.md` gives
\[
                            y_R+h_R<-\frac1{40}.        \tag{11}
\]
This implies the convenient lower bound
\[
                            y_L+h_L>-\frac{11}{15}.     \tag{12}
\]
For a direct proof set
\[
              a_L=-x_L-h_L,\qquad b_R=x_R-h_R.
\]
The actual bottom three-chain gives a_L+b_R≥1. The center-radius bound
and that same chain give a_L,b_R>−1/60, so their shifted coordinates in
(10) are positive.

If L's upper edge were at most −11/15, the reflected shifted-corner
bound would force
\[
                             a_L+1<\frac76,
\]
since \((7/6)^2+(26/15)^2>Q\). Similarly (11) forces
\[
                             b_R+1<\frac{11}{6},
\]
since \((11/6)^2+(41/40)^2>Q\). Their sum is below three, contradicting
a_L+b_R≥1. This proves (12).

## 7. The missing-top-left diagram forces V<2

Assume the actual upper chain (8). It yields
\[
 x_U-h_U\ge x_A+h_A+2h_T\ge x_A+h_A+1
                         >h_A-\frac{31}{60}.            \tag{13}
\]
The final strict inequality follows from x_A>−ρ.

### 7.1. The larger-halfwidth case

If h_A≥77/120, (13) gives U's left edge strictly above 1/8.
Since D<_yU, U's lower edge is at least D's upper edge. If D's upper
edge were at least 3/4, (10) would give
\[
                  q>\left(\frac98\right)^2+
                           \left(\frac74\right)^2
                    =\frac{1108}{256}>Q.
\]
Thus D's upper edge is below 3/4, and R<_yD gives
\[
                            y_R+h_R<-\frac14.           \tag{14}
\]
The aggregate bottom-three support terminal now forces
\[
                            y_L+h_L>-\frac58.           \tag{15}
\]
Indeed otherwise the two endpoint upper edges would sum to strictly
less than −7/8, yielding q>Q.

Both exceptional lower edges are above −5/8 by L<_yA,B and (15).
Both exceptional upper edges are strictly below 11/8: this is (9) for A,
and (3) for B. Their entire vertical union therefore has length below two,
which in particular gives V<2.

### 7.2. The smaller-halfwidth case

If h_A≤77/120, then h_A<13/20. The coordinate-only calculations in
Sections 4.1--4.2 of
`ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` show that
\(X>c_0+g\), \(Y>h-b_0\) would force h>13/20.
Taking the contrapositive,
\[
                       y_A\le h_A-\frac1{60},
 \qquad                y_A+h_A\le\frac{19}{15}.        \tag{16}
\]
This does not assume an actual perpendicular three-chain at A.

The upper edge of B is also below 19/15, by (3). Both exceptional lower
edges are above −11/15 by (12). Their vertical union has length strictly
less than
\(19/15+11/15=2\), so V<2 again.

Sections 7.1--7.2 exhaust h_A. Implication (5) now excludes the last
missing-top-left case at q≤Q.

## 8. Conclusion and limits

Every normalized original-height-three Pattern I diagram either supplies
the already proved physical four-plus-three sharp terminal, yielding
q≥1105/256, or contradicts q≤1105/256 strictly. Together with the earlier
rank and width reductions, this closes Pattern I under the explicit
hypothesis that both original actual projection heights are at most three.

The separate actual-height-four bridge and completed Pattern II capacity
theorem are needed to synthesize a full one-exception theorem. The
unrestricted nine-square problem still requires a proved global geometric
caller into the available coordinate-cover or physical-terminal classes;
no such caller is asserted here.
