# Three balanced boundary squares: the full-window metric exclusion

**Status: complete new uniform hand proof, submitted for independent review.**
This strengthens `GENERAL_BALANCED_THREE_BOUNDARY_CENTER_DISTANCE_EXCLUSION.md`
from its stated local range `R >= 2` to the complete original range

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

The local theorem below is self-contained. In particular, it does not use the
same-nine radius-two theorem or any analytic prerequisite of that theorem.
No new original fine or coarse gate is declared closed by this strengthening.

## 1. Whole physical statement

Let the original physical unit squares be interior-disjoint and contained in
the disk of radius `R` about its unchanged origin. Let `A,B,C` be three distinct
physical boundary squares. On each square assign nonnegative weights to its
actual physical circle corners, with strictly positive total weight. Write
`F_A,F_B,F_C` for the three corresponding outward circle resultants, using the
same normalization on all three squares, and assume

\[
                         F_A+F_B+F_C=0.
\tag{2}
\]

**Theorem.** Their actual centers cannot simultaneously satisfy

\[
 |c_A-c_B|\le\sqrt2,\qquad
 |c_A-c_C|\le1+\sqrt2,\qquad
 |c_B-c_C|\le1+\sqrt2.
\tag{3}
\]

The theorem permits every actual radial mask and zero individual corner
weight. Pair degrees, pair forces, owners, side applications and other
neighbors are unrestricted. There is no change to the physical squares,
circle, normals or original means.

## 2. Uniform center radii and the actual circle-corner cone

Put

\[
 Q=\frac{1105}{256},\qquad m=\frac{19}{15},\qquad M=\frac{91}{60}.
\]

For any contained unit square with center radius `r`, its farthest corner
has squared radius at least `r^2+r+1/2`. Indeed, in its own orthonormal axes,
if the center coordinates are `(x,y)`, that farthest squared radius is
`r^2+|x|+|y|+1/2`, and `|x|+|y| >= r`. Consequently

\[
                         r<M,
\quad M^2+M+\tfrac12-Q=\frac{31}{57600}>0.
\tag{4}
\]

For a physical boundary square, its actual circle corner is at distance
`1/sqrt(2)` from its center, so

\[
 r\ge R-\frac1{\sqrt2}
 >\frac{79}{40}-\frac{17}{24}
 =m,
\quad (17/24)^2-\tfrac12=\frac1{576}>0.
\tag{5}
\]

Every actual circle corner makes angle strictly less than `pi/12` with its
own center direction. To prove this for all physical masks, take outward own
coordinates at that corner, so

\[
 z=(a,b),\quad a\ge b\ge\tfrac12,\quad q=a^2+b^2=R^2,
 \qquad c=(a-\tfrac12,b-\tfrac12).
\]

The weak inequalities follow by comparing the circle corner with its two
adjacent contained corners. For its angular deviation `delta`,

\[
 \tan\delta=\frac{a-b}{2q-a-b}.
\]

With `t=a+b`, the expression is
`sqrt(2q-t^2)/(2q-t)`. Its derivative has the sign of `1-t`, which is negative
on this domain. Its maximum is therefore attained at `b=1/2`, where the
expression is `1/(2 sqrt(q-1/4))`. The exact comparisons

\[
 q-\frac14-\left(\frac{15}{8}\right)^2
 \ge\left(\frac{79}{40}\right)^2-\frac14-
       \left(\frac{15}{8}\right)^2
 =\frac{27}{200}>0,
\]

\[
 \tan\delta<\frac4{15}<2-\sqrt3=\tan\frac{\pi}{12},
 \qquad (26/15)^2-3=\frac1{225}>0
\tag{6}
\]

give the claimed strict angle. The diagonal corner, where the displayed
numerator vanishes, is included directly. Thus each nonnegative circle
resultant of positive total weight is nonzero and stays strictly within the
same open angular interval of radius `pi/12` about its center direction.

## 3. Resultants have the actual center order

The minor angular separation of any two of these boundary centers exceeds
`pi/6`. Otherwise, with their radii `r,s` from (4)--(5),

\[
 |c_i-c_j|^2
 =r^2+s^2-2rs\cos\gamma
 <r^2+s^2-\frac{12}{7}rs,
\tag{7}
\]

because `cos gamma >= sqrt(3)/2 > 6/7`. The last comparison has squared
reserve `3/4-36/49=3/196`. The expression on the right of (7) is convex in
each variable separately, so its maximum on `[m,M]^2` occurs at a corner.
The three distinct corner values are

\[
 \begin{array}{c|c}
 (r,s)&r^2+s^2-(12/7)rs\\ \hline
 (m,m)&722/1575\\
 (m,M)&2201/3600\\
 (M,M)&1183/1800
 \end{array}
\]

and all are strictly below one. This contradicts the center separation
`|c_i-c_j| >= 1`, since every unit square contains its open radius-`1/2`
incircle and the original unit interiors are disjoint.

The three open `pi/12` angular intervals from (6) are consequently disjoint.
Their nonzero resultants are distinct in direction and have exactly their
centers' circular order. Three distinct directions of nonzero vectors
summing to zero cannot be collinear. Every consecutive directed resultant
gap is therefore strictly less than `pi`: a gap at least `pi` would put
all vectors in a closed half-plane, where cancellation would force all
vectors onto its boundary line.

Taking compatible lifts of the center and resultant angles in their common
order, each center-to-resultant correction has absolute value less than
`pi/12`. Every consecutive **directed** center gap is thus strictly below

\[
                             \frac{7\pi}{6}.
\tag{8}
\]

We have not yet assumed these directed gaps are minor gaps.

## 4. The three distances cannot fit around the circle

Since

\[
 \sqrt2<\frac{99}{70},\qquad
 1+\sqrt2<\frac{169}{70},\qquad
 (99/70)^2-2=\frac1{4900}>0,
\]

the distance formula

\[
 |c_i-c_j|^2=(r-s)^2+4rs\sin^2(\gamma_{ij}/2)
\]

and `r,s>19/15` imply from (3) that

\[
 \gamma_{AB}<2v,\qquad
 \gamma_{AC}<2u,\qquad
 \gamma_{BC}<2u,
\quad
 v=\arcsin\frac{297}{532},\quad
 u=\arcsin\frac{507}{532}.
\tag{9}
\]

Here the constants are exactly
`(99/70)/(2(19/15))=297/532` and
`(169/70)/(2(19/15))=507/532`.

We claim `2u+v<pi`. Both `pi-2u` and `v` lie strictly between zero and
`pi/2`, because `u>pi/4`; moreover

\[
 \sin(2u)>\sin v
\]

is exactly the following strictly positive squared comparison:

\[
 4\cdot507^2(532^2-507^2)-297^2\cdot532^2
                         =1742127084>0.
\tag{10}
\]

Sine is strictly increasing on that interval, so (10) yields

\[
                       2u+v<\pi.
\tag{11}
\]

Also `v>pi/6` since `297/532>1/2`, and `v<u`. Thus (11) gives
`2u<5pi/6`: every pairwise minor center angle in (9) is strictly below
`5pi/6`.

If a consecutive directed center gap were a major gap, its complementary
minor gap would be below `5pi/6`; the directed gap would then exceed
`7pi/6`, contradicting (8). A gap equal to `pi` likewise contradicts
(9). Therefore all three directed gaps are their respective minor angles.
Their sum must be `2pi`, whereas (9)--(11) give a sum strictly smaller
than `2v+4u<2pi`. This proves the theorem on the entire range (1).

## 5. Existing three-spoke pentagon caller on its whole original window

For the original gate `M6.B6.PENTAGON.H3.L013`, the physical rim is
`0-1-2-3-4-0`, the interior hub has original positive spokes `H0,H1,H3`,
and precisely `0,1,3` have positive circle load. The two genuine unloaded
degree-two rim vertices are `2,4`. The actual hub is a unit bypass for
both original paths `1-2-3` and `0-4-3`.

The complete theorem `UNIT_BYPASS_NORMAL_CHANNEL.md` makes both true
channels side channels of width one, retaining every original normal
and the common actual transverse mean. If `P,Q` are the two original
means of such a side transmitter, `|P-Q|=1`, whence

\[
 |c_X-c_Y|\le |c_X-P|+|P-Q|+|Q-c_Y|
 \le\frac1{\sqrt2}+1+\frac1{\sqrt2}=1+\sqrt2.
\]

Consequently `|c_1-c_3|,|c_0-c_3| <= 1+sqrt(2)`. The actual rim contact
`01` gives `|c_0-c_1| <= sqrt(2)`. Summing the unchanged force equations
over the original six-body component cancels every original pair force
and gives `F_0+F_1+F_3=0`. The full-window theorem applies.

This recovers the already accepted whole original fine gate on (1),
including both radial masks, every original mean, every nonnegative
corner split with positive root total, every positive original pair
weight, and all three unchanged extra physical units. It uses no
separate radius-two lower bound. The six-body graph and its full true
degrees are those of `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md`. The two
caller dependencies are in addition to the self-contained metric
proof in Sections 1--4; they do not become premises of that theorem.

## 6. Publication scope

This is a uniform mathematical strengthening, not a new count entry.
It does not itself exclude the open four-spoke pentagon families.
Any use with three selected boundary squares still requires balance
of precisely their three actual circle resultants; a fourth positive
circle load cannot be discarded.
