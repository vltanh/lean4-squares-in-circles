# At most five unit-square centers lie in the radius 41 over 40 disk

**Theorem.** A family of pairwise open-interior-disjoint unit squares with
centers in the closed disk of radius `R=41/40` has at most five members.
Orientations are unrestricted. No enclosing disk for the entire squares
is required.

Together with [RATIONAL_CORE_RADIUS.md](RATIONAL_CORE_RADIUS.md), this gives
three necessary core/ring count cases for an eleven-square packing in
`q<=49013/10000`:

| Core centers of norm `<41/40` | Ring centers of norm `>=41/40` |
| ---: | ---: |
| 3 | 8 |
| 4 | 7 |
| 5 | 6 |

This closes the six-core row left by
[SIX_CORE_CENTER_BOUND.md](SIX_CORE_CENTER_BOUND.md). It does not decide any
of the three remaining rows or establish the candidate radius as optimal.

## 1. Necessary distances and the six-square reduction

Every unit square contains the open disk of radius `1/2` about its center.
Consequently centers of distinct squares have distance at least one.

The six-core theorem shows that there are at most six squares, and that
any six include exactly one square containing the origin in its open
interior. Suppose six exist. Write `c` for the center of that square,
`d=|c|`, and call the remaining five squares the neighbors. Since the
origin is inside the central square,

\[
 d<1/\sqrt2<3/4.
\]

Each neighbor avoids the origin in its open interior. In its own frame,
at least one absolute center coordinate is at least `1/2`, so its center
radius `r` lies in `[1/2,R]`.

## 2. Neighbor center rays are more than one radian apart

Suppose two neighbor center rays have minor angular difference `theta<=1`.
The alternating Taylor bound gives

\[
 \cos 1\ge 1-\frac12+\frac1{24}-\frac1{720}
 =\frac{389}{720}>\frac{27}{50}.
\]

Their squared center distance is therefore strictly less than

\[
 r^2+s^2-\frac{27}{25}rs.
\]

This expression is convex separately in `r` and `s`, so its maximum on
`[1/2,R]^2` occurs at a corner. The three corner values are

\[
 \frac{23}{100},\qquad \frac{5977}{8000},\qquad
 \frac{38663}{40000},
\]

all less than one. This contradicts the necessary center distance.
Thus every pair of neighbor center rays has minor angular difference
strictly greater than one radian.

## 3. The central square center is within 3 over 40 of the origin

Assume, for a contradiction, `d>=3/40`. For any neighbor center, let
`theta` be its angle from the ray through `c`. The necessary separation
from `c` gives

\[
 \cos\theta\le \frac{r^2+d^2-1}{2rd}
 \le \frac{R^2+d^2-1}{2Rd}=:h(d).                 \tag{1}
\]

The second inequality follows because the preceding expression is strictly
increasing in `r` when `d<1`.

The function

\[
 h(d)=\frac{d+(R^2-1)/d}{2R}
\]

is convex on the positive real axis. Hence on `[3/40,3/4]` it is bounded
above by the larger of its endpoint values,

\[
 h(3/40)=\frac{15}{41}<\frac25,
 \qquad h(3/4)=\frac{327}{820}<\frac25.
\]

All five neighbor rays consequently lie in the single closed angular arc
where `cos(theta)<=2/5`. That arc has length `2pi-2acos(2/5)<4`.
For a rational verification of the strict comparison, the alternating
Taylor lower bound at `x=23/20` gives

\[
 \cos(23/20)-\frac25
 \ge 1-\frac{x^2}{2}+\frac{x^4}{24}-\frac{x^6}{720}-\frac25
 =\frac{387656111}{46080000000}>0.
\]

Thus `acos(2/5)>23/20`, and `pi<22/7` gives

\[
 2\pi-2\arccos(2/5)<\frac{44}{7}-\frac{23}{10}
 =\frac{279}{70}<4.
\]

Order the five neighbor rays within this arc. Each of its four successive
angular gaps exceeds one: if a gap were at most one, its corresponding
minor angular difference would be at most one, contrary to Section 2.
Their total span therefore exceeds four, a contradiction. We conclude

\[
                        d<3/40.                 \tag{2}
\]

## 4. Five neighbors cannot occupy four narrow regions

Use the central square's own orthonormal axes and put its center at zero.
Each neighbor center now has norm at most `R+d<11/10`.

The open radius-`1/2` disk about a neighbor center is disjoint from the
open interior of the central square. Therefore that center has distance
at least `1/2` from the closed central square `[-1/2,1/2]^2`. (If its
distance were smaller, an interior point of the central square would also
be inside the neighbor's open disk.)

Write its coordinate magnitudes as `X,Y`. If both exceed `1/2`, put
`u=X-1/2`, `v=Y-1/2`. The preceding distance bound implies
`u^2+v^2>=1/4`, and hence `u+v>=1/2`. It follows that

\[
 X^2+Y^2=u^2+v^2+u+v+1/2\ge5/4,
\]

contradicting the strict norm bound `11/10<sqrt(5)/2`.

Thus at least one of `X,Y` is at most `1/2`. In this case distance at
least `1/2` from the central square forces the other coordinate magnitude
to be at least one. Every neighbor center therefore belongs to one of
the four regions

\[
 x\ge1,\qquad x\le-1,\qquad y\ge1,\qquad y\le-1.
\]

Within the norm-`11/10` disk these four regions are pairwise disjoint.
Five neighbor centers force two into the same region. For example, in
`x>=1`, their first coordinates belong to `[1,11/10)` and their second
coordinates belong to `(-sqrt(21)/10,sqrt(21)/10)`. Their squared mutual
distance is strictly less than

\[
 (1/10)^2+(2\sqrt{21}/10)^2=\frac{17}{20}<1,
\]

again impossible. The other three regions are identical after an isometry.
This excludes six squares and proves the theorem.

## Exact scope

The proof uses only necessary center distances, a previously proved
unit-circle arc lemma to identify the unique origin-containing square
when six centers are present, and the inscribed disks of the five
neighbors. It assumes neither common square orientations nor a central
square in general eleven-square configurations. A central square was
deduced only within the hypothetical six-core case that has now been
excluded. All original pair constraints remain relevant in the three
remaining count rows.
