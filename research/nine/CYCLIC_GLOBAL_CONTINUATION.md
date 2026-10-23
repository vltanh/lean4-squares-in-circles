# n=9: a uniform angular budget for every circle-touching square

**Status:** complete hand necessary-condition argument, pending independent
review. This does **not** close the unrestricted nine-square lower bound or
any remaining whole coarse cyclic cell. It excludes every physical packing
with eight or more circle-touching squares in the declared radius window,
regardless of stress choice, contact graph, or individual orientations.

Read base: PR #11, `6b235bda64b1064a89835eeef8b18634e213a061`.
The circle center is zero and

\[
             79/40\le R\le\sqrt{1105}/16.
\]

## 1. Statement

**Theorem A.** Every unit square contained in the disk of radius `R` and
touching its boundary contains an open arc of the circle of radius `5/4`
whose angular length is strictly greater than `pi/4`. The arc lies in the
**open interior** of the square, apart from any chosen limiting endpoints.

**Corollary B.** At most **seven physical squares** in any interior-disjoint
packing can touch the containing circle. In particular, every positive
physical stress component has at most seven loaded bodies.

This counts physical boundary-touching bodies, including those assigned
zero circle multiplier; it is stronger than a statement about one chosen
stress. It does not assert that seven such bodies are achievable in every
radius in the window.

## 2. Exact own-frame description

Take a corner `z` of the square on the outer circle. Choose the two inward
unit side directions at `z` as coordinate axes. If `z=(a,b)` in these axes,
the entire square is

\[
             [a-1,a]\times[b-1,b],\qquad a^2+b^2=R^2.
\]

Containment of the adjacent corners `z-u` and `z-v` gives `a,b>=1/2`.
Exchange the two axes so that `a>=b`. Put

\[
        r=5/4,\qquad A=a-1,\quad B=b-1,\quad q=R^2.
\]

The radius window gives the following deliberately loose strict bounds:

\[
 R<25/12,\quad a>11/8>r,\quad a<81/40,\quad b<3/2.
\tag{1}
\]

Indeed, `1105/256 < (25/12)^2`. Also
`a^2>=R^2/2>121/64`, because `6241/3200>121/64`.
Since `b>=1/2`,
`a^2<=R^2-1/4<589/144<(81/40)^2`.
Finally `b^2<=R^2/2<(25/12)^2/2<9/4`.
Thus

\[
          3/8<A<41/40,\qquad -1/2\le B<1/2.
\tag{2}
\]

Every point of the inner circle lying in the square has positive first
coordinate. Write such a point as `r(cos(phi),sin(phi))`, with
`-pi/2<phi<pi/2`. Define

\[
 \alpha=\arccos(A/r),\quad
 \beta=\arcsin(B/r),\quad
 \gamma=\arcsin(\min(b/r,1)).
\]

The upper constraint `x<=a` is redundant because `a>r`. The remaining
three constraints yield precisely the angular interval

\[
             [\max(-\alpha,\beta),\min(\alpha,\gamma)].
\tag{3}
\]

Moreover `(2)` implies

\[
 A^2+B^2<(41/40)^2+1/4=2081/1600<r^2.
\]

Hence `beta>-alpha` (automatic if `B>=0`, and otherwise obtained by
comparing the positive square roots). The interval in `(3)` is therefore
`[beta,min(alpha,gamma)]`. We prove both differences from `beta` exceed
`pi/4`.

## 3. The two inner faces leave more than a quarter right angle

The decisive exact inequality is

\[
       E:=(a-1)^2+(b-1)^2+\sqrt2(a-1)(b-1)<25/32=r^2/2.
\tag{4}
\]

Here is a whole-angle proof. At fixed `q`, set `s=a+b`. Since
`ab=(s^2-q)/2`,

\[
 E=(1-1/\sqrt2)q+s^2/\sqrt2-(2+\sqrt2)s+2+\sqrt2.
\tag{5}
\]

This is convex as a function of `s`. For `a>=b>=1/2` and `a^2+b^2=q`,
the allowed `s` interval runs from `1/2+sqrt(q-1/4)` to `sqrt(2q)`.
The lower endpoint follows either by differentiating
`sqrt(q-b^2)+b`, whose derivative is nonnegative for `b<=a`, or by
squaring. Thus the maximum in `(5)` occurs at one of the two endpoint
configurations `b=1/2` and `a=b`.

At `b=1/2`, put `A=a-1`. Since `sqrt2>7/5`,

\[
 E=A^2+1/4-(\sqrt2/2)A
   <A^2+1/4-(7/10)A
   <933/1600<25/32.
\tag{6}
\]

The second strict inequality uses `3/8<A<41/40`; the polynomial is
increasing there and its value at `41/40` is `933/1600`.

At `a=b=R/sqrt2`, the expression is increasing with `R>sqrt2`, so

\[
 \begin{aligned}
 E&=(2+\sqrt2)(R/\sqrt2-1)^2\\
  &<(2+\sqrt2)(25/(12\sqrt2)-1)^2
    =(626-287\sqrt2)/288<25/32.
 \end{aligned}
\tag{7}
\]

The last comparison is equivalent to `401<287 sqrt2`, which follows
from `401^2=160801<164738=2*287^2`. This proves `(4)` without an angle
grid or numerical minimization.

By `(2)`, `sqrt2 A+B>0`: indeed `sqrt2>4/3` and `A>3/8`.
Inequality `(4)` therefore implies

\[
 \sqrt2 A+B<\sqrt{r^2-B^2},
 \qquad
 A<r\cos(\beta+\pi/4).
\]

Since `|B|<=1/2`, we have `|beta|<=arcsin(2/5)<pi/4`.
The angle `beta+pi/4` lies in `(0,pi/2)`. Monotonicity of cosine gives

\[
                         \alpha-\beta>\pi/4.
\tag{8}
\]

## 4. The parallel side strip leaves more than a quarter right angle

If `1/2<=b<r`, the function

\[
 b\longmapsto\arcsin(b/r)-\arcsin((b-1)/r)
\]

is nondecreasing: its derivative is

\[
 \frac1{\sqrt{r^2-b^2}}-
 \frac1{\sqrt{r^2-(b-1)^2}}\ge0,
\]

because `b>=|b-1|`. Continuity handles `b=r`. Consequently

\[
             \gamma-\beta\ge2\arcsin(2/5)>\pi/4.
\tag{9}
\]

The final strict inequality follows from
`sin(pi/8)=sqrt(2-sqrt2)/2<2/5`, for example using `sqrt2>7/5`.
If `b>=r`, then `gamma=pi/2` while `beta<pi/4`, so `(9)` is again
strictly greater than `pi/4`.

Combining `(8)` and `(9)` with `(3)` proves Theorem A. Every point of
the open angular interval satisfies all four square-face inequalities
strictly, so it is in the square's open interior.

## 5. Counting and the precise cyclic consequence

For interior-disjoint squares the open arcs furnished by Theorem A are
pairwise disjoint subsets of the **same** inner circle. Eight such arcs
would have total angular length greater than `8*pi/4=2*pi`, which is
impossible. This proves Corollary B.

For a positive triangle block, every nonarticulation vertex of that block
has positive degree two. It must be loaded, by the normal-channel lemma:
an unloaded two-force transmitter would make its two touching neighbors
have positive distance. Therefore the new angular budget excludes any
selected component with at least eight such distinct forced-loaded bodies.
For example, the arrangement of four triangle blocks sharing one common
articulation has eight nonarticulation bodies and is excluded uniformly.

**This does not close C4.3333.b0.** Other arrangements of four triangle
blocks can have two or more articulation bodies and only six or seven
forced-loaded bodies. They remain in that coarse cell. Nor does the
seven-body load cap exclude a generic three-, four-, five-, six-, or
seven-loaded cyclic component.

## 6. Remaining boundary

The result supplies an exact global angular budget that does not assume a
common frame and does not use force coefficients. It does not yield the
sharp nine-square bound: circle-clear squares can meet the inner circle in
arbitrarily short arcs, or lie wholly inside it. A completion argument must
therefore retain their geometry instead of assigning each a fictitious
`pi/4` arc.

No numerical optimizer, Lean compilation, CI, whole-proof audit, or
unrestricted optimality is claimed here.

## 7. Independent incidence lemma: no triple boundary-touching junction

The following statement uses only `R>sqrt2`; it does not depend on
Theorem A, the research-window upper bound, or the selected stress.

**Theorem C.** Let interior-disjoint closed unit squares be contained in
the disk of radius `R>sqrt2`. At most two of the squares that touch the
containing circle can contain any prescribed point `p`.

Here "touch the containing circle" is a physical property. A square
assigned zero circle multiplier is still counted if it touches the
circle. The theorem excludes a triple boundary-touching junction. It
does **not** exclude a junction of two such squares with a circle-clear
square, or a triangle whose three pair contacts occur at distinct points.

### 7.1. Preliminary local alternatives

If `p` lies in the interior of one square, no other square can contain
`p`. If `p` is in the relative interior of a side of two distinct squares,
their two disjoint local open half-planes fill the available angular
space; a third square cannot contain `p`.

If `p` lies on the containing circle, it must be a vertex of each square
containing it. Both unit edges from `p` point strictly into the disk:
for an edge vector `u`, containment of `p+u` gives
`p dot u <= -1/2`. Hence each square's right-angle tangent sector lies
strictly inside the same inward open half-plane. Two disjoint sectors
of angle `pi/2` cannot fit in that open half-plane. Thus at most one
square contains such a `p`.

It remains to consider `|p|<R`, with either all incident squares having
`p` as a vertex, or one square having `p` in the relative interior of a
side. We handle these alternatives separately.

### 7.2. When every incident square has vertex `p`

If `p=0`, every point of an incident unit square is at distance at most
`sqrt2` from zero, so the square cannot touch the circle. Assume
`p=(r,0)` with `0<r<R`, after rotating coordinates, and put `q=R^2`.

A circle-touching corner `z` of a square with vertex `p` is either an
adjacent corner, with `|z-p|=1`, or the opposite corner, with
`|z-p|=sqrt2`. First suppose `z-p` has positive second coordinate.

For an adjacent corner there is at most one possibility

\[
 z-p=(\cos\theta_1,\sin\theta_1),\qquad
 0<\theta_1<\pi,\qquad
 \cos\theta_1=h_1:=\frac{q-r^2-1}{2r}.
\tag{10}
\]

Write `u=z-p`. The other unit edge from `p` must be `Ju`, rather than
`-Ju`: otherwise `z dot (-Ju)=r sin(theta_1)>0`, so `z-Ju` would lie
outside the circle. Thus the square's open tangent sector at `p` is

\[
                     (\theta_1,\theta_1+\pi/2).
\tag{11}
\]

For an opposite corner there is likewise at most one possibility

\[
 z-p=\sqrt2(\cos\theta_2,\sin\theta_2),\qquad
 0<\theta_2<\pi,\qquad
 \cos\theta_2=h_2/\sqrt2,
 \quad h_2:=\frac{q-r^2-2}{2r}.
\tag{12}
\]

The corresponding open tangent sector is

\[
                     (\theta_2-\pi/4,\theta_2+\pi/4).
\tag{13}
\]

If both possibilities exist, the sectors in `(11)` and `(13)` have
nonempty open overlap. To see this, set `c=1/(2r)`, so
`h_2=h_1-c` and `h_1>=-c`. If `h_1>=0`, then
`h_2/sqrt2<h_1`. If `h_1<0`, then
`h_2<=2h_1<sqrt2 h_1`, giving the same strict inequality. Hence
`theta_2>theta_1`.

Also

\[
                       q>(r-1)^2+1.
\tag{14}
\]

Indeed, the convex function `(r-1)^2+1` on `[0,R]` is bounded above
by the larger of its endpoint values `2` and `q-2R+2`; both are
strictly smaller than `q` because `R>sqrt2`. Equation `(14)` gives
`h_2>-1` and therefore `theta_2<3pi/4`. Consequently

\[
 \theta_2+\pi/4>\theta_1,
 \qquad
 \theta_2-\pi/4<\pi/2<\theta_1+\pi/2,
\]

as required. Two distinct squares with these sectors would have
overlapping interiors near `p`. The same is true if they use the same
candidate: an adjacent or opposite corner candidate determines the
square uniquely. It follows that at most one incident square can have
a circle-touching corner above `p`. Reflection gives the analogous
statement below `p`.

The only remaining possibility is a circle-touching corner on the
horizontal line through `p`. A positive horizontal adjacent edge is
impossible, since the next corner displaced by a perpendicular unit
edge would lie outside the circle. A negative horizontal adjacent or
opposite displacement cannot reach the circle when `0<r<R` and
`R>sqrt2`. A positive horizontal opposite displacement requires
`r=R-sqrt2`. In that case the circle has no point at distance `1` from
`p`, and its only point at distance `sqrt2` from `p` is that one outer
corner. It determines one square, leaving no other boundary-touching
incident square. Thus in every vertex-only case there are at most two.

### 7.3. One side-interior incidence

Suppose three circle-touching squares contain `p`, with `p` in the
relative interior of a side of the first. Its tangent sector has angle
`pi`. Each other square must have a vertex at `p` and a tangent sector
of angle `pi/2`. The sectors must partition the entire angular space,
so the three squares have a common frame. In coordinates relative to
`p`, they are necessarily

\[
 \begin{aligned}
 S&=[-1,0]\times[-t,1-t], &&0<t<1,\\
 B&=[0,1]\times[0,1],\\
 C&=[0,1]\times[-1,0].
 \end{aligned}
\tag{15}
\]

Let the actual coordinates of `p` relative to the disk center in this
frame be `(x,y)`. Equality of the farthest-corner radii of `B` and `C`
gives

\[
 \max(y^2,(y+1)^2)=\max(y^2,(y-1)^2),
\]

which forces `y=0`. Put

\[
 M=\max(x^2,(x+1)^2),\quad
 N=\max(x^2,(x-1)^2),\quad
 h=\max(t,1-t)\in[1/2,1).
\]

All three squares touching the circle now means

\[
                         q=M+1=N+h^2.
\tag{16}
\]

Since `h<1`, this requires `N>M`, hence `x<0`. If `x<=-1/2`, then
`N-M=1-2x>=2`, contradicting `N-M=1-h^2<=3/4`. Thus
`-1/2<x<0`, and `(16)` gives

\[
              -4x=1-h^2,\qquad -3/16\le x<0,
              \qquad q=(x+1)^2+1<2.
\]

This contradicts `R>sqrt2` and completes Theorem C.

### 7.4. Exact scope of the incidence consequence

In a physical contact incidence graph, every junction involving three
or more distinct squares therefore includes a circle-clear square.
A selected loaded triangle cannot be represented by one common
contact junction. These conclusions impose no unjustified planarity
claim on the body-pair graph, and do not close a remaining whole coarse
cyclic cell. In particular, the six- and seven-loaded arrangements
left in `C4.3333.b0` still need a separate argument.
