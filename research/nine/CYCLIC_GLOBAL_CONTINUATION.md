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
