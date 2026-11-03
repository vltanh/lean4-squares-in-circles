# The central-capacity consequences still require a ninth-original coupling

November 3, 2026. Exact hand obstruction to a weakened extraction premise.
This note concerns **eight** physical squares. It is not a nine-square
counterexample, does not close any mask or original, and does not weaken
any all-nine theorem.

## 1. The precise obstruction

There are eight physical unit squares strictly inside the circle of squared
radius `Q=1105/256`, with pairwise disjoint open interiors, which have all
three properties below:

1. Every original obeys `max(|c_i·u_i|,|c_i·v_i|)>27/100`, and exactly two
   originals meet the open disk of radius `23/100`.
2. Every center-cone four-chain, in every orthonormal frame and with every
   relabeling, has **all three** consecutive links weak. There is no
   center-cone four-chain containing even one actual projection link.
3. There is **no cover by two fixed projection-separating directions**,
   even when those two directions may be oblique to one another.

Thus the two consequences of the reviewed all-nine central-arc theorem,
when used only as extra conditions on a retained eight-square subsystem,
do not force either the actual-cone-four caller or the two-direction-cover
caller. A new proof must retain the ninth square in another joint physical
argument. The result does not say that such an argument is impossible.

The construction is a small exact rotation of the two top squares in
`EIGHT_ORIGINAL_ALL_WEAK_EXTRACTION_OBSTRUCTION.md`, together with one
common vertical translation. The rotation removes its two-direction cover;
the estimates below prove that the all-weak extraction obstruction survives.

## 2. Exact centers and independent physical frames

Put

`c=159999/160001`, `s=800/160001`,

`d=1/c=160001/159999`, `X=d/2`,

`h=(c+s)/2=160799/320002`, `delta=h-1/2=399/160001`,

`b=-83/120`, `m=37/120`, `T=m+1/2+h=97/120+h`.

Then `c^2+s^2=1`, `0<s<c`, and

`X<501/1000`, `1/2<h<503/1000`, `0<delta<1/400`.

Use the following eight original squares:

| Original | Center | Own first axis | Own second axis |
|---|---|---|---|
| A | `(-1,b)` | `(1,0)` | `(0,1)` |
| B | `(-1,m)` | `(1,0)` | `(0,1)` |
| C | `(0,m)` | `(1,0)` | `(0,1)` |
| D | `(X,T)` | `(c,s)` | `(-s,c)` |
| E | `(0,b)` | `(1,0)` | `(0,1)` |
| F | `(1,b)` | `(1,0)` | `(0,1)` |
| G | `(1,m)` | `(1,0)` | `(0,1)` |
| H | `(-X,T)` | `(c,s)` | `(-s,c)` |

The first six aligned squares form two rows of three. Horizontal neighbors
are one unit apart, and `m-b=1`, so their open interiors are disjoint.

The bottom support height of either rotated top square is

`T-h=m+1/2=97/120`.

This equals the top support height of the middle aligned row. Therefore
both top squares are vertically separated from all six aligned originals.
Finally their center difference is `(d,0)`, whose projection on `(c,s)` is
`dc=1`. Each top square has width one on this own axis, so their open
interiors are disjoint too. All 28 pair constraints are retained.

## 3. Strict containing-circle bound

For every top-square point, the coordinate bounds give

`|x| <= X+h < 201/200`,

`|y| <= T+h =97/120+2h <363/200`.

Hence its squared norm is strictly below

`(201/200)^2+(363/200)^2 =17217/4000`.

The exact containing-circle reserve is

`Q-17217/4000 =389/32000 >0`.

For the bottom aligned row, the largest squared corner norm is

`(3/2)^2+(143/120)^2 =52849/14400 <4<Q`.

For the middle aligned row it is

`(3/2)^2+(97/120)^2 =41809/14400 <4<Q`.

Thus every corner of every original is strictly inside the required disk.
Convexity of the disk gives containment of each whole square.

## 4. Both global central consequences hold exactly

For A, B, F, G the first own-center coordinate has absolute value one.
For C and E the own-coordinate maxima are respectively `37/120` and
`83/120`, both strictly greater than `27/100`.

For D and H, `T>1` implies `||c_i||^2>1`. Since the own frame is
orthonormal, its larger squared own-center coordinate is at least
`||c_i||^2/2>1/2>(27/100)^2`. Therefore every original satisfies the
strict own-axis exclusion, and none contains the closed `23/100` disk.

C contains the origin in its interior, so its clearance is zero. E's
nearest point to the origin lies on its top side, at height `-23/120`;
thus its clearance is `23/120<23/100`.

A and F have horizontal clearance at least `1/2`. B and G also have
horizontal clearance `1/2`. D and H lie entirely above `97/120`, which is
larger than `23/100`. Consequently **exactly C and E** meet the open
central disk. The independent rational checker also evaluates the exact
own-coordinate distance formula for every square.

## 5. No cover by any two fixed projection directions

Among the aligned originals there is a pair with center difference `(1,0)`
and a pair with center difference `(0,1)`.

For an aligned unit square, its width in a unit direction `(p,q)` is
`|p|+|q|`. Separating the first pair by that projection requires

`|p| >= |p|+|q|`,

so `q=0`: that direction must be horizontal. Separating the second pair
requires `p=0`: that direction must be vertical. Any two-direction cover
of all eight originals must therefore use horizontal and vertical,
up to signs and order.

The top pair has horizontal center gap `d=1/c`, whereas its sum of
horizontal halfwidths is `2h=c+s`. Their difference is strictly positive:

`c+s-1/c = s(c-s)/c >0`.

Their vertical center gap is zero. Thus their open projections overlap
in both mandatory directions, and no two-direction cover exists.

This argument allows arbitrary fixed directions initially; it does not
assume that the purported two directions are perpendicular.

## 6. Uniform support control for every witness frame

Fix any unit witness axis `e=(p,q)` and put

`a=|p|`, `b0=|q|`, `h0=(a+b0)/2`, `epsilon=1/250`.

Then `a^2+b0^2=1` and `1/2<=h0<=1/sqrt(2)`.
The six aligned originals have projection halfwidth exactly h0. For either
rotated original, the triangle inequality for absolute values gives

`|h_i(e)-h0| <= (1-c+s)h0`.

Here `1-c+s=802/160001` and `h0<5/7`, so

`(1-c+s)h0 <4010/1120007 <1/250=epsilon`.

Consequently all eight original halfwidths satisfy

`h0-epsilon <= h_i(e) <= h0+epsilon`.

Each square contains the aligned inset of halfwidth `g_i=1/(4h_i(e))`.
For a center-cone link, the horizontal gap is the larger absolute
coordinate gap. Disjointness of the two original insets therefore forces
that gap to be at least `g_i+g_j`.

If a cone four-chain had one actual consecutive link, its three gaps
would have total at least

`L(h0)=2(h0-epsilon)+1/(h0+epsilon)`.

Indeed the actual gap contributes at least `2(h0-epsilon)`; each of
the other two cone gaps contributes at least `1/(2(h0+epsilon))`.
This remains valid if additional links are actual, and retains all ties.

## 7. Exact span contradiction on the entire direction domain

The center set is symmetric under horizontal reflection. Its projection
span in any direction with `a=|p|`, `b0=|q|` is exactly

`W=max(2a+b0, (1+X)a+(2+delta)b0)`.

This follows directly by taking maxima and minima over the three rows.
It does not depend on the top squares' orientations.

### 7.1. Directions with `h0<=69/100`

The enclosing center rectangle has width two and height `2+delta`, so

`W<=4h0+delta <4h0+1/400`.

The decreasing function `1/t-2t`, at `t=h0+epsilon<=347/500`, gives

`L(h0)-4h0 >=500/347-347/250 =4591/86750 >1/400`.

Hence `L(h0)>W` on this whole direction interval.

### 7.2. Directions with `h0>=69/100`

Now `a+b0>=69/50` and

`(a-b0)^2=2-(a+b0)^2 <=239/2500 <(31/100)^2`.

Therefore `a,b0>107/200`.
The first expression in W is below `4h0-1/4`, because its deficit
from `4h0` is `b0>107/200>1/4`.
For the second expression the deficit is

`(1-X)a-delta*b0 > (499/1000)(107/200)-1/400`

`=52893/200000 >1/4`.

Thus `W<4h0-1/4` throughout this interval.

On the other hand, using `1/h0-2h0>=0` and `h0>=1/2`,

`L(h0)-4h0 = (1/h0-2h0)-epsilon/[h0(h0+epsilon)]-2epsilon`

`>= -6epsilon=-3/125`.

Since `3/125<1/4`, again `L(h0)>W`.

Sections 7.1–7.2 cover all directions, including the common endpoint.
A proposed cone four-chain cannot have a span both at least L and at
most W. It follows that **every cone four-chain of these eight originals
has main mask 111**, in every frame and with every relabeling.

## 8. A literal `111/11` witness remains

Use the diagonal witness frame

`e=(1,1)/sqrt(2)`, `f=(-1,1)/sqrt(2)`.

The chains A,B,C,D and E,F,G are center-cone chains. AB, BC, EF, FG have
one original coordinate difference zero and the other one, so their
witness coordinate gaps tie and their actual projection comparisons fail.
CD has positive original coordinate differences `X` and `1/2+h`, so
it is a cone link. Its witness horizontal gap is

`(X+1/2+h)/sqrt(2)`.

The endpoint halfwidth sum is `(1+c)/sqrt(2)`, and
`X+1/2+h<1+c` by the displayed rational constants. Thus CD is weak too.
H is a retained eighth physical original outside the selected seven.

## 9. What remains missing

The actual-four occupancy assembly requires an **actual cone four-chain**
and the retained original-nine caller. The two-direction theorem requires
a cover of **all pairs** by two fixed physical projection directions.
Neither hypothesis follows from this eight-original physical subsystem,
even after adding both global central-capacity consequences.

This is stopping evidence for that weakened extraction route. It does not
rule out a theorem that uses the ninth original's position, frame, all its
pair separations, and its interactions with the central originals. Such a
shared ninth-original argument, or a complete equivalent all-nine case
cover, remains the missing step. No ledger, mask, or positional root is
changed by this note.
