# From the twin scaffold toward the sharp obstruction

## Scope

This note starts with the following additional hypothesis on a
minimum-radius packing chosen to have the fewest actual contacting pairs:
two squares strictly inside the circle have actual degree two and share
the same two neighbors. The four-square theorem in
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md), section 9, applies.
It does not assume that the other four squares have either of the
candidate orientations.

The first proposition below identifies the central member of this
scaffold by ordinary geometry. The subsequent implication from this
scaffold to the complete five-corner chain is still being developed;
it is not a conclusion of the proposition.

Assume throughout that eight unit squares fit a disk centered at zero,
with squared radius at most `98/25` and radius less than two. The analytic
central-square theorem in
[HUMAN_GLOBAL_GEOMETRY_CLOSURE.md](HUMAN_GLOBAL_GEOMETRY_CLOSURE.md)
therefore supplies exactly one square containing zero in its open
interior.

## 1. One of the twin transmitters is the central square

**Proposition.** Under the twin hypothesis, the unique open central
square is one of the two twins. After a possible reflection in a
horizontal line through zero, the centers can be written

$$
B=(x+1,b),\qquad D=(x-1,d),\qquad
C=(x,c),\qquad T=(x,t),
$$

in their common horizontal and vertical frame, with

$$
|x|<\frac12,\qquad |c|<\frac12,\qquad
t>c+1>\frac12,
\qquad t-1<b,d<c+1.                                    \tag{1}
$$

Here `C` is the central square. The other four squares, whatever their
frames, are strictly separated from both `C` and `T` as closed sets.

**Proof.** The four-square theorem gives the displayed normal coordinates
and, after naming the twins in increasing height order,

$$
t-c>1,\qquad
c,t\in[\max(b,d)-1,\min(b,d)+1].                       \tag{2}
$$

In fact all four contact intervals on the twins' vertical sides have
positive length. If, for example, `|c-b|=1`, the contact of `C` with
`B` is a single endpoint. Translate `C` a sufficiently small distance
vertically away from `B`. This removes that contact. Both horizontal
separators from `C` to `B,D` remain valid independently of the change
of height, so neither pair acquires an interior overlap. Strict disk
containment of `C` and all its formerly positive distances from the
other squares persist under a sufficiently small translation. The
contact count has decreased, a contradiction. The same argument
applies to each of `C-B,C-D,T-B,T-D`. Thus all four corresponding
height differences have absolute value strictly below one.

Consequently

$$
c<b,d<t,\qquad t-1<b,d<c+1,\qquad 1<t-c<2.             \tag{3}
$$

For example, `b>=t-1>c` and `b<=c+1<t`, and the same argument
applies to `d`. The strict upper bound on `t-c` follows from
`t-1<b<c+1`.

The rightmost point of `B` has horizontal coordinate `x+3/2`, and
the leftmost point of `D` has coordinate `x-3/2`. Disk containment
with `R<2` gives

$$
-\frac12<x<\frac12.                                   \tag{4}
$$

Thus `B` and `D` cannot contain zero even as a point of their closed
squares. Also `t+1/2<R<2` and `c-1/2>-R>-2`. Together with
`t>c+1`, these imply

$$
c-\frac12<0<t+\frac12.                                \tag{5}
$$

Indeed, the first disk bound gives `c<t-1<1/2`, and the second gives
`t>c+1>-1/2`.

Consider the open rectangle

$$
\mathcal H=(x-1/2,x+1/2)\times(c+1/2,t-1/2).            \tag{6}
$$

It has width one and height `t-c-1`, strictly between zero and one.
Its bottom and top edges are sides of `C` and `T`. Its left and
right edges are covered by `D` and `B`: both neighbor height intervals
contain `[c+1/2,t-1/2]`, by (3). Its entire boundary therefore lies
in the union of the four closed scaffold squares. Its interior is
disjoint from that union. It follows directly that `H` is a connected
component of their open complement: any continuous path from a point
of the rectangle to its exterior must first meet its boundary.

The open interior of any other square is disjoint from every closed
scaffold square. To see the small boundary point here, an open set
containing a boundary point of a closed square also contains interior
points of that square. Thus pairwise disjoint square interiors exclude
such a boundary point as well. Since a square's open interior is
connected, if it meets `H`, its whole open interior lies in `H`.
That is impossible. A unit square in any frame has vertical projection
of length `|cos(theta)|+|sin(theta)|>=1`, whereas `H` has height
strictly less than one.

By (4)--(5), zero lies either in one of the two twins, on a twin's
boundary, or inside `H`. The last possibility is incompatible with the
existence of an open central square: neither a scaffold square nor any
other square can contain zero there. The boundary possibility is also
incompatible with an open central square, by the same boundary argument
in the preceding paragraph. Hence the central square is one of the
twins. Reflect vertically if it is the upper twin, then rename the
lower central twin `C` and the other twin `T`. This gives (1), using
the fact that zero lies in the open square `C`.

Finally, each twin has actual degree exactly two, and its neighbors are
exactly `B,D`. Every other closed square is therefore disjoint from
each twin. Their positive distances follow from compactness. `QED`

### The gap may be filled, and the twins may be made into a domino

Let

$$
K=[x-1/2,x+1/2]\times[c-1/2,t+1/2].
$$

Every remaining square is interior-disjoint from this entire solid
rectangle. Its open interior avoids both twins and the bounded gap
`H`, by the proof above. These three regions exhaust the interior
of `K` except for straight joining segments, and an open set meeting
such a segment also meets one of the three open regions. Thus there
is no omitted boundary channel.

The rectangle `K` is the convex hull of `C` and `T`. It is strictly
inside the disk, since its four vertices are vertices of the two
strictly contained twins. For a packing normal form, one may therefore
replace `T` by the standard square with center `(x,c+1)`. This new
square is a subset of `K`, is disjoint in open interior from `C`,
and remains separated from `B,D` by their unchanged horizontal
separators. It is interior-disjoint from every remaining square by
the solid-rectangle conclusion. The containing radius does not
increase.

After this replacement `C,T` form an exact vertical `1 by 2` domino.
The old inequalities also give `c<b,d<c+1`, so both side neighbors
overlap the heights of both halves of that domino. The replacement
can create extra boundary contacts; it is used as a radius-preserving
packing normal form, not as a new claim about the minimum contact
count of the original representative.

## 2. Immediate disk and cap restrictions

In the coordinates of the proposition, the exact farthest-corner
inequalities for the scaffold are

$$
\begin{aligned}
(x+3/2)^2+(|b|+1/2)^2&\le R^2,\\
(x-3/2)^2+(|d|+1/2)^2&\le R^2,\\
(|x|+1/2)^2+(t+1/2)^2&<R^2.
\end{aligned}                                           \tag{7}
$$

The final inequality is strict because `T` is strictly inside the
circle. In particular

$$
c<\sqrt{R^2-(|x|+1/2)^2}-\frac32.                      \tag{8}
$$

No unit square can lie wholly to the right of `B`, wholly to the left
of `D`, or wholly above `T`, where these directions mean separation
beyond the corresponding scaffold side. Indeed, those three supporting
lines have respective coordinates

$$
x+\frac32>1,\qquad x-\frac32<-1,\qquad t+\frac12>1.
$$

A unit square has width at least one in each of these directions, so
such a separated square would have a point whose corresponding
coordinate has absolute value greater than two, contradicting `R<2`.

These exclusions concern full square projections. They do not exclude
a square separated from a scaffold neighbor on one of its own rotated
axes. In particular they do not prove that all four remaining squares
lie below `C`, that two of them are parallel to `B,D`, or that a
parallel tilted pair has been identified.

## 3. A two-unit corner span without an orientation assumption

The next lemma retains arbitrary frames on the four remaining squares.

**Projection lemma.** Let `Q` be a unit square with horizontal and
vertical sides, and let `S` be any unit square with disjoint open
interior. Write the difference of their centers as `(a,d)`, and let
`L=|cos(theta)|+|sin(theta)|` be the vertical width of `S`. If
`|a|<=7/8`, then

$$
|d|+\frac{1+L}{2}\ge2.                                 \tag{9}
$$

If equality holds, `S` is parallel to `Q` and `|d|=1`.
Thus the lowest vertex of the lower-center square and the highest
vertex of the higher-center square have vertical distance at least
two. The inequality is strict for nonparallel frames.

**Proof.** Put `W=(1+L)/2`. This is the sum of the half-widths of
the two squares on either axis of `Q` or `S`. If (9) failed, then

$$
|a|\le7/8<W,\qquad |d|<2-W\le W,
$$

so no axis of `Q` separates the squares. On an axis of `S`, let
`c,s` be the absolute horizontal and vertical components. Then
`c,s>=0`, `c^2+s^2=1`, and `c+s=L`. Its center projection is at
most `c|a|+s|d|`. We claim

$$
\frac78 c+s(2-W)\le W.                                \tag{10}
$$

Indeed, twice the right side minus twice the left side is

$$
(1-s)^2+c\left(s-\frac34\right).                       \tag{11}
$$

For `s>=3/4` this is nonnegative, with equality only when `s=1`.
For `0<=s<3/4`, both terms compared in
`(1-s)^2>c(3/4-s)` are nonnegative. Squaring and dividing by
`1-s>0` reduces that strict inequality to

$$
P(s):=7-33s+56s^2-32s^3>0.
$$

It follows at once from

$$
P'(s)=-96\left(s-\frac7{12}\right)^2-\frac13<0,
\qquad P(3/4)=\frac14>0.
$$

This proves (10), strictly unless the selected axis is vertical.
If `s>0`, the strict bound on `|d|` now gives
`c|a|+s|d|<W`; if `s=0`, use `|a|<W` directly. No axis of
`S` separates either, contradicting the separating-axis theorem.
This proves (9).

If the frames are nonparallel, `L>1`; every axis of `S` has both
components nonzero and (10) is strict. At equality in (9), the
axes of `Q` still have strict projection overlap because
`|d|=2-W<W`, and (10) excludes the axes of `S`. This is again
impossible. Equality therefore requires parallel frames, for which
`W=1` and (9) gives `|d|=1`. `QED`

### Application to the scaffold's outer columns

Define

$$
\rho=\sqrt{R^2-\frac14}.
$$

Every square center `p`, in any frame, satisfies

$$
|p|\le\rho-\frac12.                                   \tag{12}
$$

The exact farthest-vertex squared norm is
`|p|^2+1/2+|p dot e|+|p dot f|`, which is at least
`|p|^2+|p|+1/2`; solving this quadratic proves (12).
The two first inequalities in (7) also give

$$
|x|\le\rho-\frac32.                                   \tag{13}
$$

Let `S` be any remaining square whose center has horizontal
coordinate `z>=x+1/2`. Its horizontal center displacement from `B`
satisfies

$$
-\frac12\le z-(x+1)\le2\rho-3
<\sqrt{15}-3<\frac78.                                  \tag{14}
$$

The middle strict inequality uses `R<2`; the last follows by
squaring `\sqrt{15}<31/8`, namely `960<961`.
The projection lemma therefore applies to `B,S`. In particular, if
`S` is below `B` in center height, its lowest vertex and `B`'s
highest vertex have vertical distance at least two. The same
conclusion, reflected horizontally, applies to `D` and every remaining
square whose center has horizontal coordinate `z<=x-1/2`.

Thus, if a remaining square is found below each outer neighbor in
these respective center regions, the first three projected-chain
inequalities can be obtained without first proving either remaining
square parallel to the scaffold: use its lowest vertex at each lower
end, and the upper outer corners of `B,D` for the horizontal span
three. These are actual disk points. The two final oblique inequalities
would still need their own proof using the two remaining squares.

### Centers in the middle strip are below the central square

For completeness there is a stronger, simpler consequence when
`|a|<=1/2`: disjointness implies `|d|>=1`. If both `|a|<=1/2`
and `|d|<1`, neither axis of `Q` separates. For an axis of `S`,
again with absolute components `c,s`,

$$
c|a|+s|d|\le\frac c2+s
\le\frac{1+c+s}{2}=W,
$$

where the second inequality is `s<=1`. The projection is strict:
if `s>0` use `|d|<1`, and if `s=0` use `c/2<W`.
The separating-axis theorem gives the contradiction.

Consequently, a remaining square with center `(z,h)` in the closed
middle strip `|z-x|<=1/2` satisfies

$$
|h-c|\ge1,\qquad |h-t|\ge1.
$$

Since `1<t-c<2`, these inequalities force `h<=c-1` or `h>=t+1`.
The second possibility is excluded by `t>1/2` and (12), since
`\rho-1/2<3/2`. Hence

$$
|z-x|\le\frac12\quad\Longrightarrow\quad h\le c-1.      \tag{15}
$$

This is a center-height statement. A rotated square may still extend
above the horizontal side of `C` while being separated on its own
axis; (15) does not replace that distinction by full vertical
separation.

## 4. The scaffold blocks the central square's two upper corner exceptions

Use the terminology in
[HUMAN_STRUCTURAL_LEMMAS.md](HUMAN_STRUCTURAL_LEMMAS.md): a square
is **corner-separated relative to `C`** when it is interior-disjoint
from `C` but neither central-axis separator exists. Its center and
its unique outward separating axis then lie in the same strict
quadrant relative to `C`.

**Proposition.** No remaining square is corner-separated relative to
`C` at its northeast or northwest corner. Thus at most two of the
seven other squares lack a separator parallel to an axis of `C`,
and any exceptions are assigned to its two lower corners.

This statement uses the four-square scaffold and its strict contact
overlaps, but does not require any orientation restriction on the
remaining squares.

**Proof.** Suppose a square `S` were corner-separated at the northeast
corner of `C`. Write its center relative to `C` as `(a,d)`. The
central corner lemma gives

$$
0<a<W,\qquad 0<d<W,\qquad
W=\frac{1+\gamma+\sigma}{2},\qquad
\gamma,\sigma>0,\quad \gamma^2+\sigma^2=1,              \tag{16}
$$

where `n=(gamma,sigma)` is the unique separating side normal of `S`
in the northeast quadrant. Set

$$
\Delta=t-c>1.                                          \tag{17}
$$

By section 1, `S` is interior-disjoint from the entire solid rectangle
`K`. The separating-axis theorem for the rectangle and square supplies
an axis of `K` or `S` separating them. Any such separator also
separates `S` from `C`, since `C` is a subset of `K`.
No axis of `K` can do this: those are precisely the axes of `C`,
excluded by the corner-separated hypothesis. Among the signed axes
of `S`, the only possible separator from `C` to `S` is the
unique vector `n` above. Thus `n` must also separate `K` from
`S`.

The support of `K` in direction `n` exceeds that of `C` by
`sigma Delta`. The separating inequality consequently requires

$$
W+\sigma\Delta\le\gamma a+\sigma d
<W(\gamma+\sigma)=W+\gamma\sigma
<W+\sigma\Delta.                                       \tag{18}
$$

Here `W(gamma+sigma-1)=gamma sigma`, and the last strict
inequality uses `Delta>1>=gamma`. This is a contradiction.

Reflection in the vertical axis gives the northwest case, with `D`
in place of `B`. The one-square-per-corner theorem in
HUMAN_STRUCTURAL_LEMMAS.md bounds the two remaining lower exceptions
by two in total. `QED`

The same argument, reflected vertically, says that no remaining
square is corner-separated relative to `T` at either of its two
lower corners. This second statement concerns `T` as the reference
square and does not identify it as central.

## 5. The sharp implication still to prove

The target is to obtain five disk points and an angle
`0<=t<=pi/4` satisfying the five projected inequalities in
[FIVE_CORNER_REDUCTION.md](FIVE_CORNER_REDUCTION.md), or to obtain a
stronger obstruction that excludes a radius below the unique exact
family optimum proved in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md).

The scaffold already gives a horizontal span of three between suitable
corners of `B,D`. Turning that span into the entire chain still
requires a theorem about the four remaining squares and their
separating directions. Their arbitrary frames are retained in this
open step; no six-parallel-square or common-tilt hypothesis is adopted.
