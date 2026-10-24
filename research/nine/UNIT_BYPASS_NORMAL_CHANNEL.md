# A unit-square bypass forces a single side-normal transmitter

**Status: complete hand geometric implication; independent full hand audit passed.**
Suppose a positive normal-transmission path joins squares B,D and
contains at least one internal square. If another interior-disjoint
unit square A physically touches both B and D, then the path has
exactly one internal body and that body is side-normal to the channel.
Its reserve is exactly one.

There is no containing-circle hypothesis, no assumed common frame,
and no normal genericity assumption in this theorem. It gives a complete
width reduction for every clear degree-two transmitter in a physical
four-cycle, but does not exclude the surviving side-normal cycles.

## 1. The normal channel is a shortest segment

The force and torque equations at each unloaded degree-two internal
body give the normal-channel statement of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md. There are a unit vector n,
actual endpoint contacts p_B in B and p_D in D, and a positive reserve
L such that

\[
 p_D-p_B=L n,
 \qquad n\cdot b\le n\cdot p_B\quad(b\in B),
 \qquad n\cdot d\ge n\cdot p_D\quad(d\in D).
 \tag{1}
\]

The reserve is the sum of the projected widths of the internal bodies.
Each width is exactly one or sqrt(2), according as the transmission
direction is a side axis or a diagonal of that unit square.

Choose any q_B in A intersect B and q_D in A intersect D. Equation
(1) and the unit-square diameter give

\[
       L\le n\cdot(q_D-q_B)\le |q_D-q_B|\le\sqrt2.
 \tag{2}
\]

Two or more internal bodies would give L at least2, contrary to (2).
There is exactly one internal body U, and only its side-normal or
diagonal alternative remains.

## 2. The diagonal alternative is impossible

Suppose L=sqrt(2). Every comparison in (2) is then equality:

\[
                         q_D-q_B=\sqrt2\,n.
 \tag{3}
\]

The points q_B,q_D are opposite vertices of A, since the diameter of
a unit square is attained only at opposite vertices. Also they attain
the two endpoint supporting planes in (1):

\[
                 n\cdot q_B=n\cdot p_B,
                 \qquad n\cdot q_D=n\cdot p_D.
 \tag{4}
\]

The diagonal transmitter U likewise has opposite vertices p_B,p_D.
Thus A and U have the same square frame, with a diagonal parallel to n.
Their centers are the respective midpoints of their two endpoints.
By (3), their center displacement equals

\[
                          c_A-c_U=q_B-p_B,
                          \qquad n\cdot(c_A-c_U)=0.
 \tag{5}
\]

Both q_B and p_B lie in B's same support face normal to n. A support
face of a unit square is either a vertex or a side of length one.
Consequently

\[
                              |c_A-c_U|=|q_B-p_B|\le1.
 \tag{6}
\]

On the other hand, two same-frame unit squares whose center displacement
is perpendicular to a common diagonal can have disjoint interiors only
if that displacement has length at least sqrt(2). Indeed its absolute
components on each side axis are both \(|c_A-c_U|/\sqrt2\),
and at least one such component must be at least one for the two open
unit projection intervals to be disjoint. This contradicts (6).

Therefore the diagonal alternative cannot occur. The unique internal
body U has width one and is side-normal to n. \(\square\)

## 3. Exact consequences and scope

Every positive four-cycle with a zero-circle-weight degree-two vertex
falls under this theorem: the opposite cycle vertex is the unit-square
bypass. Its transmitter must therefore be side-normal. All arbitrary
application heights on the two opposite faces remain; the theorem does
not replace them by the body's side midpoints.

The same result excludes a longer all-clear transmitter path whenever
its two endpoint bodies have any other common physical unit neighbor,
even if one or both contacts to that neighbor have zero stress.

In the opposite-loaded-pair residual of C1.4.b1.C4, the clear cycle
vertex is consequently a single side-normal transmitter of reserve1.
Its frame need not equal the radial leaf's or the articulation's frame.
The remaining shared-side means, corner masks and four exterior
completion squares are not discarded, and that residual class is not
closed here.

No Lean compilation, CI, pose grid, or numerical optimizer is used.

## 4. The bypass and transmitter are separated transversely

**This additional full-chart consequence has passed an independent hand
audit, separately from Sections 1--3.**

Rotate and translate the surviving side-normal alternative so that

\[
                     U=[-1/2,1/2]\times[0,1].
\]

Then B lies below y=0 and D above y=1. Since A touches both, its
vertical projection contains the whole interval [0,1]. Nevertheless A
has disjoint interior from U. These conditions force A to lie entirely
to the left or entirely to the right of U.

Here is the complete separating-axis calculation, including a tilted A.
Let its two coordinate halfwidths be w/2, where

\[
                 w=a+b,\qquad a,b\ge0,\qquad a^2+b^2=1,
\]

and write its center displacement from U as (x,y). The projection
containment gives

\[
                              |y|\le\frac{w-1}{2}.
\tag{7}
\]

Some side axis of A or U separates the two squares. The vertical axis
cannot do so, because their vertical projections overlap in an interval
of length one. If the horizontal axis separates them, its condition is
already

\[
                              |x|\ge\frac{w+1}{2}.
\tag{8}
\]

Otherwise a separating side axis of A has absolute horizontal and
vertical components (a,b), or (b,a). In the first case the separator
condition and (7) imply

\[
       a|x|\ge\frac{w+1-b(w-1)}2\ge\frac{a(w+1)}2,
\tag{9}
\]

because the exact difference of the doubled numerators is

\[
              (1-a)(w+1)-b(w-1)=2b(1-a)\ge0.
\tag{10}
\]

If a=0 this proposed separator is vertical and is impossible; otherwise
(9) gives (8). Interchanging a and b proves the other side-axis case.
Thus (8) always holds. Since A's horizontal halfwidth is w/2 and U's
is 1/2, (8) is precisely horizontal projection separation.

**Corollary 4.1.** Every unit bypass in this theorem is separated from
its unique side-normal transmitter by a line parallel to the transmission
direction. In the original invariant notation, the two squares are
separated along the transmitter's axis Jn.

The separation may have a positive gap. If it is a contact and A is
tilted, A's unique transverse support vertex meets a transmitter side.
No contact between A and U, common frame, centered application, or
additional positive edge is inferred merely from this separation.
