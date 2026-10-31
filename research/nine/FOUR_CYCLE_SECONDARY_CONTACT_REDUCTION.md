# A secondary radius minimizer has contact between a C4 bypass and transmitter

**Status: complete conditional minimizer reduction; Sections 1--7 passed
root's full hand audit and the independent full hand audit.**
For a sharp radius lower-bound proof, one may choose a
nine-square radius minimizer which, among all radius minimizers, minimizes
the sum of squared center norms. At such a packing, a surviving
opposite-loaded-pair C4-with-leaf certificate has an additional physical
contact between its leaf articulation A and its clear transmitter U.
The contact need not carry positive stress.

This uses the existing strict selected certificate. It changes neither
the point-normal convention nor any actual application mean. It is a
reduction at a canonical minimizer for the radius lower bound, not a
classification of every packing attaining that radius. No whole C4,
diamond, completion capacity or unrestricted nine-square closure is
asserted.

## 1. The secondary minimizer exists

Translate the containing-circle center to zero. At the minimum radius
R_*, the space of labeled nine-square packings is compact: centers are
bounded, the nine frame angles lie on a product of circles, containment
is closed, and interior nonoverlap is a closed separating-axis condition.
Therefore the continuous function

\[
                          \Phi=\sum_{i=1}^{9}|c_i|^2
\tag{1}
\]

attains its minimum on that space. Choose such a packing before making
the finite physical-normal selections and extracting a radius stress.
It is still a global radius minimizer, so every necessary certificate
and every previously proved whole-class exclusion applies unchanged.

For the proposed lower-bound contradiction assume, as usual, that

\[
                 79/40\le R_*\le\sqrt{1105}/16.
\tag{2}
\]

The lower endpoint is the separately imported lower window; the upper
endpoint is the radius range under examination. The secondary choice
is available without any assumption that all radius minimizers have
the same geometry.

## 2. The complete normal-channel domain

Suppose its selected positive component is the C4

\[
                            A-B-U-D-A
\]

with a pendant radial leaf at A, B,D loaded, and U of zero circle
weight. The unit-bypass theorem gives a side-normal channel of reserve
one and transverse separation of A,U. Rotate and reflect about zero so

\[
 U=[X-1,X]\times[Y,Y+1],\qquad
 A\subseteq\{x\ge X+g\},\qquad g\ge0,
\tag{3}
\]

where x=X+g is A's left support line. The projection of A on the
vertical axis contains [Y,Y+1]. The endpoint bodies satisfy

\[
                     B\subseteq\{y\le Y\},\qquad
                     D\subseteq\{y\ge Y+1\}.
\tag{4}
\]

The radial-leaf articulation estimate gives a point of A within

\[
       \varepsilon=\max(\sqrt{R_*^2-1/4}-2,0)<1/60
\tag{5}
\]

of zero. In particular

\[
                              X+g\le\varepsilon.
\tag{6}
\]

All these statements hold for every S/D leaf and every orientation of
A. Shared-side means on BU and UD remain their actual means.

## 3. A positive transverse gap lies inside the empty C4 hole

Suppose g>0. The four actual consecutive contact points of the cycle
are then distinct. BU and UD differ by the unit vertical reserve.
AB and AD have vertical coordinates at most Y and at least Y+1.
A contact shared by AB and BU would belong to both A and U, impossible
when g>0; the same applies at D. These observations also exclude any
opposite-contact coincidence.

The center/contact loop of the four bodies is therefore a simple
Jordan curve, by the usual open-interior center-spoke construction.
At any horizontal level y_0 strictly between Y and Y+1, its B and
D portions are absent by (4). Its U portion crosses that level
exactly once, at a point of U. Its A portion also crosses exactly
once, at a point of A. For the latter assertion, if the vertical width
of A is w<=sqrt(2), projection containment gives

\[
                   Y+1-w/2\le(c_A)_y\le Y+w/2.
\]

Thus its center lies strictly between Y and Y+1. The path from the
AB application through c_A to the AD application is strictly monotone
in height; its endpoints lie on opposite sides of the open interval.
The analogous U path is strictly monotone as well.

The bounded horizontal slice of the Jordan curve is the interval
between those two crossings. The U crossing has first coordinate at
most X, and the A crossing has first coordinate at least X+g.
Consequently the entire open rectangle

\[
                         (X,X+g)\times(Y,Y+1)
\tag{7}
\]

lies on the bounded side of the cycle.

`FOUR_CYCLE_LEAF_HOLE_EMPTY.md` excludes every further unit square
from this bounded side. More precisely, the open interior of any
other square avoids the closed four bodies and hence avoids the
center/contact loop. Its connected open interior is entirely on one
side of that loop. If it entered (7), it would be an additional unit
square in the forbidden C4 hole. Thus no other packing square has an
interior point in (7). The radial leaf is included among the other
squares; alternatively its circle contact alone puts it on the outer
side of this loop.

## 4. An inward translation contradicts secondary minimality

For any sufficiently small 0<t<g, translate U by t e_x, keeping
its frame and every other square fixed. It remains vertically between
B and D by (4), and it remains strictly to the left of A by (3).
Every newly occupied interior point lies in the rectangle (7).
Every other interior point was already in U. Section 3 therefore
preserves all nine-square nonoverlaps, including every unstressed
completion square.

Its center first coordinate is c_x=X-1/2. By (6), both before and
after the translation,

\[
                   c_x+t<X+g-1/2\le\varepsilon-1/2<0.
\tag{8}
\]

For an axis-aligned unit square with center (c_x,c_y), the maximum
corner squared radius is

\[
                    (|c_x|+1/2)^2+(|c_y|+1/2)^2.
\]

Equation (8) shows that the translation strictly decreases this
quantity. Thus U stays in the same containing disk, whether or not it
was physically circle-touching with zero multiplier. All other disk
constraints are unchanged.

At the same time its center contribution to (1) changes by

\[
                         2c_x t+t^2<0.
\tag{9}
\]

The translated configuration is therefore another packing in the
minimum-radius disk with strictly smaller Phi. This contradicts the
secondary choice. The assumption g>0 was impossible.

**Theorem 4.1.** At the secondary minimizer of Section 1, every
surviving opposite-loaded-pair C4-with-leaf component satisfies

\[
                              A\cap U\ne\varnothing.
\tag{10}
\]

This is a physical contact assertion only. The two existing channel
forces on U are opposite side-axis forces; no positive multiplier on
the transverse AU contact is inferred.

## 5. The nonparallel contact and its owner signs

The A/U-parallel case is already excluded in a compatible selected
certificate by `FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md`. In the
remaining case A is oblique to U. Its leftmost vertex is its only
point on x=X. That vertex lies strictly between Y and Y+1.
Indeed its vertical distances to A's lowest and highest vertices are
the two positive oblique side components, each strictly less than one.
Since A's vertical projection contains [Y,Y+1], this puts the leftmost
vertex strictly inside that interval.

Thus AU is a genuine vertex/relative-side-interior contact, owned by
U, with normal e_x from U to A. The physical triples A,U,B and
A,U,D are both contact triangles, even though AU has zero stress.
The radius-free triangle side-normal obstruction gives the following
exact consequences for any actual owned A-tip normal:

| Owned edge | Necessary sign, with n=e_y and m=e_x |
| --- | --- |
| A owns AB, normal n_B from A to B | n_B dot m<=0 |
| A owns AD, normal n_D from A to D | n_D dot m<=0 |
| B owns AB | n_B dot n<=0 |
| D owns AD | n_D dot n>=0 |

For example, if A owns AB, apply
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` at A to its AB normal
and its actual AU normal -m. If B owns AB, apply it at B to
-n_B and its BU normal n. The other two signs are the same
calculation. Equality is retained.

The new physical AU contact and these owner signs can be used in a
radius lower-bound argument at the canonical minimizer. They do not
by themselves give the missing completion bound, remove a physical
two-circle-corner mask, or classify noncanonical equality packings.

No Lean compilation, CI, numerical pose argument or change of the
strict physical-normal convention is used.

## 6. Every A-tip positive-length shared side is impossible

The following deductions remain conditional on the same canonical
minimizer and the physical contact proved above. They introduce no
additional minimization principle and no positive AU multiplier.

Write the oblique A using its leftmost vertex P as

\[
 \begin{split}
 P&=(X,y_0),\qquad Y<y_0<Y+1,\\
 v&=(a,b),\quad w=(b,-a),\quad a,b>0,\quad a^2+b^2=1,\\
 A&=P+[0,1]v+[0,1]w.
 \end{split}
\tag{11}
\]

Suppose AB has a positive-length shared side. Its normal from A to B
is an A side axis. Section 5 gives a nonpositive horizontal component.
The only such axes are -v and -w. The minimum-w face is
P+[0,1]v, entirely at height at least y_0>Y; it cannot meet B,
which lies below Y. Hence the shared normal is -v.

Every unit square sharing a positive segment of that face on its
other side has the form

\[
                    B=P-v+\tau w+[0,1]v+[0,1]w,
                    \qquad -1<\tau<1.
\tag{12}
\]

Its unique top vertex is P+tau w. Since B lies below Y and touches
U, its maximum height is exactly Y. Thus

\[
             \tau=\frac{y_0-Y}{a}>0,
             \qquad (P+\tau w)_x=X+\tau b>X.
\tag{13}
\]

But the top vertex is the only B point at height Y, so its contact
with U would have to be that vertex. The displayed horizontal
coordinate is outside U, a contradiction.

For AD, the same argument can be written without any reflection:
the only possible shared normal is -w, and

\[
                    D=P-w+\tau v+[0,1]v+[0,1]w.
\]

Its unique lowest vertex P+tau v must have height Y+1, so
tau=(Y+1-y_0)/b>0. Its horizontal coordinate X+tau a>X again
lies outside U. This excludes AD as well.

**Corollary 6.1.** At the canonical minimizer, neither AB nor AD
in a surviving opposite-loaded-pair C4-with-leaf component has a
positive-length physical intersection. Every such contact is a
singleton. This includes all physical circle masks of B and D and
does not fix, approximate or discard any shared-side mean on BU or UD.

## 7. The complete two-A-owned D-leaf alternative is impossible

Suppose the pendant leaf is radial D, and let e be its direction
from A to the leaf. The existing radial-D articulation theorem makes
e a side axis of A. The force balance at A is

\[
                    \alpha e+\mu n_B+\nu n_D=0,
                   \qquad \alpha,\mu,\nu>0,
\tag{14}
\]

where n_B,n_D are its outward normals toward B,D. Assume both
are side axes of A. Taking the component perpendicular to e shows
that both must be parallel to e. Indeed one perpendicular axis
cannot be canceled by a parallel one; two perpendicular axes cannot
cancel the nonzero e-component of the leaf force.

A is oblique to U, so e has a nonzero horizontal component.
The two owner signs from Section 5,

\[
                     n_B\cdot e_x\le0,
                     \qquad n_D\cdot e_x\le0,
\]

therefore make the two parallel normals point in the same direction.
Equation (14) fixes that direction as

\[
                             n_B=n_D=-e.
\tag{15}
\]

Their two actual applications consequently belong to the same
minimum-e side of A. The B application has height at most Y;
the D application has height at least Y+1. Their vertical difference
is at least one, while the entire A side has length one. Equality
is forced throughout: the two points are its endpoints, and the
side is vertical. That would make A parallel to U, contradicting
the already excluded parallel-bypass case.

**Corollary 7.1.** The entire D-leaf alternative in which A owns
both A-tip normals is excluded at the canonical minimizer, with
every B/D circle mask and every channel mean retained.

There is also a useful complete necessary sign statement for the
remaining D-leaf alternatives. If even one A-owned cycle normal
were parallel to the D-leaf axis e, (14) would make the other normal
parallel to e too. Both would then be A side axes, just excluded.
Consequently every surviving A-owned cycle normal is perpendicular
to the D-leaf axis. This assertion concerns the actual side normal;
it makes no selection or ownership assumption about the other edge.

The shared-side exclusion and the D-leaf consequence do not remove
the remaining singleton A-owned/B-owned transitions, a physical
two-circle-corner mask, the all-three-loaded C4 domain, or the four
arbitrary completion squares. The full C4 and parent cell therefore
remain open.
