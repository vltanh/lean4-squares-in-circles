# Actual transmitter pockets lie in outward circular caps

**Status: complete hand completion-domain theorem; root and separate
independent full hand audits passed.** Work in the declared window
\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\tag{1}
\]
with the common selected physical certificate. Let the entire positive
component be a simple cycle with at least three loaded bodies.

The contracted force polygon is the one proved in
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. The theorem below uses actual
occupied paths and circle spokes to locate exterior completion squares.
No inclusion of a free region in the concurrence polygon is assumed.

## 1. A complete actual channel barrier

Consider one positive-reserve channel between consecutive loaded bodies
X,Y. It may contain one or two actual unloaded transmitters. Rotate and
label it so that its two endpoint applications are
\[
       P_X=(l,h),\qquad P_Y=(l+w,h),\qquad h>0,\quad w\ge1,
\tag{2}
\]
with the origin below the channel. The actual proper-port and channel
relations give
\[
 X\subset\{x\le l\},\qquad Y\subset\{x\ge l+w\},
\tag{3}
\]
and the complete segment \(P_XP_Y\) is occupied by the actual
transmitter or consecutive transmitters.

Write the endpoint centers as
\[
                 c_X=(x_X,y_X),\qquad c_Y=(x_Y,y_Y).
\]
The full endpoint lemma in FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md,
Sections 1--2, transferred in SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md,
Section 5, gives
\[
 y_X,y_Y\ge0,\qquad
 x_Y-x_X=w+H_X(e_x)+H_Y(e_x)\ge2.
\tag{4}
\]
Every contained-unit center has norm strictly below
\[
                              M=\frac{91}{60}.
\tag{5}
\]
Consequently
\[
                 x_X<-\frac{29}{60},\qquad
                 x_Y>\frac{29}{60}.
\tag{6}
\]
These inequalities use the actual projection widths and retain every
shared-side mean.

Every physical circle corner is less than \(15\) degrees from its
center direction, by FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md,
Section 1. Equations (4)--(6) therefore put **every** circle corner
of X in the open left half-plane and every circle corner of Y in
the open right half-plane. Indeed each center's angle from the
vertical axis on its own side is at least
\[
 \arcsin\frac{29}{91}>15^\circ;
\]
one exact comparison is
\[
       \sin15^\circ<\frac{\pi}{12}<\frac{11}{42}<\frac{29}{91}.
\tag{7}
\]

There is a physical circle corner \(z_X\) of X with height at least h.
If X has one physical circle corner z, its proper concurrence has
the form \(q_X=\tau z\), with \(0<\tau\le1\), and has height h.
Thus \(z_y=h/\tau\ge h\). If X has two physical circle corners,
write it as the radial S square
\[
       [d,d+1]e+[-1/2,1/2]Je,\qquad
                     d=\sqrt{R^2-\frac14}-1.
\]
Its center height is nonnegative by (4), so \(e_y\ge0\).
Its highest vertex is therefore on the outer radial face and is
a physical circle corner. Since \(P_X\) belongs to X, that highest
corner has height at least h. This argument does not use an equal
corner-weight split or an interior radial-S concurrence.

Choose such a highest circle corner \(z_X\), and choose \(z_Y\)
in the same way on Y. We have proved
\[
                 (z_X)_x<0<(z_Y)_x,\qquad
                    (z_X)_y,(z_Y)_y\ge h.
\tag{8}
\]
For a two-corner endpoint these are the circle corners facing the
upper channel arc: on the left body the highest corner is its
clockwise corner, and on the right body it is its counterclockwise
corner. If the center height is zero the same statement follows
by choosing the higher of the two circle corners.

The broken line
\[
                         z_X-P_X-P_Y-z_Y
\tag{9}
\]
is a simple crosscut of the containing disk. Its first and last
segments lie in the actual convex units X,Y. Its middle segment
lies in the actual channel. The two vertical supporting strips
in (3) prevent intersections between the three segments away
from their consecutive endpoints. Every interior point of the
crosscut is strictly inside the circle.

Join (9) to the upper circle arc from \(z_Y\) to \(z_X\).
This is a Jordan curve, entirely in the closed half-plane
\(\{y\ge h\}\). Its bounded region is consequently in that same
half-plane: a bounded Jordan region lies in the convex hull of
its boundary, or equivalently each point below the line can
reach infinity without crossing the curve.

**Channel-cap theorem.** Every additional unit whose open interior
lies in this actual exterior channel region is wholly contained
in
\[
                              D_R\cap\{y\ge h\}.
\tag{10}
\]
In particular its center satisfies
\[
                              (c_T)_y\ge h+\frac12.
\tag{11}
\]
The half-width of an arbitrary oriented unit is at least \(1/2\),
which proves (11) without imposing its frame.

The statement concerns the actual bounded side of the occupied
crosscut (9). It is not an inference from the position of a
concurrence point or from a diagram of a contracted force polygon.

## 2. These are the actual exterior channel regions

Here is the topological identification needed when the local cap
theorem is used in the whole cycle.

The arbitrarily small physical center/contact embedding of
PHYSICAL_BODY_GRAPH_UNCROSSING.md gives a Jordan cycle, with exterior
circle spokes on all loaded bodies. The annular-order argument in
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md shows that the loaded body order
on that curve is its physical circle order. Thus the exterior region
between consecutive loaded bodies X,Y follows their actual intervening
transmitter path and the corresponding circle arc.

That consecutive arc is exactly the upper arc used in Section 1.
The origin is below the positive-height channel; the proper
concurrence polygon follows its other loaded bodies on the
complementary, inward side. Its order agrees with the physical
loaded-body circle order. Equations (8) place the facing endpoint
corners in opposite horizontal half-planes at height at least h,
so their upper connecting arc has precisely the outward orientation.
No third loaded spoke can lie on this arc: it would insert a loaded
body between the two consecutive channel endpoints in that same
cyclic order. Extra physical boundary bodies with zero circle
multiplier may lie there and are retained below.

Within each actual square, its center/contact path can be replaced
by a straight segment between the same physical boundary applications.
This is a homotopy inside that convex occupied square. On the channel,
the replacement is exactly the occupied segment \(P_XP_Y\).
The two endpoint portions can likewise be replaced by
\(z_XP_X\) and \(P_Yz_Y\). Hence the relevant outside region is
the bounded side of (9) together with the upper circle arc used
in Section 1.

This statement remains valid at coincident junctions and shared-side
endpoints. Fix any two points in the open interior of an additional
square and a compact path joining them in that interior. This path
has positive distance from the closed core union. All sufficiently
small junction perturbations and all homotopies inside the occupied
core avoid it. The two points therefore have the same eventual
region label. Connectedness of the extra's open interior then
places its whole interior, and by closure its whole square, in
one of the indicated closed regions. This is the same weak-boundary
argument used for the complete C5 domain.

A physical two-corner body can also bound a small circle cap between
its two corners. Such a cap contains no additional unit: it lies
beyond that body's outer radial face at support height
\(\sqrt{R^2-1/4}=d+1\), whereas a unit in \(D_R\) beyond a support
line has support height at most d. This is the sharp elementary
center/half-width bound in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md,
Section 1. Thus choosing the facing corners in Section 1 omits
no possible extra-square region.

Additional zero-weight physical contacts or extra circle contacts
on an unloaded transmitter may subdivide a channel region. They
cannot allow an extra's connected open interior to cross the
occupied barrier, and every resulting subdivision still satisfies
the same cap inclusion (10).

For a direct contact between consecutive loaded bodies, the complete
exterior-pair-pocket theorem of
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Sections 2--4, already
excludes every additional unit in its outside pocket. Its actual
body and circle-corner premises are present here.

## 3. Full necessary completion cover for the remaining simple C6

CONTACT_RING_HOLE_AREA.md applies to the actual six-body cycle,
including its weak junction limits:
\[
       \operatorname{area}(\text{central free region})
              \le \frac64\cot\frac{\pi}{6}
              =\frac{3\sqrt3}{2}<3.
\tag{12}
\]
It follows that at most two of the three additional unit squares
can lie in the whole bounded central region. This counts their
actual disjoint open interiors, each of area one. Any subdivisions
by additional physical contacts only reduce the available set.

The area source bounds the full set H defined in its Section 1:
the entire bounded interior of the physical ring outside the closed
ring squares, including all its free connected components. It does
not bound only one selected face of a contact-polygon drawing.
Its limiting polygon has winding zero or one; its signed area is
the sum of all winding-one face areas, with no cancellation.
For a coincident-junction limit, fix compact inner portions of all
central extra interiors before taking the arbitrarily small
physical routing. The same winding argument puts all these portions
on the bounded side. The limiting chord lengths still belong to
the six actual squares, and every long-chord inward cap subtraction
in that source is unchanged. Taking the limit gives (12) for their
whole central free union. Thus artificial small routing faces or
additional zero-weight contacts cannot hide another unit-area
component from the count.

The already excluded long-channel and adjacent-zero load families
leave the following entire completion domains:

| Loaded positions in the simple C6 | Exterior channel regions | Complete necessary location of the three extras |
| --- | --- | --- |
| Three alternating loads | Three singleton-transmitter regions | At most two in the central region; every other extra is in one of the three actual caps (10). |
| Four loads, zero vertices at cyclic distance two | Two singleton-transmitter regions | At most two centrally; all others in the two caps. The two direct boundary-pair pockets are empty. |
| Four loads, zero vertices at cyclic distance three | Two singleton-transmitter regions | At most two centrally; all others in the two caps. The two direct boundary-pair pockets are empty. |
| Five loads | One singleton-transmitter region | At most two centrally; at least one extra in its single actual cap. The four direct boundary-pair pockets are empty. |

All channel widths and all actual transverse means remain. For the
alternating row, the entire at-least-two-diagonal class is already
excluded, and the all-side/all-unique/all-singleton class is already
excluded. The table neither reopens those exits nor promotes them
to the remaining shared-side or physical radial masks.

Every remaining simple C6 therefore requires at least one whole
extra square in an explicitly proved outward channel cap, with
its exact actual height h. No numerical control is used in this
deduction, and no extra is assumed to lie in the force polygon.

This is a complete routing and cap theorem, not a capacity theorem
for the caps or a closure of any remaining C6 load orbit. A whole
joint bound on the indicated caps and central region is still needed.
No square is moved, no multiplier or mean is altered, and no larger
chorded component is assigned degree-two equations.
