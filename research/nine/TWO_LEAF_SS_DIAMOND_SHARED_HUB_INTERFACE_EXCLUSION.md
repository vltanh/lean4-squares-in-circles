# Two S leaves exclude the whole shared-side hub interface of a diamond

Date: October 27, 2026.

Full root review: REVIEW_THREE_BRIDGE_CELL_SS_DIAMOND_AND_ADJACENT_C4_ROOT_2026_10_27.md.
Separate full-source/scope review: REVIEW_SS_DIAMOND_SHARED_HUB_INTERFACE_MIXED_BLOCKS_2026_10_27.md.
The reviews pin the mathematical source before this acceptance-only header edit.

**Status: accepted complete whole-interface hand theorem.** This source does not close an entire
original leaf-type gate. Its explicit remaining interfaces are recorded
at the end.

Keep all nine original physical units and the common compatible
selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The actual positive diamond has hubs H,K and tips B,C, with edges

    HK, HB, HC, KB, KC.

There is one genuine radial S leaf at each of H and K. The actual
hubs therefore have true positive degree four. B,C have true degree
two and are loaded, since an unloaded degree-two unit cannot have
two physically touching neighbors. The genuine leaf roots H,K are
physically circle-clear. Their full equations, all original normals,
positive magnitudes, physical corner masks, individual zero weights
and actual common application means are retained. The two leaves
and all three arbitrary completion units remain in place.

**Theorem.** The original HK contact cannot be a positive-length
shared side. More generally, the selected actual HK normal cannot be
an owned side axis of both hubs: the strict point-contact convention
would then force the contact to have positive length, reducing to
the first statement.

No degree-three equation is assigned to either hub.

## 1. A full corner cap for any unit resting on one of two adjacent sides

Put J=(h,a). Suppose a unit T lies in y>=a, has a point (p,a) with
p<=h, and has a point with first coordinate at least h. Then

    T is contained in the closed ball of radius
    phi=(1+sqrt(5))/2 about J.                         (1)

This includes a whole side at y=a and every original contact mean.

If T is aligned with the horizontal line, its bottom side contains
J: its left endpoint is at most p<=h and its right endpoint is at
least h. Its coordinate differences from J have absolute values at
most one, so its radius about J is at most sqrt(2)<phi.

Otherwise its actual minimum-y point is a vertex P=(p,a), and its
complete unchanged chart is

    T=P+[0,1](c,s)+[0,1](-s,c),
    c,s>0, c^2+s^2=1.

Its rightmost point has coordinate p+c. Hence eta=p-h belongs to
[-c,0]. Every vertex's squared norm relative to J is convex as a
function of eta, so it suffices to inspect eta=-c and eta=0.
At eta=0 all four values are at most two. At eta=-c the vertices
are

    (-c,0), (0,s), (-c-s,c), (-s,c+s).

The last two squared norms are 1+c^2+2cs and 1+s^2+2cs. Both
are at most 1+phi=phi^2. For example the exact identity

    phi-c^2-2cs=phi*(s-c/phi)^2 >= 0

uses c^2+s^2=1 and phi-1/phi=1; interchange c,s for the other
bound. Convexity of the square and of the containing ball proves
(1) for the full unit, not only its vertices. Reflection gives
the corresponding lower-side cap.

## 2. The two ends of a genuine shared hub side

Suppose HK has positive shared length. Rotate and translate only
for the following geometric argument, writing

    H=[h-1,h] times [a-1,a],
    K=[h,h+1] times [b-1,b].

Their shared interval on x=h has endpoints

    ell=max(a-1,b-1),       u=min(a,b),       ell<u.

Every common physical neighbor T of H and K has a nonempty section
on x=h: a segment joining an H contact to a K contact crosses that
line. It cannot contain any (h,y) with ell<y<u. Such a point has
a neighborhood covered by H and K, and any unit containing it has
interior points entering int H or int K. Its section on x=h is an
interval by convexity. Therefore every common neighbor is entirely
of one of the two section types:

    upper: every point of T on x=h has y>=u;
    lower: every point of T on x=h has y<=ell.          (2)

The two alternatives are disjoint, including endpoint contacts.

For an upper neighbor, suppose a=u<=b, so H is the lower-top hub.
The actual HK normal at H is east. The complete physical triangle
owned-normal theorem, applied to HKT, makes the actual H-to-T
normal have nonnegative first component. Its possible H features
are therefore the two horizontal faces, the right face, and the
two right vertices. A downward normal puts all T below a-1 and
cannot satisfy the upper section condition. A strict lower-right
port itself lies at height a-1<u on x=h, also impossible. An east
normal has its actual port on x=h, so the upper condition forces
that port to be J=(h,u). A strict upper-right normal likewise has
its port at J. An upward normal puts all T in y>=u directly.

At J in the remaining cases, H occupies the lower-left quadrant
locally and K occupies either the right half-plane or the lower-right
quadrant. Thus their union covers a lower half-neighborhood at J.
The interior tangent sector of the distinct unit T cannot enter it.
Both its inward side rays therefore have nonnegative vertical
component, which puts its entire convex square in y>=u. This also
handles an actual side endpoint or a coincident application.

Consequently every upper common neighbor lies wholly above u,
touches the lower-top hub on y=u at a point with x<=h, and meets
x>=h because it touches K. Section 1 gives

    T is contained in the radius-phi ball about (h,u). (3)

If K is the lower-top hub, reflect horizontally. Reflection vertically
gives the full analogous statement for a lower neighbor:

    T is contained in the radius-phi ball about (h,ell).
                                                               (4)

No generic choice of a shared-side mean was made.

## 3. Two positive diamond tips cannot use the same end

We prove this directly, retaining every equal-height and endpoint
case. Suppose B,C are both upper neighbors. Set the lower top to
zero and reflect horizontally if necessary, so

    H=[h-1,h] times [-1,0],
    K=[h,h+1] times [b-1,b],       0<=b<1.

By Section 2 both B and C lie in y>=0, have an actual bottom
support point with first coordinate at most h, and have maximum
first coordinate at least h.

Here is the elementary complete ground-support observation used
for those two unchanged units. Choose such bottom points
P_i=(p_i,0) and order p_1<=p_2. Let M_1 be the first unit's maximum
first coordinate. Then

    p_1<=p_2<=h<=M_1.                                 (5)

Every unit supported on y=0 at P contains the full inward segment
P+[0,1]e_y. At a vertex this follows by resolving e_y into its two
inward side axes, whose components belong to [0,1]; for a side it
is the actual normal segment across the unit.

If p_1<p_2<M_1, the first unit has an interior point on x=p_2
at a height strictly between zero and one. For an aligned first
unit this is immediate. Otherwise its bottom vertex and rightmost
vertex are joined by one actual side, whose latter endpoint has
height in (0,1). A point strictly above that side at x=p_2 is
interior and still below height one. The second unit's actual
inward segment contains that point. A point of the second closed
unit in the first open interior gives open-interior overlap by
interior approximation. Hence this strict case is impossible.

If p_1=p_2, their two unit tangent sectors at that ground point
must both fit in the upper half-plane with disjoint interiors.
Their angles are at least pi/2. The only possible cover consists
of the exact upper-left and upper-right quadrants; a side-interior
sector cannot fit. Thus both units are aligned, one on each side
of the ground point. The left unit's maximum first coordinate
and (5) force that point to have coordinate h.

It remains to treat p_1<p_2=M_1. Equation (5) gives p_2=M_1=h.
The first unit has a point on its right support with height strictly
between zero and one: its rightmost vertex if tilted, or a side
interior if aligned. If the second unit were tilted, the vertical
inward segment above its bottom vertex would be interior at all
heights in (0,1), causing overlap at this point. If it were aligned
and P_2 lay in its bottom-side interior, the same conclusion holds.
Its bottom-right endpoint would put its interior on the same left
side as the first unit, also causing overlap at that right support.
The sole remaining second unit is therefore

    [h,h+1] times [0,1].                              (6)

The equal-ground-point case gives the same right unit. Since (6)
avoids the actual K, we must have b=0. The first unit has maximum
x=h, so its physical K contact is on x=h at height at most zero.
It is wholly above zero. Thus its rightmost support meets the
ground. A tilted ground-supported square has its rightmost vertex
strictly above its bottom vertex, so it cannot do this. The first
unit is exactly

    [h-1,h] times [0,1].                              (7)

Accordingly the only physical same-end limit consists of the four
aligned quadrants at (h,0). The two required positive diamond edges
from each lower hub to the diagonally opposite upper tip are the
two opposite-pair strands at this one four-body junction. They
interlace in the actual cyclic sector order. The common matched
normal selection and junction uncrossing of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` exclude both opposite pairs
being positive in the final physical planar certificate. No new
normal is selected and no side mean is moved in this conclusion.

Thus B,C cannot both use the upper end. Reflection excludes both
using the lower end. The two actual positive tips must use different
ends of the original shared side.

## 4. The full true hub equations point both S leaves away from the side

Return to coordinates about the true circle origin. Keep the shared
chart from Section 2. Each genuine S root meets D_epsilon. The two
opposite physical half-planes at HK consequently give

    -epsilon<=h<=epsilon.                             (8)

At H, the actual east HK normal has nonnegative scalar product with
each H-to-B and H-to-C normal, by the two complete physical triangle
owned-normal implications. The full true H4 force equation therefore
makes its genuine leaf direction e_H satisfy

    (e_H)_x<0.

At K the actual west normal gives, using its complete K4 equation,

    (e_K)_x>0.                                        (9)

The genuine S applications d e_H and d e_K are actual outward
support points of their respective unchanged unit squares. Hence

    d e_H=(h-1,y_H),       d e_K=(h+1,y_K),
    (h-1)^2+y_H^2=d^2=(h+1)^2+y_K^2.                 (10)

These identities are consequences of the real leaf supports and
the full hub equations. No boundary-tip force was omitted.

## 5. The entire low and critical radius domain

If d<1, (10) is immediately impossible: the maximum of (h-1)^2
and (h+1)^2 is (1+|h|)^2>=1.

If d=1, (10) forces

    h=0, y_H=y_K=0, e_H=-e_x, e_K=e_x.

The actual H and K have x intervals [-1,0] and [0,1], and both
unchanged vertical intervals contain zero. Their real radial S
leaves are

    [-2,-1] times [-1/2,1/2],
    [1,2] times [-1/2,1/2].

These four actual units form exactly the full closed-slider cage of
`P_ALL_COMPLETION.md`, at the exact radius R^2=17/4. Its capacity
theorem permits at most four other units. The actual tips B,C and
all three arbitrary completion units are five distinct other units.
This is the complete nine-unit contradiction, with every slider
endpoint retained and with no degree premise on the two middle units.

## 6. At high radius one actual end is too central for a boundary tip

Now d>1, so d=1+epsilon with 0<epsilon<1/60. Equations (8)--(10)
give

    |y_H|, |y_K| <= 2 sqrt(epsilon).                  (11)

Indeed (1+epsilon)^2-(1-epsilon)^2=4 epsilon.
If the H leaf is the west owned axis, (10) forces h=-epsilon.
If the K leaf is the east owned axis, it forces h=epsilon. Both
axis alternatives cannot occur at positive epsilon. Thus at least
one of the two actual S leaves uses a strict opposite-side corner.

Suppose, for example, this is H's upper-left corner. Its top is
a=y_H>0, with a<=2 sqrt(epsilon). The other root K meets
D_epsilon, so its top b is at least -epsilon. Thus the upper end
u=min(a,b) satisfies

    -epsilon<=u<=2 sqrt(epsilon).

If H instead uses its lower-left corner, the lower end obeys the
reflected bound. The same statements hold if the strict corner is
on K. In every case one actual shared-side endpoint J satisfies

    |J|^2 <= epsilon^2+4 epsilon
            <241/3600<16/225,
    |J|<4/15.                                        (12)

Section 3 puts one of the two original positive boundary tips at
this end. Sections 1--2 contain that entire unchanged unit in a
ball of radius phi about J. Since phi<13/8,

    |z| <= |J|+phi
          <4/15+13/8
          =227/120<237/120=79/40<=R

for every point z of that tip. It is physically circle-clear,
contradicting its true loaded degree-two equation. This excludes
the entire high-radius shared-side domain, including the corner
and mean endpoints already covered in Sections 1--3.

## 7. Exact scope and what remains

The proof excludes the complete shared-side HK interface for the
original `M6.B4L2.DIAMOND.TWO_HUBS.LBC.SS` family, across the full
radius window and all three arbitrary completion units. It also
excludes a selected HK normal owned by both hubs, since a singleton
vertex/vertex contact cannot carry an axis endpoint normal under
the retained strict convention.

It does not exclude a singleton HK contact owned by just one hub,
or a strict vertex/vertex HK contact owned by neither. Those entire
interfaces remain, and the original full leaf-type gate and whole
attachment parent remain unchecked on this source alone.

All physical units, true positive degrees, actual force and torque
equations, physical masks, individual zero weights, original normals
and shared-side means remain. There is no numerical pose, modified
normal after extraction, compilation, CI or remote action.
