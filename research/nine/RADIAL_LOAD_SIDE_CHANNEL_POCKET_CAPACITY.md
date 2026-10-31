# A width-one channel incident to a physical radial load has exterior capacity at most one

**Status: complete whole-domain hand geometric theorem; author, root
and separate independent full source, geometry and exact audits passed.**

Work throughout \(79/40\le R\le\sqrt{1105}/16\), with \(\rho=5/4\).
The entire positive component is a simple cycle with at least three
loaded bodies. X and Y are consecutive loaded bodies joined by one
actual unloaded degree-two **side-normal** transmitter U, of reserve
one. At least one endpoint S has two physical circle corners. Keep
both original nonnegative corner weights, their positive total,
every actual application mean, and every physical square.

**Theorem.** The entire actual exterior X-U-Y pocket contains at most
one additional physical unit square. If both endpoints are physically
radial, that whole pocket is empty. The exact radial/radial center-gap
identity also excludes every all-side, all-radial alternating positive
cycle, including C6 and C8.
The theorem uses the actual cap and cyclic-order conclusions of
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. Other central regions and other
C6 width/mask families retain their separate obligations.

## 1. Complete radial endpoint support cover

In S's actual positively oriented radial frame,
\[
S=[d,d+1]e+[-1/2,1/2]f,\qquad f=Je,\qquad
K=d+1=\sqrt{R^2-1/4}.
\]
The whole window gives \(9/10<d<61/60\), \(|d-1|<1/10\), and
\(R-\sqrt2>14/25\). Let g be its original unit normal toward U,
and p its original application. Reserve one gives the actual
application on the next loaded body exactly \(p+g\); no transverse
mean changes.

An outer circle vertex cannot be shared. The outer radial face
cannot support a unit neighbor because its support K exceeds R-1
and a unit has width at least one. Thus neither a positive outward
radial component nor the outer radial axis remains.

The inner radial axis \(g=-e\) is impossible too. Its unchanged
point would be \(p=de+yf\), \(|y|\le1/2\), making the next loaded
application \((d-1)e+yf\). Its squared norm is strictly less than
\[
1/100+1/4=13/50<(14/25)^2.
\]
Every point of the next boundary unit has norm at least
\(R-\sqrt2\), by its diameter and actual circle corner.
This is a contradiction. The argument requires neither parallel
forces at S nor any assumption on its separate corner weights.

A tangential radial axis \(g=\pm f\) is impossible as well. Its
actual support is \(p\cdot g=1/2\). Reserve one puts the next
loaded application's g-coordinate at \(3/2\). That entire next
unit lies in \(g\cdot x\ge3/2\), so its width at least one forces
a point of g-projection at least \(5/2>R\), a contradiction.

Thus the entire remaining radial support is a strict inner vertex
\[
p=de\pm f/2,\qquad g=-ce\pm sf,\qquad
c,s>0,\quad c^2+s^2=1.
\]
The original application is in the strict relative interior of U's
side. A side endpoint would be a point-only vertex/vertex contact
with a selected side-axis normal, contrary to the existing strict
point-normal convention. No new normal or mean is chosen.

## 2. Every such actual channel cap has height greater than one half

The proper force polygon supplies its positive actual height h,
with the origin on the inward side. At an upper strict inner
vertex its outward normal is \(se+cf\), and at the lower vertex
it is \(se-cf\).
In either case
\[
h=ds+c/2>(s+c)/2\ge1/2.
\]
The determinant check is
\(\det(de+f/2,-ce+sf)=ds+c/2>0\), with both signs reversed below.
Thus these are the actual positive-height exterior sides.

The physical channel-cap theorem puts every whole pocket extra E
in \(\{N\cdot x\ge h\}\). Its half-width is at least \(1/2\), so
\[
|c_E|\ge N\cdot c_E\ge h+1/2>1.
\]
ANNULAR_CENTER_ARC_BUDGET.md gives an open \(\rho\)-circle arc
inside \(E^\circ\) of length strictly greater than \(\pi/4\).
E need not touch the boundary or carry any force.

## 3. One radial endpoint improves the whole center-angle bound

The endpoint center norms satisfy
\[
r_S=K-1/2>7/5,\qquad r_Y>5/4.
\]
The former uses \(K>19/10\), proved by squaring at \(R=79/40\);
the latter is the universal boundary-center bound. The actual
channel application distance is one, and each center is at distance
at most \(1/\sqrt2\) from its application. Thus
\[
|c_S-c_Y|\le1+\sqrt2.
\]
Normalized channel coordinates give opposite strict horizontal center
signs and nonnegative heights, so the actual outward consecutive
center gap \(\gamma\) belongs to \((0,\pi]\).
If \(\gamma\ge\arccos(-2/3)\), the cosine law gives
\[
\begin{split}
|c_S-c_Y|^2
&\ge r_S^2+r_Y^2+(4/3)r_Sr_Y\\
&>(7/5)^2+(5/4)^2+(4/3)(7/5)(5/4)\\
&=7027/1200>35/6>(1+\sqrt2)^2.
\end{split}
\]
Here \(7027/1200-35/6=9/400>0\), and \(\sqrt2<17/12\)
gives the last comparison. This contradicts the actual center-distance
upper bound. Therefore \(\gamma<\arccos(-2/3)\).

The exact convenient angle comparison is
\(\arccos(-2/3)<53\pi/72=132.5^\circ\).
Use \(\pi>25/8\) from ANNULAR_CENTER_ARC_AT_23_25.md and
\[
z=425/576<17\pi/72<\pi/2.
\]
Monotonicity and the signed sine Taylor remainder give
\[
\sin(17\pi/72)>\sin z>z-z^3/6
=2/3+4851271/1146617856>2/3.
\]
Taking cosine at \(\pi/2+17\pi/72\) proves the angle comparison.
No rounded angle is a premise.

## 4. The radial endpoint blocks its entire larger centered arc

Put \(\beta=\arcsin(2/5)\). The entire closed \(\rho\)-circle
intersection of S is exactly the centered arc \([-\beta,\beta]\)
in its radial frame. Its tangential condition is
\(|\rho\sin\theta|\le1/2\), and throughout this arc
\[
d<61/60<\sqrt{21}/4\le\rho\cos\theta\le\rho<K.
\]
Thus all radial-face inequalities are strict; the two angular
endpoints lie on the tangential sides. Other angles in the positive
radial half-plane violate the tangential condition, and S has no
points in the opposite half-plane.

Every point of this **closed** arc is blocked for another unit's
open interior. If a point of a closed square lay in another square's
open interior, a small open ball there would meet the first square's
open interior. This excludes the angular endpoints too.

Also \(\beta>\pi/8\), since \(\sin(\pi/8)<2/5\); its exact squared
comparison is \(2-\sqrt2<16/25\). The other boundary endpoint blocks
a closed centered arc of half-width \(\pi/9\) by CENTERED_INNER_ARC.md,
whether it has one or two physical circle corners and whether one
individual weight vanishes.

## 5. The whole actual pocket routes into the same free inner-circle interval

Normalize the original applications and supports as
\[
P_X=(l,h),\quad P_Y=(l+1,h),\quad
X\subset\{x\le l\},\quad Y\subset\{x\ge l+1\}.
\]
The endpoint-center theorem gives
\[
0\le\phi_Y<\pi/2<\phi_X\le\pi,\qquad
\gamma=\phi_X-\phi_Y.
\]
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md identifies the pocket as the
bounded side of the occupied crosscut
\(z_X-P_X-P_Y-z_Y\) and its outward outer-circle arc.
The entire Jordan curve is above \(h>1/2\).

Both boundary endpoints meet the \(\rho\) circle in single closed
arcs containing their radial-center points in their relative
interiors, by the explicit closed-interval formulas of
ANNULAR_CENTER_ARC_AT_23_25.md. Those radial points are in the open
endpoint units, so their x coordinates are strictly below l and
strictly above l+1 respectively. Monotonicity of cosine on the
upper semicircle shows that the middle crosscut segment meets that
semicircle only at angles between \(\phi_Y\) and \(\phi_X\).
The other crosscut pieces lie in the closed endpoint units and
meet the \(\rho\) circle only in their closed arcs.

Each endpoint arc restricted to the upper semicircle remains a single
interval containing its center angle, even if its full arc extends
below the horizontal axis. Indeed
\[
c\cdot p\ge |c|^2-|c|/\sqrt2>0
\]
on each boundary unit, so the whole arc is in the open angular
semicircle about its center. With the center angles in opposite
upper quadrants, the claimed upper restrictions are intervals.
Neither can pass across the other center angle, which is inside
the other open unit.

Take any \(\rho\)-circle point in \(E^\circ\). It is above h and
outside both closed endpoint units. If its angle is below \(\phi_Y\),
follow the upper circle to angle zero. That path avoids both
endpoint intervals, the middle crosscut segment, and the outer-circle
arc, because \(R>\rho\). The positive horizontal ray then escapes
to infinity below h, contradicting the bounded pocket label.
An angle above \(\phi_X\) is excluded by the path to \(\pi\) and
the negative ray. If \(\phi_Y=0\) or \(\phi_X=\pi\), the
corresponding case is empty.

Every inner-circle point in \(E^\circ\) is therefore between the two
endpoint center directions. Avoiding their two closed blocked arcs
confines all such points to **one** intervening free interval of
length at most
\[
\gamma-\beta-\pi/9.
\]
The radial endpoint may be either X or Y; the same sum applies.
No sector containment of E or its center was assumed.

The physical cap theorem's compact-interior homotopy argument
retains this conclusion at shared junctions and original mean
endpoints. Additional zero-weight contacts may subdivide the pocket
but cannot move an extra's connected interior across the occupied
crosscut or change the free circle interval just proved.

## 6. Exact capacity and scope

The exact inequalities give
\[
\gamma-\beta-\pi/9
<53\pi/72-\pi/8-\pi/9=\pi/2.
\]
Every whole pocket extra contains an open inner-circle arc longer
than \(\pi/4\). Two interior-disjoint extras would give disjoint
arcs with combined length greater than \(\pi/2\) inside one interval
of length less than \(\pi/2\), which is impossible.
The entire actual pocket has capacity at most one.

All physical circle masks, both zero endpoints of the radial body's
individual corner weights, original side means, exact unloaded
transmitter degree, and all other squares remain. No radial motion,
replacement packing, new normal, sampled angle boxes, Lean
compilation or CI is used.


## 7. A channel between two physical radial loads has an empty exterior pocket

Suppose both loaded endpoints are radial. Their unchanged applications
\(P_X,P_Y\) are strict inner vertices, so both have norm
\[
r_0=\sqrt{d^2+1/4},\qquad |P_Y-P_X|=1.
\]
Their common channel line therefore has origin distance
\(\sqrt{r_0^2-1/4}=d\); the force polygon identifies the actual
outward height as \(+d\).

By END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1, every contained
unit wholly beyond this line must be the unique radial square
\[
E=[d,d+1]N+[-1/2,1/2]JN.
\]
Its inner side is exactly \(P_XP_Y\): both are length-one chords
at height d with endpoint norm \(r_0\).

But the actual transmitter U is a side-normal unit whose two
applications are in strict relative interiors of its opposite sides.
The midpoint of \(P_XP_Y\) is consequently in \(U^\circ\), and
U has open points on both sides of the channel line near it.
E has open interior immediately on the outward side, so U and E
overlap. This contradicts physical disjointness.

Thus the whole actual radial/radial exterior pocket is empty,
with every original transverse application mean retained.

## 8. The exact radial/radial outward center gap

Put \(\phi=\arctan(1/(2d))\), and normalize the actual applications
as \((-1/2,d),(1/2,d)\), with the outward direction upward.
The left application's argument is \(\pi/2+\phi\).
Since it is an inner radial vertex, its radial-axis direction is
either \(\pi/2\) or \(\pi/2+2\phi\). The first would put that
vertex on the wrong tangential support for the outgoing \(+x\)
channel; it would also make the channel normal a tangential radial
axis, already excluded in Section 1. Thus its actual center direction
is \(\pi/2+2\phi\). The right center direction is
\(\pi/2-2\phi\), by reflection.

The complete physical channel-order theorem identifies the actual
consecutive outward center gap as
\[
\gamma=4\phi.
\]
This uses actual support features and physical cyclic order.
No corner weights, axes or radial concurrence are adjusted.

## 9. The entire all-side/all-radial alternating C6 is excluded

In an alternating C6 with three radial loaded bodies and three
side-normal transmitters, all three consecutive center gaps equal
\(4\phi\). Their physical cyclic order makes their sum \(2\pi\).
Therefore \(12\phi=2\pi\), which gives \(d=\sqrt3/2\).

This contradicts \(d>9/10>\sqrt3/2\). Equivalently, each of
the three gaps is strictly less than \(2\pi/3\).

The whole all-side/all-three-physical-radial alternating C6 is
therefore impossible, including both zero endpoints of every original
individual corner-weight pair. No unique-corner turning theorem,
new normal, motion or equality-limit argument enters this closure.


## 10. Uniform all-radial alternating-cycle exclusion, including C8

The same identity excludes a larger whole family. Suppose every
loaded body of the actual simple positive cycle is physically
radial, and exactly one actual unloaded side-normal degree-two
transmitter lies between each consecutive pair. Let k be the number
of loaded bodies; by hypothesis \(k\ge3\). Every actual outward
consecutive center gap is the same
\[
\gamma=4\arctan(1/(2d)).
\]
The complete physical cyclic order gives \(k\gamma=2\pi\).

Over the whole radius window,
\[
\frac{\pi}{2}<\gamma<\frac{2\pi}{3}.
\]
The upper inequality is Section 9's comparison
\(d>9/10>\sqrt3/2\). For the lower, use
\[
d<61/60<6/5,\qquad
\tan\phi=1/(2d)>5/12>\sqrt2-1=\tan(\pi/8),
\]
where \(\sqrt2<17/12\) has strict squared margin \(1/144\).
Thus \(\phi>\pi/8\), giving the lower bound.

For \(k=3\), the sum \(k\gamma\) is strictly smaller than \(2\pi\).
For every \(k\ge4\), it is strictly larger. Both contradict the
actual cyclic sum. No integer k is possible.

This excludes the entire stated alternating radial family, including
the C6/SSS and C8/SSSS cases in the nine-square problem. The C8
application retains its actual one completion square. Every original
individual circle-weight endpoint, physical radial mask, true degree,
transverse mean and all other squares remain. A cycle with a unique
loaded corner, a diagonal transmitter, a direct loaded/loaded edge
or a different channel length does not meet this uniform premise
and retains its own obligations.
