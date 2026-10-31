# Independent review of whole-pocket capacity two for a radius-two side channel

Date: October 26, 2026.

**Verdict: PASS for the entire stated side-channel domain and the precise remaining-C6 allocation consequence.**

Reviewed in full: RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO.md.

The actual cap/crosscut theorem, its shared-junction and weak-boundary region argument, the full annular closed-intersection formulas, and the centered endpoint arcs were read and independently audited in REVIEW_C6_REMAINING_CAP_0_CAPACITY_ONE_C6_2026_10_26.md. The strengthened quarter-turn source at \(H>1/4\) was separately audited in REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_C6_2026_10_26.md.

## 1. Exact actual center-angle bound

The physical theorem supplies the outward-positive channel frame, the two actual endpoint supports, and the actual consecutive center angles in opposite upper quadrants. Thus the gap in \((0,\pi]\) used in the cosine law is the actual outward gap.

Each application is within \(1/\sqrt2\) of its own actual center. Together with the unchanged reserve-one segment this gives
\[
 |C_X-C_Y|\le1+\sqrt2.
\]
Every original endpoint boundary square has an actual circle corner, so both center norms exceed \(63/50\) throughout the radius window. The two intermediate inequalities have the correct radical directions; the exact final margin is \(1/1400\).

If the outward gap were at least \(5\pi/6\), the cosine-law product coefficient would be positive. The lower center norms can therefore be substituted, giving
\[
 |C_X-C_Y|^2>(2+\sqrt3)(63/50)^2
 >\frac{26}{7}(63/50)^2
 =\frac{35}{6}+\frac{119}{1875}.
\]
The upper estimate \((1+\sqrt2)^2<35/6\) is strict. I independently reconstructed the two displayed rational margins and checked the positive radical-square comparisons. This proves the full actual gap bound \(<150^\circ\), with no force-ratio or orientation restriction.

## 2. Full actual routing and capacity

The actual cap contains each whole additional unit. Its height \(H>1/4\) and radius \(R\le2\) meet the exact strengthened quarter-turn theorem, so every extra has one connected open inner-circle arc of length greater than \(\pi/4\), regardless of its independent orientation or circle load.

The two endpoint units meet the inner circle in connected closed arcs, with their radial-center points in their open interiors. Their actual horizontal supports put those radial points strictly on the two opposite sides of the channel. Hence intersections of the middle channel segment with the upper semicircle lie between the two center angles.

The full endpoint arcs lie in the open angular semicircles about their centers, by \(C\cdot p>0\). Their restrictions to the upper semicircle are therefore intervals. Neither can cross the other endpoint's radial-center point, which belongs to the other open square. These facts justify the path to infinity used to exclude an extra-interior arc point outside the actual consecutive interval.

The other two crosscut segments remain in the closed endpoint units, and the outer arc is at radius \(R>5/4\). The horizontal escape rays lie below the strictly positive channel height. Thus the routing proof applies to the actual occupied crosscut and bounded pocket label; it does not assume sector containment of a square or center.

Each endpoint then blocks its closed centered arc of half-width \(\pi/9\) inside its open interior. All extra arcs lie in the single free interval whose length is
\[
 <5\pi/6-2\pi/9=11\pi/18<3\pi/4.
\]
Three disjoint actual extras would contribute disjoint open arcs with total length greater than \(3\pi/4\), a contradiction. This establishes capacity at most two for the entire actual pocket.

Both physically unique and radial endpoints satisfy the used physical hypotheses. The argument needs no positive individual radial corner weight, selected equal-weight mean, or additional endpoint equation. The cited compact-interior homotopy preserves routing at original shared mean endpoints, coincident junctions and zero-weight contacts.

## 3. Exact remaining-orbit join

The full remaining unique-one-share C6 has \(R<2\) by the independently reviewed common-point theorem. Its actual channel-2 height is \(>1/4\), as independently audited in REVIEW_C6_CHANNEL_2_HEIGHT_C6_2026_10_26.md. Therefore the new whole-pocket theorem gives \(n_2\le2\).

Together with the already accepted empty pocket 1, central capacity one and pocket-0 capacity one, this removes precisely the previous allocation \((n_c,n_0,n_2)=(0,0,3)\). It retains
\[
 (0,1,2),\qquad(1,0,2),\qquad(1,1,1).
\]
The source does not exclude two extras in pocket 2, infer an allocation-free whole C6 contradiction, or close an unrestricted parent gate. All original physical squares remain. No sampled sign, parameter grid, computational certificate, Lean compilation or CI is used.

