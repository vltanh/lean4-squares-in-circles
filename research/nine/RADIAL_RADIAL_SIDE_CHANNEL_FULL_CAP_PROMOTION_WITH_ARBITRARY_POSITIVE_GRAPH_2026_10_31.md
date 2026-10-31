# Every strict radial/radial side channel reaches its cap with an arbitrary positive graph

Date: October 31, 2026 UTC. **Complete geometric hand theorem.**
The whole upward motion is free against every actual square. No simple
positive-cycle hypothesis is required; all original chords, higher
degrees and other components remain. The proof uses one occupied
crosscut made from the two actual radial endpoints and the actual
transmitter, followed by the equality case of the universal unit-square
support cap. No Lean, CI or external computation is used.

## 1. Full local theorem, including every other physical square

Let finitely many actual closed unit squares have disjoint open
interiors in the same disk about O=0, with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    9/10<d<61/60.

Let X,Y be two distinct actual squares having **two physical circle
corners each**. No positivity of the two individual corner coefficients
is assumed. Let U be an original unloaded true-degree-two side
transmitter between X and Y. Keep its entire original two-force and
torque equations, actual normals and application points. Use the same
strict point-normal convention already present in the original common
certificate. No hypothesis is imposed on the true positive degrees,
loads, additional forces or physical contacts of X,Y or any other unit.

Let g be the original channel direction from X towards Y. The full U2
gives the actual applications

    P_Y-P_X=g, |g|=1.

The actual U side ports are strict, as proved in Section 2. In the
orthonormal frame (g,N) constructed there, the actual data are

    P_X=(-1/2,d), P_Y=(1/2,d),
    U(b0)=[-1/2,1/2] x [b0-1/2,b0+1/2],
    d-1/2<b0<d+1/2.                                (1)

**Theorem.** With every other actual square fixed, replace U(b0) by

    U(b)=[-1/2,1/2] x [b-1/2,b+1/2]

for any b in the entire closed interval

    b0<=b<=d+1/2.                                   (2)

The resulting full packing is physically feasible in the same disk.
At the endpoint it is exactly the radial cap square

    U(d+1/2)=[-1/2,1/2] x [d,d+1],                 (3)

with two physical circle corners. Every other unit, including every
completion square and every original positive chord, has remained fixed.

This is a geometric alternative-packing theorem. It does not assign
a positive circle coefficient to U, reselect a normal, or transfer a
secondary minimum to the endpoint packing.

## 2. The exact original radial endpoint chart is local

The required endpoint geometry is independent of any entire-cycle
assumption. For clarity, its complete local entry is recalled here.
A physical two-corner endpoint X has its actual radial form

    X=[d,d+1]*e+[-1/2,1/2]*f, f=Je.

Its original channel support cannot be an outer circle vertex, since
such a vertex cannot be shared by another actual contained unit. Nor
can it be the outer radial face: a neighboring unit has width at least
one and would extend beyond the circle's outer support.

The inner radial axis is impossible as well. If g=-e, its unchanged
application would be P_X=d*e+y*f with |y|<=1/2, and the next actual
boundary endpoint application would be

    P_Y=(d-1)*e+y*f.

The radius window gives |d-1|<1/10, hence

    |P_Y|^2<1/100+1/4=13/50<(14/25)^2.

Every point of Y has norm at least R-sqrt(2)>14/25, because Y has
an actual circle corner and diameter sqrt(2). This is a contradiction.

A tangential radial axis is impossible: its actual support is 1/2,
so the application on the next endpoint has projection 3/2, and that
whole endpoint lies beyond this support. Its width at least one would
force a point of projection at least 5/2>R.

Thus both actual endpoint applications are strict inner radial vertices.
Each has squared norm d^2+1/4. Their mutual distance is one, so their
midpoint has norm d and is perpendicular to g. Define N to point from
O to that midpoint. This gives the original positions P_X,P_Y in (1).

Because each endpoint support is a strict vertex and U's selected
normal is a side axis, its actual U application cannot be a side
endpoint. Such an application would be a vertex/vertex singleton whose
selected normal is an axis of U, contrary to the unchanged strict
point-normal convention. Thus both are in strict U side interiors.
The side length and the full U2 equation give exactly the strict
interval for b0 in (1).

For the physical endpoint orientations put

    phi=atan(1/(2*d)),
    e_X=(-sin(2*phi),cos(2*phi)),
    e_Y=( sin(2*phi),cos(2*phi)).                   (4)

Indeed the argument of P_X is pi/2+phi. Its radial axis can only
be N or e_X, according to which inner corner it is. The first choice
would put the radial square across the required support x<=-1/2.
Therefore its actual radial axis is e_X. The reflected argument at
Y, whose whole support is x>=1/2, gives e_Y. These are statements
about the original physical supports, not a cyclic-order choice.

The original actual circle corners

    Z_X=P_X+e_X,
    Z_Y=P_Y+e_Y                                    (5)

therefore exist. Since d>1/2, 0<phi<pi/4 and cos(2*phi)>0.
Their common height is d+cos(2*phi)>d. Their horizontal coordinates
are respectively less than -1/2 and greater than 1/2.

The same local support exclusions and radial corner identities are
the physical portions of Sections 1, 7 and 8 of
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`. Neither their
local derivation above nor the present theorem imports that source's
separate entire-cycle or force-polygon conclusions.

## 3. An occupied crosscut encloses a geometrically empty cap

Join the four actual points in the order

    Z_X -- P_X -- P_Y -- Z_Y.

The first segment lies in X, the last in Y, and the middle segment
lies in U(b0); its relative interior lies in U(b0)'s open interior
by the strict interval (1). This is a simple occupied crosscut from
the circle to the circle. By (4),(5), its two side branches lie
outside the open strip -1/2<x<1/2, and every point on it has y>=d.

Complete it with the upper outer-circle arc from Z_Y to Z_X. The
result is a simple Jordan curve. Let H be its bounded open region.
The upper arc also has y>d; its two endpoints are symmetric about
the N axis and have the same positive height. Consequently

    closure(H) is contained in {y>=d}.              (6)

Moreover H contains the whole open portion of the central strip
above the application chord and inside the circle:

    -1/2<x<1/2, d<y, x^2+y^2<R^2.                 (7)

These statements can be read directly from vertical sections: in the
central strip the crosscut is the horizontal segment y=d, the two
side branches are outside that strip, and the upper circle arc is
its other boundary. Alternatively the half-plane y<d is connected
to infinity without crossing the Jordan curve, proving (6).

Consider any other actual unit E distinct from X,U,Y. Its open
interior is disjoint from the **closed** squares X,U,Y. To justify
the closed version, an open ball in E meeting a point of one of
those closed squares would meet that square's open interior, since
the closed square is the closure of its interior. This would violate
the original interior disjointness.

Every point of E's open interior also lies strictly inside the
containing disk. Hence E's connected open interior misses the entire
Jordan curve: it misses the occupied crosscut and the outer circle.
If it had even one point in H, it would be wholly in H. Taking
closures would give the whole actual square

    E subset {y>=d}.                                (8)

There is only one possible contained unit satisfying (8). Its center
z obeys |z|<=d+1/2 by the farthest-corner formula. Its vertical
halfwidth h is at least 1/2, so (8) gives

    d+1/2<=d+h<=z_y<=|z|<=d+1/2.

Every inequality is equality. Thus z=(0,d+1/2), h=1/2, and the
actual frame is aligned with the horizontal and vertical axes.
The last claim follows from
(|u_y|+|v_y|)^2=1+2|u_y*v_y|: equality of the halfwidth to
1/2 makes one own vertical component zero and the other one.
Therefore E must be precisely the cap square in (3).

But that square overlaps U(b0) in open interior: both contain
horizontal coordinates in (-1/2,1/2), and their vertical interiors
overlap on the nonempty interval (d,b0+1/2), by (1). This is
impossible. We conclude that **no other actual unit has an open
interior point in H**. In fact no other closed unit meets H, by
the same small-ball argument.

This empty-cap conclusion counts every actual unit. A unit carrying
an additional positive chord is subject to exactly the same physical
argument as a zero-stress completion square. No graph deletion or
planar routing of the rest of the positive graph is needed.

## 4. The entire swept new region lies in that empty cap

For b in (2), the new U(b) is contained in the circle. Its center
height is positive, and its farthest corner has squared norm

    1/4+(b+1/2)^2<=1/4+(d+1)^2=R^2.              (9)

The original endpoint supports x=-1/2 and x=1/2 remain unchanged,
so nonoverlap with X,Y is retained automatically.

Suppose another actual E had overlapping open interior with U(b).
An overlap point cannot belong to the original closed U(b0), by
original interior disjointness and the small-ball argument above.
Since the new lower side never moves downward, such a new overlap
point must have

    -1/2<x<1/2,
    y>b0+1/2>d,
    x^2+y^2<R^2.

By (7) it lies in H. This contradicts the empty-cap conclusion of
Section 3. Hence every actual pair remains interior-disjoint for
every b in the entire interval (2). No local continuation hypothesis
or unexamined first stopping contact is needed: the whole new sweep
was excluded at once using the original occupied crosscut.

At b=d+1/2 formula (3) and (9) give the claimed physical circle
contacts. This proves the theorem, including its closed upper endpoint.

## 5. Endpoint and certificate boundaries

The original lower and upper strict inequalities in (1) are supplied
by the original side-interior ports. No original equality is omitted.
At the final cap, the old unchanged applications become its two inner
corners. The physical packing remains valid, but their old side-axis
normals are now weak vertex normals. No strict-selector theorem is
reapplied there and no new positive circle load is assigned to U.

If a separate geometric caller begins already at b0=d+1/2, the
promotion statement is trivial. The **lower** weak position
b0=d-1/2 cannot be added: the cap square above it need no longer
overlap its open interior and may block an upward motion. This
boundary is excluded by the actual original strict port convention,
not by a generic limiting argument.

The theorem makes no Phi-minimum transfer. All original force and
torque equations are unchanged at strict intermediate positions when
the same original forces are retained, but the present conclusion
requires only physical feasibility and does not use that observation
to extract a new certificate.

## 6. Literal application to chorded six-body cores

In the original D02 core, keep the rim

    V--A--B--N--C--D--V

and its genuine positive AD chord. Suppose the actual side N has
two physically radial endpoints B,C. The theorem applies to the
actual triple B,N,C without changing the true A3/D3 stars or
removing AD. Every other core unit and all three completing squares
stay fixed, while N reaches a physical circle cap. The extra
positive chord, any shared roof, every original weight and all
other physical contacts are retained in the starting packing.

The same conclusion applies inside arbitrary larger positive graphs
with the same local radial/radial side-channel geometry. In particular
it is unnecessary to treat the surrounding positive component as a
simple cycle or to suppress a higher-degree hub to degree two.

This theorem requires **both** endpoint physical two-corner masks.
Merely having positive circle load at B,C is not the RR hypothesis.
Mixed radial/unique or unique/unique side channels remain outside
this promotion result until their own motions are proved.

The geometric promotion by itself does not close the original D02
row or prove a sufficient nine-unit completion count. Pocket dilation
for other faces has its own hypotheses; no b+r+k bound is asserted
by applying an entire-simple-cycle theorem to the chorded core.
No original ledger flag, complete n=9 claim or formal verification
status is changed by this local theorem alone.

## 7. Several original RR units can be promoted successively

Choose any finite set of original RR transmitters satisfying Section 1.
Each is originally physically circle-clear by (1) and (9), whereas
every one of its two radial endpoints is physically circle-touching.
Consequently no chosen transmitter is an original radial endpoint of
another chosen transmitter.

Promote the chosen transmitters one at a time. At each step the next
transmitter and its two original radial endpoints are still in their
unchanged strict local chart (1), and the entire current packing is
physically feasible by the preceding steps. Apply the purely geometric
crosscut and sweep proof of Sections 3--4 to that current packing.
It includes all previously promoted squares among the other actual
units, so it proves feasibility of the entire next move against them.

Previously promoted units may now have weak old corner normals.
This causes no new premise failure: the geometric crosscut/sweep proof
requires strict ports only for the **currently moving** transmitter.
It does not require a globally strict selected certificate in the
current intermediate packing. No fresh force extraction or selector
application is made.

Induction therefore puts every chosen original RR unit at its exact
physical circle cap simultaneously, with every unchosen actual unit
fixed. This proof permits arbitrary original positive chords and
higher degrees throughout, just as the one-body theorem does.

## 8. A force-free count transfers to the original unchanged bodies

For an actual nine-unit packing define the already proved critical
clearance

    h_* = sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1)-1,
    1/5<h_*<29/128.

The complete force-free Theorem D of
`UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md`
states that at most seven actual units have distance at least h_*.
Its equality case and every weak distance endpoint are included.
Every physical circle-touching unit is farther than h_* because its
distance is at least R-sqrt(2)>14/25.

If b counts all original physically boundary units and r chosen RR
transmitters are promoted by Section 7, these are b+r distinct physical
boundary units in the resulting packing. Hence

    b+r<=7.                                         (10)

More generally, let F be any set of original units outside the chosen
RR set whose distances are at least h_*. Those units stayed fixed.
The resulting packing has |F|+r distinct units of distance at least
h_*, so

    |F|+r<=7.                                       (11)

In particular, after promoting all the chosen RR units, the two
critical-near units guaranteed by Theorem D must both lie outside
that set. Their positions were never moved. Therefore the **original
packing already has two distinct critical-near units outside every
chosen original RR set**. This is a statement about their unchanged
physical positions, not a transferred Phi minimum or new circle load.

For the chorded D02 RR caller, promote its actual N while retaining AD.
The original V,B,C are boundary units and therefore far. It follows
that at least two of the original A,D and the three actual completion
units have distance strictly less than h_*. The same conclusion
retains all their true degrees, loads, masks and mutual contacts.
It is a complete necessary completion restriction; its remaining
five-unit near/far alternatives are not declared impossible here.

No exterior-pocket dilation is invoked in (10),(11). To add a count
of pocket occupants reaching the circle, a literal geometric dilation
theorem for those pockets must separately be supplied; the original
entire-simple-cycle theorem is not borrowed for a chorded graph.
