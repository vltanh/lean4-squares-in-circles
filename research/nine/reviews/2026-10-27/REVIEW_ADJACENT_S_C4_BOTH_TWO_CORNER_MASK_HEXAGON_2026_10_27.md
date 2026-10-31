# Independent review: both physical two-corner masks in the adjacent-S C4

Reviewer: hexagon. Date: 2026-10-27.

**Disposition: ACCEPTED in full.** This record was reconstructed after the
workspace rollback, following another complete read of the byte-restored
source `ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md`, SHA-256
`e55398acb2f544139113cfa30f93f8dd9dd68656c40d9ba0cfc4c20aeb7f870f`.
The prior review had SHA-256
`5230a7356c29f59bdd9d47dd1153e466b2fb61610be4d39e74108fccb44c0e2c`;
its exact prose was not retained, so this full replacement has a new pin.

## Initial selection and the complete physical mask

The two physical circle corners force the actual radial S rectangle,
independently of individual circle weights. Opposite maximal corners would
force the wrong small radius. For two touching radial S units, the bisector
reflection gives either a positive vertical gap or actual interior overlap
unless tan(theta)=1/(2d). The resulting contact is the actual singleton
(r0,0), with two different frames modulo quarter turns. It cannot be a
four-square junction. The perpendicular bisector normal is strictly inside
the common normal cone, so a1/1000 open neighborhood is a nonempty legitimate
initial restriction on the fixed pose.

There are finitely many such actual pairs. The restriction remains compatible
with the existing finite analytic avoidances because their nonzero functions
cannot vanish on any nonempty open set. These parameters are separate from
the matched opposite forces at four-square junctions. The original uncrossing
changes only those matched opposite pairs and available side-endpoint atoms;
it cannot change this non-four-junction pair. Thinning and aggregation do not
alter a surviving point normal. The argument therefore describes a single
compatible initial certificate, rather than a later reselection.

## Complete local BC feature cover

I rechecked the C2 moment signs. The actual B near point first makes the
C-to-B x component negative. A positive y component would give two strictly
positive C pair moments. A zero y component retains the whole inner-side
mean and the exact equation makes its height negative. Thus every actual
BC point has norm strictly greater than d and at most r0.

None of the four tilted-root B vertices has a norm in that annulus: three
are at or below d and the remaining squared norm exceeds d^2+7/15.
For aligned B, the left vertices are below d. A candidate upper-right port
(d,h),0<h<=1/2, retains both endpoint axes. East duplicates the actual S
leaf. For positive vertical component the complete B3 equation and torque
give alpha(1-h)=mu(s-c), hence s>c. Its real A port and A near point then
give w^2<=epsilon(1+sqrt(2))<1/24, contradicting w>=1/2.
This proves actual B ownership at BC without imposing a degree on A.

The horizontal C-to-B possibility is then exhausted by all actual B own
supports. The only possible support d is the real B leaf direction and
would duplicate C with that leaf. Consequently the contact is exactly
the lower inner C corner, with positive c,s and the unchanged quantities
H=dc-s/2 and D0=ds+c/2.

## Full B3 and full two-corner C cone

The use of the previously accepted force-free shallow tilted-S screen has
its correct broader scope: it allows U>=1-epsilon, including an
origin-interior root, and makes no degree assumption. Its remaining owned
West side has every point below radius d; hence a tilted B must use South,
H=1-V. H<49/60 then gives0<U<1 and0<V<1, so O lies in its actual open
interior. This scope must remain present when restoring that prerequisite;
the older off-origin-only theorem would not suffice.

For aligned B I verified every possible relative leaf axis. The negative
BC axis is excluded by an actual transverse coordinate exceeding one, and
the remaining perpendicular frame has positive D0. The exact full B3
moment is mu(D0-epsilon)=alpha(1-H). The actual A near point yields
(1-H)^2<=2epsilon D0-epsilon^2<=d^2-1<121/3600, hence H>49/60.
No fictitious boundary load or degree-two equation is assigned to A.

At C the original torque is nu(db+a/2)=mu D0, and its complete circle
force is mu(c,s)-nu(-a,b). Its weak lower-cone inequality is exactly
G=bc-(2d+1)as-ac<=0. This uses a nonnegative combination of both actual
corners and permits either individual weight to be zero. At the bisector,
G0=(H-D0)/r0. If H>=49/60, the exact bounds give G0>1/70, while the
declared initial normal neighborhood gives |G-G0|<151/30000<1/70.
The contradiction proves H<49/60 for the full physical mask.

## Original-domain join

The first local application makes B contain the origin openly; reflecting
the same actual C,D pair and interchanging the two true roots makes A
contain it openly. The reversed original normal satisfies the same initial
open restriction. Distinct actual A and B therefore overlap.

All true A3/B3/C2/D2 equations, both genuine leaves, every shared-side mean,
all physical corner masks and individual zero weights survive. The three
other squares remain arbitrary. This closes exactly the both-two-physical-
corner high mask, with no claim about the mixed or unique/unique masks.
No correction is requested. The source and its original mathematical
prerequisites were accepted; file restoration of a prerequisite does not
authorize replacing it by a narrower theorem.
