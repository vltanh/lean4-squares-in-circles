# Strict turns and the complete shared-side normal form for all-unique side C6

Date: October 25, 2026.

**Status: complete hand implication; author and independent root saved-source
and direct-prerequisite review passed.** See REVIEW_STRUCTURAL_INPUTS_2026_10_25.md. No existing gate is reticked and no new
gate is introduced. The remaining three-extra completion problem is not
settled by this source.

Consider the entire alternating six-cycle with three positively loaded
physical-unique-circle-corner units and three unloaded side-normal
transmitters. Retain the common selected physical certificate, every
original shared mean and all three extra units. Work throughout

    79/40 <= R <= sqrt(1105)/16.

The actual loaded concurrences q_i form the strict counterclockwise
triangle containing the origin, and q_i is a positive multiple of its
actual unique circle corner z_i. Write theta_i for its exterior turns.

**Theorem.** Every theta_i is strictly greater than pi/2 and at most
3pi/4. On each loaded unit, the two original applications are distinct
points of one inner side, at least one application is a vertex, and at
most one of its two positive loaded/transmitter interfaces can be a
genuine shared side. Consequently the entire all-unique/shared family
has between one and three genuine shared interfaces, with the original
means and all endpoint cases retained.

## 1. The only possible non-strict turn

The complete local turn proof in Section 1 of
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md uses no diagonal premise in
its unique-corner calculation. It gives

    theta_i <= 3pi/4,
    theta_i=3pi/4 implies q_i=z_i.

The three exterior turns sum to 2pi. Hence theta_i>=pi/2. If one
equals pi/2, relabel it q_0. Then

    theta_0=pi/2, theta_1=theta_2=3pi/4,
    q_1=z_1, q_2=z_2.

The concurrence triangle is right and isosceles, with right angle at
q_0. Put L=|q_2-q_1|. Both other sides have length L/sqrt(2).

At each of q_1,q_2, the true application distances from concurrence are
exactly 1 and sqrt(2). This is also read directly from the complete local
equality cover: at q=z, a 135-degree turn uses an adjacent non-circle
vertex and the opposite inner vertex. The distances are respectively
1 and sqrt(2); the former has an actual loaded side-axis normal. A
variable side mean cannot have any other coordinate at q=z, because its
proper normal line fixes the transverse coordinate to that of z.

Let d_1,d_2 in {1,sqrt(2)} be the distances on the q_1-to-q_2 channel.
Its actual side-transmitter reserve is one, so

    L=d_1+1+d_2.

The other proper distance at each of these two loaded units is the
other member of {1,sqrt(2)}. Therefore the two proper distances alpha,beta
at q_0 are exactly

| (d_1,d_2) | L | (alpha,beta), up to exchange |
| --- | --- | --- |
| (1,1) | 3 | (1/sqrt(2)-1,1/sqrt(2)-1) |
| (1,sqrt(2)) | 2+sqrt(2) | (0,sqrt(2)-1) |
| (sqrt(2),sqrt(2)) | 1+2sqrt(2) | (1/sqrt(2),1/sqrt(2)) |

The first row is impossible because proper distances are nonnegative.
This finite table contains exact lengths, not angle subdivisions or
numerical poses.

## 2. The actual origin fixes the concurrence radius

Because q_1,q_2 are on the original circle, the origin projects to the
midpoint of their chord. The strict origin containment of the concurrence
triangle places the origin between that chord and q_0. The right-isosceles
geometry therefore gives, for either remaining row,

    |q_0| = L/2-sqrt(R^2-L^2/4).                  (1)

The expression is positive. Its square root is the distance from the
origin to the chord; q_0 has distance L/2 from the chord on its inward
side. This argument keeps the original circle origin throughout.

## 3. The row with one zero proper distance

Here alpha=0 and beta=sqrt(2)-1. Thus q_0 itself is one original
application of the loaded unit S_0.

If q_0 were a vertex, its positive radial relation to the unique circle
corner would make it the opposite radial-D vertex. A different vertex
is at distance at least one, greater than beta. A side-interior second
application cannot have its normal parallel to the segment from that
inner vertex: that segment is tangent to any incident side, whereas
the actual normal is perpendicular. Nonincident sides are at distance
at least one. Thus q_0 is not a vertex.

It is consequently in a side interior, with its incident normal a side
axis. The second normal is perpendicular, so is the other side axis.
Its application must be the adjacent inner vertex on the same side as
q_0. Choose inward own axes so the unique circle corner is (a,b),
with a,b>1/2. The zero-length application is

    q_0=(a-1+beta,b-1)=kappa*(a,b),  kappa>0.

The positive circle force is a strict positive combination of the two
inward side normals, so these are the two inner sides at that far
corner. Comparing coordinates gives

    a/b=1-beta=2-sqrt(2),
    |z_0-q_0|=sqrt(7-4sqrt(2)).

Hence

    |q_0|=R-sqrt(7-4sqrt(2)) > 31/40,             (2)

because sqrt(2)>7/5 gives sqrt(7-4sqrt(2))<6/5 and R>=79/40.

But L/2=1+1/sqrt(2)<12/7, and

    6241/1600-(12/7)^2-(49/50)^2
      =2841/1960000 > 0.

Equation (1) gives

    |q_0| < 12/7-49/50 =257/350 <31/40.

The final gap is 57/1400. This contradicts (2), excluding the whole
zero-proper-length row, including an original shared-mean endpoint.

## 4. The row with two equal proper distances

Here alpha=beta=1/sqrt(2), and the two actual outward normals of S_0
are perpendicular.

If either actual normal is a side axis of S_0, so is the perpendicular
one. The applications are on two adjacent inner sides, and q_0 has
distance 1/sqrt(2) from each. In inward own coordinates,

    q_0=z_0-(1-1/sqrt(2))*(e+v).

Its positive radial relation to z_0 forces the two positive coordinates
of z_0 to agree. Therefore

    |q_0|=R-(sqrt(2)-1) >187/120,                 (3)

using sqrt(2)<17/12 and R>=79/40. This includes side-axis contacts
whose original means are side endpoints.

If neither normal is a side axis of S_0, both applications are actual
vertices. Their separation is exactly one, since the two proper rays
are perpendicular with lengths 1/sqrt(2). They are adjacent vertices,
and the unique point inside the square at those distances from both is
the square center. Thus q_0=c_0. Its positive radial relation to z_0
makes S_0 radial D, with a=b. But the complete moment-sign table (6)
in the turn source requires a>b for the lower-left/upper-left pair,
and b>a for the lower-right/lower-left pair. These are precisely its
two adjacent non-circle vertex pairs. Neither condition holds when
a=b. Thus this case contradicts the strictly positive common moment.

Only the side-axis case (3) could remain. For it,
L/2=1/2+sqrt(2)<23/12 and

    6241/1600-11/3-(12/25)^2=427/120000>0,
    (1/2+sqrt(2))^2=9/4+sqrt(2)<11/3.

Equation (1) consequently gives

    |q_0|<23/12-12/25=431/300<187/120.

The final gap is 73/600. This contradicts (3) and excludes the last
row. Therefore no loaded turn can equal pi/2.

## 5. Complete shared-side feature consequence

We have proved pi/2<theta_i<=3pi/4 at all three loaded units.
The full actual-port cover in the turn source now leaves only points
on one inner side, with at least one vertex. Two actual loaded side
axes would give turn at most pi/2 (or forbidden parallel forces), so
at most one positive interface at a loaded unit can be shared.

The two original means cannot coincide. If neither interface is shared,
the two transmitters each contain an open half-disk at the same loaded
vertex, and their support half-planes overlap. If one is shared, its
transmitter contains the ray from that point in the outward normal
direction of the loaded side; this remains true at a physical side
endpoint. The other contact is a loaded vertex in the strict relative
interior of its side transmitter. Its outward loaded normal has
strictly positive scalar product with that first outward direction,
because their angle is pi-theta_i<pi/2. A small perturbation of the ray
into the shared transmitter's open interior is consequently also in
the other transmitter's open half-plane. Their interiors overlap,
again impossible. Thus the means are distinct even at every shared
endpoint.

The directed inner-side chord has length 0<ell_i<=1. It has the exact
original-mean and torque representation in Section 3 of
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md. The all-singleton family is
already excluded by its separate complete theorem. The remaining
all-unique/shared family therefore has one, two or three genuine shared
interfaces, with at most one at each loaded unit. This finite physical
normal form retains the original full angle intervals, forces and
means; it is not a claim that any of its completion cases is closed.

No Lean compilation, CI, numerical pose premise, additional normal
selection or remote write is used in this proof.
