# Full independent review: three near neighbors of a boundary unit

Date: October 27, 2026.
Reviewer: hexagon, independently of author triangle_bridges.

**Verdict: ACCEPTED in full, no correction requested.** I read all four
sections and independently derived the whole fixed-lens proof and its
literal original C1.4.b3 attachment:

    BOUNDARY_UNIT_THREE_NEAR_NEIGHBORS_FRESH_EXCLUSION.md
    ba49bbf678dfecdadbd120328de745253c8e5a45a5f7635d7044fc784179f156.

This is a full new mathematical audit, not an inference from the lost
older lens theorem or its former hash.

## 1. Actual center reduction, including all weak contact endpoints

I checked the actual square circumradius and open-incircle estimates.
Every unit meeting the closed D_(1/60) has center norm at most
1/sqrt(2)+1/60<29/40. Every physical boundary center at R>=79/40
has norm greater than63/50, regardless of its physical mask or circle
weights. The exact rational reserves are1/576 and1/1400.

After a common rotation, write the actual boundary center as(q,0),
q>63/50. For every candidate near center with x<=29/40<63/50,
the derivative of its squared distance to(q,0) with respect to q
is strictly positive. Thus replacing q by the fixed63/50 enlarges
the whole contact domain, with no shift of any actual square.

Actual physical contact supplies center distance at most sqrt(2).
Distinct near units have center distance at least one. It is therefore
enough to bound the diameter of each CLOSED lens half by a constant
strictly below one. Axis centers do not evade the two-half pigeonhole:
they can be assigned to either containing closed half.

## 2. Both curved arcs and the entire convex half-lens

I independently computed the intersection coordinate
x0=647/14400 and checked0<x0<a and0<b-x0<sqrt(2).
The upper boundary is exactly the axis segment B--A and the two
stated short circle arcs.

Same-arc distances are bounded by their endpoint chords. For cross
arcs, I independently differentiated
Q_x*cos(theta)+Q_y*sin(theta). It is nondecreasing when Q_x<=0;
when Q_x>=0 it is concave on the whole first-quadrant interval.
Thus the farthest point on the O-centered arc is A or Z.

The distance from the other circle arc to A increases with its
actual angle because b>a. Its distance to Z is bounded by its
short-arc chord to B. Convexity of squared distance handles the
axis segment and then the full convex lens half. This proves the
complete maximum-of-three-endpoint-chords bound without replacing
the curved lens by an unjustified inscribed triangle.

Every closed arc intersection, horizontal-axis endpoint and actual
contact equality remains in this argument.

## 3. Exact strict diameter calculation

Using exact Fraction arithmetic independently of the source
derivation, I verified all displayed identities:

    (29/40-1/60)^2-1/2=1/576,
    79/40-5/7-63/50=1/1400,
    x0=647/14400,
    1-|A-Z|^2=4003/288000,
    b-x0-6/5=217/14400,
    b-a-1/2=7/200.

The two elementary radical comparisons sqrt(2)>5/4 and
sqrt(2)<3/2 prove the other two chord bounds strictly. Consequently
both whole closed lens halves have diameter below one. Three
actual near centers cannot occur.

The local theorem is force-free, permits arbitrary degrees and
orientations, and needs no upper radius bound. Physical circle
contact, rather than a positive weight at a particular corner,
is exactly its boundary hypothesis.

## 4. Full original diamond attachment and selection scope

I reread NO_UNLOADED_DIAMOND_HUB.md in full, including its compatible
pre-extraction singleton selection and arbitrary-neighbor degree scope.
It needs the actual hub's exact positive degree three, with one of
its neighbors physically touching the other two. It permits arbitrary
extra forces and loads at those three neighbors.

In the displayed diamond, K has exactly H,B,D as neighbors, and
H physically touches B,D. Therefore the selected zero-load K
alternative is excluded by that theorem, so K has positive total
circle load and is physically boundary. The decorated H remains
true degree four, and the decorated tips B,D remain true degree three.

The three actual genuine roots H,B,D each meet D_(1/60) in every
original radius and D/S case by their original radial inward segment.
They are distinct physical units. Thus the force-free local theorem
applies to the unchanged K and these exact three neighbors. The
two other physical squares remain arbitrary and present.

This closes the entire stated original C1.4.b3 attachment, including
all side means, physical masks, zero individual weights and radius
endpoints. It does not close the other three-leaf attachments or
the whole coarse cell. No normal, mean or body equation was altered.
No numerical pose, compilation, CI, remote action or shared-metadata
change was used in this audit.

