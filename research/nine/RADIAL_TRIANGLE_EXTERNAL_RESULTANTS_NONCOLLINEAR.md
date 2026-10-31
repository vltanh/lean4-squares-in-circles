# A physical triangle's radial external resultants cannot be collinear

Date: October 26, 2026.
**Status: accepted complete theorem after full-source independent review in REVIEW_RADIAL_TRIANGLE_NONCOLLINEAR_GLOBAL_2026_10_26.md.** No ledger or original label is changed here.

## 1. Full local scope

Let three actual interior-disjoint unit squares A,B,C touch pairwise,
with a positive physical force on each of the three triangle edges.
Keep each actual common application and selected common normal, including
every shared-side mean and endpoint. At each body retain the sum F_i of
all its other forces. Assume the origin moment of that entire external
force system is zero and the body's full force and moment equations hold.
The external system need not be one leaf or one circle load. It may
include both an actual circle load and any number of radial bridges.

**Theorem.** All three F_i are nonzero, and their directions are
noncollinear. Consequently the common-moment theorem
RADIAL_TRIANGLE_CONCURRENCE.md applies whenever the triangle's common
directed contact moment is nonzero, without a separate boundary-leaf
argument for noncollinearity.

This is a local theorem about the full actual triangle equations. It
does not assign a degree-two equation to a root with additional forces,
select a new force or normal, or assert that a concurrence is inside
a body. No radius, circle mask, canonical-pose or support-minimization
premise is needed beyond those of the actual compatible force system.

Orient the triangle A to B to C to A. Write its directed positive
edge-force vectors as f_AB, f_BC, f_CA. The full equations are

    F_A = f_CA-f_AB,
    F_B = f_AB-f_BC,
    F_C = f_BC-f_CA.                                      (1)

In particular F_A+F_B+F_C=0. Each edge vector is nonzero.

We use exactly two purely physical facts for three pairwise-touching
unit squares, proved with full feature and mean cover in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section2, and recalled in
RADIAL_TRIANGLE_CONCURRENCE.md, Section1:

* Two parallel outward normals at one body must have the same sign.
  Opposite support faces would separate its two touching neighbors by
  a positive projection width.
* If the two outward normal lines at one body are nonparallel and
  concur at q, their actual ports have the form P=q+a*n and Q=q+b*m,
  with a,b>=0.

## 2. Nonzero external resultants and the parallel alternative

If F_A=0, equation (1) gives f_CA=f_AB. The two actual outward
cycle forces at A are then f_AB and -f_CA, which are opposite.
The first physical fact excludes this. The same argument applies
at B and C, so every F_i is nonzero.

Suppose for contradiction that all F_i are collinear on an axis e.
If a cycle pair at A is parallel, its two outward normals agree
in sign by the first physical fact. Their nonzero sum is -F_A,
so both edge vectors at A are parallel to e. Equation (1) then
makes the remaining edge vector parallel to e as well.

But all three directed edge vectors cannot be collinear. Indeed,
write their signs along e as s_AB,s_BC,s_CA in {+1,-1}. The
same-outward-sign requirement at the three bodies gives

    s_AB=-s_CA,       s_BC=-s_AB,       s_CA=-s_BC,

which is inconsistent. Thus under the supposed collinearity of
the F_i, every cycle pair must be nonparallel.

## 3. Proper ports force all three concurrences and contacts to coincide

Let q_A,q_B,q_C be the three genuine nonparallel concurrences.
Taking the full moment equation about q_i, the two cycle forces
contribute zero because their actual lines pass through q_i.
The external system has origin moment zero, so its moment about
q_i is -det(q_i,F_i). Therefore

    det(q_i,F_i)=0.                                      (2)

Because F_i is nonzero and parallel to e, each q_i lies on the
same line through the origin parallel to e. This permits positive,
negative and zero scalar multiples; no sign is assumed.

At an actual edge, the proper-port fact at its two endpoints gives

    q_B-q_A = lambda_AB*f_AB,       lambda_AB>=0,          (3)

and the corresponding cyclic relations. Explicitly lambda_AB is
the sum of the two nonnegative proper lengths divided by the
positive force magnitude on AB.

If two concurrence points differed, their joining edge in the
triangle would have lambda>0. Equation (3) would make that edge
force parallel to e. Since all F_i are parallel to e, equation
(1) would make all three edge forces parallel to e. Section2 has
already excluded that. Hence

    q_A=q_B=q_C=q.                                      (4)

Every lambda in (3) is now zero because the corresponding edge
force is nonzero. Its two proper lengths are separately zero,
since they are nonnegative. Thus the actual common application
of each physical triangle edge is exactly q. All three squares
contain that point, and both cycle normals at each are normals
of that square at q.

## 4. Two actual tangent cones cannot occupy the same strict half-plane

At each body its two cycle normals at q are nonparallel. Therefore
q is a vertex of that square: a side-interior point has only one
outward normal ray. Its outward normal cone has angle pi/2.
The actual sum of the two positive cycle forces is -F_i.
A positive combination of two nonparallel vectors of this cone
lies in its angular interior. Thus -F_i is a strictly interior
outward normal direction at q.

Equivalently, both inward side rays of the square at q have
strictly positive scalar product with F_i. Its entire right-angle
tangent cone, except its vertex, lies in the open half-plane

    {v : F_i.v>0}.                                      (5)

There are three nonzero collinear F_i summing to zero. At least
two have the same sign along e. Their two square tangent cones
therefore lie strictly in the same open half-plane through q.
Both angular cones have width exactly pi/2, while their interiors
must be disjoint because the two square interiors are disjoint.
This is impossible: two closed angular intervals of length pi/2
with disjoint interiors have total angular length pi, whereas
their union, strictly inside one open semicircle and bounded away
from its endpoints, has length strictly less than pi.

Equivalently, the positive angular margins of both cones from
the half-plane boundary leave too little angular room for two
right angles. This is an actual local overlap contradiction;
no body is moved and no contact is perturbed.

The supposed collinearity is impossible, proving the theorem.

## 5. Use with a potentially loaded bridge-attached triangle root

If a triangle vertex A has both its own circle load and a radial
bridge branch, retain both in F_A. Every circle atom and every
radial bridge has zero origin moment, so the theorem applies to
that full aggregate. The other two resultants are also nonzero
and noncollinear by the theorem, provided all their original
external forces have zero origin moment.

When the common triangle moment H is nonzero, the complete
RADIAL_TRIANGLE_CONCURRENCE.md theorem now gives a positive
multiple of F_i at every nonparallel root. If B is known to be
clear with one genuine leaf branch, its concurrence is therefore
on that original leaf's positive ray. No analogous leaf-only
direction is assigned to A when A carries its own circle load.

For H=0 this source proves only nonzero noncollinear resultants;
the separate zero-moment geometry in an application is still
required. At a parallel root no fictitious concurrence is used.

No Lean compilation, CI, numerical sampling or scalar certificate
was used. No entire global radius or equality conclusion follows
from this local structural theorem alone.
