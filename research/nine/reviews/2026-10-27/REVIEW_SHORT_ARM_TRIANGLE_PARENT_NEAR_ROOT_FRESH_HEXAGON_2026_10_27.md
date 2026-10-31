# Independent full review: a three-force triangle arm parent and a near root

Date: October 27, 2026.
Reviewer: hexagon, independently of author triangle_bridges.

**Result: ACCEPTED in full, with no correction.** I read and independently
derived the complete local theorem and its whole original B9 caller in

    SHORT_ARM_THREE_FORCE_TRIANGLE_PARENT_NEAR_ROOT_FRESH_EXCLUSION.md
    0347f02721a7457aabb90840535f4e6b67bd0a6955a23bb0836fe46a34f437b0.

This review covers every physical feature and original mean in both H
frames, the force-free far-corner obstruction, and both remaining high
arm types. It is not merely an attachment or dependency-availability
review. The conclusion closes the whole original diamond tip-arm /
hub-leaf attachment B9, retaining true H3,C4,K3,D2,X2,L1,M1 and the two
other physical squares. No conclusion for a degree-four arm parent is
inferred.

## 1. Literal hypotheses and the complete physical prerequisites

The local problem has an actual positive H-C-K triangle, exactly three
positive pair forces at H, and its unchanged HX force beta*e at delta*e.
The hypotheses delta<=epsilon and |delta|<r make H physically clear:
every H point has norm at most |delta|+sqrt(2)<R. This is the reason its
circle force is zero. C's actual point in the closed D_epsilon supplies
h_H(n_HC)<=epsilon, since all of C lies beyond that same actual support.
It does not put the HC application itself in the small disk.

I reread in full the geometric proofs in

    UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md
    ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac;

    END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md
    6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb;

    RADIAL_TRIANGLE_CONCURRENCE.md
    5fcd6675510bace9cfe9b2e49c8dc0f7a237c907d7655142cc66401f060d13bf.

Only the physical support facts from their indicated early sections are
imported. In particular, at a minimum-m point of a unit, a direction u
with u.m<0 has strictly less than one positive support span. At a vertex
this follows by resolving u in its two actual inward axes; at a side
interior only the tangential interval can contribute positively. Side
endpoints are covered by the vertex calculation. Applying that fact to
an H-owned axis proves that the other triangle normal is nonobtuse to
it. Applying it to strictly exposed opposite H vertices makes C and K
closed-disjoint, which is impossible. Opposite parallel triangle normals
also separate C and K by the positive width of H; equal-sign parallel
normals remain available until explicitly treated.

These statements require only the three physical contacts. They impose
no circle load, degree, zero external moment, radial concurrence or
force equation on C or K. I checked that none of the later radial or
two-tip conclusions in those prerequisite files is used in this proof.

The complete actual H equations are consequently precisely

    beta*e_x + mu_1*n_1 + mu_2*n_2 = 0,
    mu_1*det(P_1,n_1) + mu_2*det(P_2,n_2) = 0.

The real HX origin moment vanishes at delta*e_x. All three forces and
both original applications are retained. No smaller triangle external
moment is presumed to vanish.

## 2. The new far-corner obstruction is force-free and complete

I checked the full tangent-sector cover at a corner P=(A,B) whose
coordinates exceed 9/10 and whose actual H interior occupies Southwest.
A second square containing P cannot contain it in its interior. At a
vertex of that square, its right-angle tangent sector has disjoint
interior from Southwest. One of its two actual inward axes must lie in
the closed Northeast quadrant. Indeed a connected right-angle sector
avoiding open Southwest cannot have both endpoints outside closed
Northeast. This includes the horizontal and vertical equality axes.

At a side-interior point, the square's entire inward half-plane must
avoid Southwest. Its inward own normal therefore lies in closed
Northeast. In both cases the full unit segment from P in that actual
unit direction lies in the second square. Thus a contained point would
have squared norm strictly greater than

    2*(9/10)^2 + 1 + 2*(9/10) = 221/50.

The exact excess over the allowed upper squared radius 1105/256 is
663/6400>0. The strictness comes from the coordinates of P, not from
discarding a tangent-sector endpoint. Reflections of the whole physical
corner and its occupied quadrant preserve the argument. No force,
boundary load or normal selection is used here.

## 3. The entire tilted H frame

If H does not own East, its original East support is a unique vertex
P=(delta,0), with actual inward axes f=(-a,b), j=(-b,-a), a,b>0.
In these orthonormal coordinates H is exactly

    [-delta*a,1-delta*a] times [-delta*b,1-delta*b].

Both coordinates of its opposite corner exceed 59/60, whether delta is
negative or nonnegative. The new physical lemma excludes every other
unit at that corner, regardless of its force normal or degree.

The actual sum of the two triangle forces is beta*(a,b), strictly
positive in both own components. If one normal is the negative f axis,
the physical nonobtuse fact forces the other f component nonpositive,
contradicting that sum. The negative j case is identical. If one normal
is the positive f axis, the other has nonnegative f component and
strictly positive j component. It is therefore either positive j or a
strict normal at the forbidden opposite corner. The positive j first
case reflects this. The only surviving owned-axis pair would be the two
positive axes, both of whose actual supports exceed 59/60. Whichever
is HC violates its true support bound at the near C.

If neither normal is an H axis, both strictly expose actual vertices.
At the near vertex both components are negative. Pairing it with one
adjacent vertex keeps one summed component negative. Two forces at one
adjacent vertex have that same problem. The two different adjacent
vertices are opposite vertices of H and are forbidden by the physical
triangle lemma. The far corner is already unavailable. This exhausts
all strict-vertex pairs, including equal-point and parallel pairs. No
compatibly selected free normal was replaced by an owned one.

Thus the complete tilted frame is excluded, without an origin-in-H
premise or a sign assumption stronger than delta<=epsilon.

## 4. The entire aligned H frame and both slider endpoints

For an East-owned HX contact the original frame is

    H=[delta-1,delta] times [h-1,h],  0<=h<=1.

The interval for h comes from the actual point (delta,0); no mean or
slider was centered. An H-owned North normal forces the other vertical
component nonnegative, contradicting the zero vertical sum. South is
the reflected case. East contradicts horizontal balance. West makes
the other normal horizontal; it is also West by the same-sign parallel
fact, and the near C support would then be 1-delta>59/60>epsilon.

Consequently both normals strictly expose vertices. Their vertical
components have opposite signs. Opposite vertices cannot occur, the
two right vertices cannot supply a negative horizontal sum, and the
same vertex cannot give opposite vertical signs. The full remaining
pair is the two left vertices, with normals (-c,s) and (-u,-v), all
four components positive.

I rederived the torque directly from their original points. Vertical
balance mu_+*s=mu_-*v cancels the common horizontal-coordinate moment,
leaving

    mu_+*h*c - mu_-*(1-h)*u = 0.

At h=0 this is strictly negative; at h=1 it is strictly positive. Both
initial endpoints are therefore genuinely excluded, and 0<h<1.
Reflecting the physical configuration if needed makes the actual C
the upper neighbor. Its support inequality is

    (1-delta)*c + h*s <= epsilon.

Every term on the left is positive. It yields c<1/59, then s>9/10,
and h<1/54. The exact sine squared reserve is 66039/348100. If
epsilon=0 the support inequality is already impossible, so no weak
critical case has been omitted by these bounds.

The other actual neighbor K contains the lower-left H vertex. After
reflecting both coordinates, that vertex has coordinates
1-delta>59/60 and 1-h>53/54, and H occupies its Southwest quadrant.
Both exceed 9/10. The full far-corner obstruction therefore excludes
K itself. This argument keeps every possible K mask and contact owner;
it does not use a K equation.

## 5. The whole original B9 join

The literal diamond edges are CK,CH,KH,CD,KD, with outside edges
H-X-L and C-M. The true degrees are H3,C4,K3,D2,X2,L1,M1, not the
degrees of an isolated end triangle. I reread the complete current
low/critical/type prerequisite

    SHORT_ARM_DISTINCT_GENUINE_ROOT_LOW_CRITICAL_AND_TYPE_FRESH_EXCLUSION.md
    fa43c1e85ac5f290430c0440f2c36dca1333058df6a0b0fda272fa3d0469a729.

Its full independent review remains

    REVIEW_SHORT_ARM_DISTINCT_ROOT_LOW_CRITICAL_TYPES_HEXAGON_2026_10_27.md
    e045669a10fa1a1d41f86a350d910790339976da5d8401c028e09e30db4de39d.

It applies to these distinct actual roots without requiring their edge
or their degrees, and closes all direct-D leaves, arm diagonals and the
whole d<=1 domain. The only remaining high cases have direct M=S and
an actual width-one arm with L=S or D. In the S case its original
application is delta*e=epsilon*e. In the D case it is (r-1)*e, with
delta<0 and |delta|=1-r<r because r>1/2. Thus both meet exactly the
local theorem's hypotheses. The original C is near by its genuine
leaf, and H-C-K is its actual positive triangle.

The local result needs only H's three real pair forces. All four C
forces, all three K forces, the real HK chord, the other tip D and
both arbitrary completion squares remain. Every original radius,
terminal type, width, private load, physical circle mask, individual
zero weight, contact owner and shared application is included.

## 6. Independent exact checks and review boundary

I recomputed the printed rational reserves with exact Fraction
arithmetic. The checks gave 663/6400 for the far-corner excess and
66039/348100 for the sine estimate. Additional strict margins are
1/12 for 59/60-9/10, 11/135 for 53/54-9/10, and 29/30 for the large
owned support versus 1/60. The radius-window implications r>1/2
and epsilon<1/60 have squared reserves 281/1600 and 31/57600,
respectively. These verify the exact hand bounds; no numerical pose
or finite angle cover is a proof premise.

The source is fully accepted at the stated pin with no requested
correction. It closes B9 alone as a whole new attachment. This review
does not modify the fresh attachment cover, any shared ledger, remote
file, Lean code or CI state, and does not infer a whole C1.4.b3 closure.
