# One proper endpoint makes a diagonal boundary channel shorter than 150 degrees

Date: October 27, 2026.

**Status: complete proposed local theorem and whole original
H2_D0.L0124 exclusion, pending full root and separate independent
review.** No original gate, shared ledger, certificate, or remote
object is changed.

Put Q=1105/256. Keep all nine actual unit squares, their disjoint
open interiors, and the unchanged compatible selected certificate.
The geometric theorem below works throughout 2<=R<=sqrt(Q).

**Diagonal-angle theorem.** Let W be an actual unloaded degree-two
diagonal transmitter between two physical circle-boundary squares X,Y.
Suppose just Y has an actual positive proper concurrence on its W-force
line. Then the minor angle between the actual centers of X and Y is
strictly less than 5pi/6.

No concurrence, local equilibrium equation, or degree restriction is
imposed on X. All original shared means, physical circle masks, and
individual zero circle weights remain. Y's positive proper concurrence
is stated explicitly below; it is not required to lie inside Y when
Y has two physical circle corners.

**Original-family consequence.** The entire original gate

    M6.B6.PENTAGON.H2_D0.L0124

is impossible, including its graph-preserving reflected image. Its
true degree-three endpoint 2 retains all three original positive forces.
The contradiction concerns the complete original core; all three
additional actual units stay present.

## 1. Full diagonal endpoint geometry and properness at only Y

The compatible diagonal convention puts W's two actual applications
at opposite vertices, with the actual channel axis owned by both
endpoint squares and each application strictly inside its endpoint
side. Thus X and Y are axis aligned in the channel frame. Orient the
horizontal axis from X to Y. Their horizontal center difference is
exactly 1+sqrt(2).

Every actual contained unit has center radius less than M=91/60.
Indeed, in its own frame a farthest corner has squared norm

    |c|^2+|c.u|+|c.v|+1/2 >= |c|^2+|c|+1/2,

whereas M^2+M+1/2-Q=31/57600>0. Since 1+sqrt(2)>M, the left
center is strictly left of O and the right center strictly right.

Let a,b be the absolute farthest horizontal and vertical corner
coordinates of X, and c,d the corresponding coordinates of Y.
These are the actual physical farthest coordinates, regardless of
the signs of their vertical centers. Write A=2+sqrt(2). Then

    a+c=A,
    a^2+b^2=c^2+d^2=R^2,
    b,d>=1/2,
    11/8<a,c<81/40.                                (1)

For the last bounds, a,c<=sqrt(Q-1/4)<81/40 and
A-81/40>11/8, using sqrt(2)>7/5. The unchanged channel
applications are

    P_X=(1-a,h), P_Y=(c-1,h).                       (2)

The stated one-endpoint premise is precisely

    q_Y=P_Y+ell*(1,0)=t F_Y,
    ell>=0, t>0,                                  (3)

where F_Y is the full original nonzero nonnegative combination of
Y's physical circle corners. It preserves every original corner
weight and the actual application P_Y. No analogous statement is
assumed at X.

### 1.1. Zero channel height is already impossible

Suppose h=0. Equation (3) gives (F_Y)_y=0. Since Y is axis
aligned and its horizontal center is strictly positive, a nonzero
vertical center would give exactly one physical circle corner, with
nonzero vertical coordinate of that same sign. Thus Y must have
vertical center zero, with its two physical circle corners
(c,+/-1/2), and

    c=sqrt(R^2-1/4)>=sqrt(15)/2>1/2+sqrt(2).

The last positive squared comparison is 3/2-sqrt(2)>0.
Consequently a=A-c<3/2 and

    b^2=R^2-a^2>4-9/4=7/4>1.

X's vertical interval is therefore either [b-1,b] or [-b,1-b];
neither contains zero. This contradicts the actual application (2).
Hence h is nonzero. Reflect the common vertical axis, if necessary,
so that h>0. The same original forces and means are retained.

### 1.2. Y has nonnegative center height, including the radial mask

Equation (3) now makes (F_Y)_y>0. A negative Y center height would
give exactly one physical circle corner with negative y coordinate,
which is impossible. Thus the vertical center height of Y is d-1/2
and is nonnegative. Its actual interval is [d-1,d], and

    d-1<h<d.                                      (4)

If d>1/2, the physical circle corner is uniquely (c,d). The positive
ray and nonnegative ell in (3) give the exact proper inequality

    h >= d*(1-1/c).                               (5)

If d=1/2, Y is physically radial with circle corners (c,+/-1/2).
No fixed weight split or inequality (5) is imposed in that case.

## 2. Both endpoint centers at nonnegative height

First suppose X's vertical center is nonnegative. In the actual
channel frame its center is (-(a-1/2),b-1/2), while Y's center is
(c-1/2,d-1/2). Define their elevations above their respective
horizontal axes by delta_X,delta_Y in [0,pi/2). Their upper center
angle is

    gamma=pi-delta_X-delta_Y,
    0<gamma<=pi.                                  (6)

Suppose gamma>=5pi/6, so delta_X+delta_Y<=pi/6. For either endpoint,
let r_i be its actual center radius and delta its elevation. Because
its actual frame is axis aligned, its farthest-corner equation is

    R^2=r_i^2+r_i*(cos(delta)+sin(delta))+1/2.       (7)

This includes delta=0 and either physical radial mask. For
0<=delta<=pi/6,

    cos(delta)+sin(delta)
       <=(1+sqrt(3))/2<11/8.

If r_i<=13/10, equation (7) would give

    R^2<(13/10)^2+(11/8)*(13/10)+1/2
        =1591/400<4,

contrary to R>=2. Therefore each r_i>13/10.

For nonnegative angles with sum at most pi/6,

    cos(delta_X)+cos(delta_Y)
       >=1+cos(delta_X+delta_Y)>=1+sqrt(3)/2.

The first inequality follows directly from
cos(u)+cos(v)-1-cos(u+v)
=4 sin(u/2)sin(v/2)cos((u+v)/2)>=0. Consequently the actual
horizontal center gap satisfies

    1+sqrt(2)
       =r_X cos(delta_X)+r_Y cos(delta_Y)
       >(13/10)*(1+sqrt(3)/2)
       >(13/10)*(1+6/7)=169/70
       >1+sqrt(2),                                (8)

which is a contradiction. The two last strict comparisons use
3/4>36/49 and (99/70)^2>2, respectively. Thus gamma<5pi/6.
Since gamma is already at most pi, it is the minor center angle.

This entire case uses only the actual aligned boundary geometry.
In particular it does not derive a proper concurrence at X.

## 3. The complete negative-height X alternative

Suppose instead that X's vertical center is negative. Its actual
vertical interval is [-b,1-b], with b>1/2. Strict side-interior
membership of the unchanged P_X gives

    0<h<1-b,
    b<1.                                         (9)

It follows that a>sqrt(R^2-1)>=sqrt(3), and hence

    11/8<c<A-sqrt(3)<27/16.                       (10)

For the last strict comparison, it suffices to show
sqrt(3)>sqrt(2)+5/16. Both sides are positive; their squared
reserve is

    231/256-(5/8)*sqrt(2)
       >231/256-(5/8)*(99/70)=33/1792>0.

The physical radial Y mask is impossible in (10), since it would
give c>=sqrt(15)/2>27/16. Therefore Y has one physical circle
corner and the actual inequality (5) applies.

### 3.1. A full convex comparison forces h>3/8

Suppose h<=3/8. Since c>1, inequality (5) would imply

    R^2=c^2+d^2
       <=g(c):=c^2+(9/64)*c^2/(c-1)^2.            (11)

This function is strictly convex throughout c>1:

    g''(c)=2+(9/32)*(2c+1)/(c-1)^4>0.

On the entire closed interval [11/8,27/16], its maximum is
therefore at an endpoint. Both exact endpoint values are below four:

    g(11/8)=121/32=4-7/32,
    g(27/16)=114453/30976=4-9451/30976.             (12)

Equations (10)--(12) give R^2<4, a contradiction. Thus

    h>3/8,
    b<5/8.                                       (13)

This is a whole continuous interval comparison, not a pose test or
an imported two-proper-endpoint height bound.

### 3.2. The actual center elevations differ by more than thirty degrees

Using (13) and R>=2 in the unchanged circle equations gives

    a^2>4-25/64=231/64>(15/8)^2,
    a>15/8,
    c=A-a<1/8+sqrt(2)<31/20,
    d^2>4-(31/20)^2=639/400>(5/4)^2.

Here sqrt(2)<57/40 proves the third comparison. Thus the
positive center magnitudes obey

    a-1/2>11/8,       0<b-1/2<1/8,
    0<c-1/2<21/20,    d-1/2>3/4.                  (14)

Let beta be X's depression below the negative horizontal axis,
and let delta be Y's elevation above the positive horizontal axis.
Equation (14) implies

    0<beta<arctan(1/11),
    delta>arctan(5/7).

The two fixed arctangents differ by an angle in (0,pi/2), whose
tangent is exactly

    [(5/7)-(1/11)]/[1+(5/77)]=24/41>1/sqrt(3),

the strict squared comparison being 3*24^2=1728>1681=41^2.
Therefore delta-beta>pi/6. The upper center angle from Y to X is

    gamma=pi+beta-delta<5pi/6.                    (15)

It lies in (0,pi), so again it is the minor center angle. This
proves the complete negative-height alternative without deleting it
or assigning X the equation of a degree-two loaded unit.

Sections 1--3 prove the diagonal-angle theorem for every physical
unique/radial mask and every unchanged side-interior application.

## 4. A balanced four-boundary path cannot have this true transmitter

The full theorem FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md applies
to four actual physical boundary units forming a three-edge path,
with strictly positive total circle load on each and their full
circle-resultant sum zero. Its Sections 2--3 prove that the minor
angle between the endpoint centers is strictly greater than 5pi/6.
This is the source's actual angular conclusion before its later
metric estimate; no degree-two premise at those endpoints is used.

Suppose those same endpoints X,Y are joined through an actual
unloaded degree-two transmitter W, and Y has the positive proper
concurrence (3). If W is a side transmitter, its two actual
applications have distance one. The endpoint-center distance is
then at most 1+sqrt(2), contrary to the metric conclusion of the
same balanced-path theorem. If W is diagonal, Sections 1--3 above
make its minor endpoint center angle less than 5pi/6, contrary to
the angular conclusion. Both genuine transmitter widths are covered.

This is a local balanced-path obstruction with arbitrary other
original forces at X and the two internal path units. Its force
premise is their full circle-resultant sum, not a stress obtained
by deleting any endpoint edge.

## 5. Exact entire original H2_D0.L0124 join

The original graph and load table is
SIX_BODY_INNER_PENTAGON_LOAD_COVER.md, Sections 1--3. Keep its
actual exterior pentagon 0-1-2-3-4-0 and both positive H spokes
H0,H2. For load set0124, the true degrees are

    0,2: degree three;
    1,3,4,H: degree two.

Exactly 0,1,2,4 have positive total circle load. The actual boundary
path is 2-1-0-4. Summing the full original equations of all six
component bodies cancels every positive internal force, including
both H spokes, and gives

    F_2+F_1+F_0+F_4=0.

Thus the entire original four-boundary-path theorem applies. The
actual rim unit 3 is an unloaded degree-two transmitter between
X=2 and Y=4; its true force and torque equations give one of the
two compatible widths covered in Section 4.

The unchanged endpoint Y=4 has exactly two positive pair forces
and the physical boundary neighbor 0. The full conditional loaded
concurrence theorem, TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md,
Lemma 2.1, therefore gives exactly (3) at its actual force toward
3. That lemma retains all physical circle masks, zero individual
weights, coincident application possibilities, and actual shared
means; a radial concurrence is allowed to lie outside its square.
There is no local concurrence call at the true degree-three body 2.

Every hypothesis of Section 4 is now present, producing the strict
opposite bounds on the same actual endpoint angle. The full original
load family and its graph-preserving reflected image are excluded.

The original radius window below or at two is already excluded for
the same nine actual units by NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md.
That accepted same-nine theorem and its declared dependencies are
retained. The present local proof handles every remaining radius
2<R<=sqrt(Q); its geometric inequalities also include R=2.

No exterior-pocket placement, force-polygon routing at a higher-degree
endpoint, or completion-capacity premise is needed. The earlier
one-proper diagonal cap research files are historical unfinished
stronger questions; their open SAT or pocket-routing steps are not
inputs to this proof. The other H2_D0 load families and its whole
graph parent retain their separate original obligations.

The arithmetic in this source was reconstructed with exact rational
comparisons: sixteen strict comparisons and seven displayed identities
pass. No numerical sampling, new certificate normal, altered mean,
physical stress split, Lean compilation, CI, remote write, or shared
ledger mutation is used.
