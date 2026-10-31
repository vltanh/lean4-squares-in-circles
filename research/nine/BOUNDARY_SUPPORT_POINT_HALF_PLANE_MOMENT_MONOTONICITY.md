# A boundary support point controls every contact moment across a coordinate half-plane

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: new complete proposed force-free theorem and arbitrary-degree
full-star consequence, frozen for separate independent and root review.**
The support direction need not be an own side axis of the boundary
unit. Its actual minimum point may be a tilted vertex or any point of
a full aligned side. No original contact mean or normal is changed.

## 1. Complete statement about the original circle origin

Let R>sqrt(2). Keep actual closed unit squares in the same radius-R
disk about O, with pairwise disjoint open interiors. Use an oriented
orthonormal chart with the unchanged circle origin O=(0,0).

Let K be a physical boundary unit. Suppose it has an actual minimum-x
support point

    P=(X,h),          X>-1/2, h>=0.                       (1)

Thus K lies in x>=X. The horizontal direction in (1) is arbitrary
relative to the actual axes of K. Let F be any nonzero nonnegative
combination of K's actual physical circle-corner position vectors,
with every individual zero coefficient and every physical corner
retained. Assume

    F_y<=0.                                               (2)

Let T be any other actual contained unit touching K. Keep its actual
common support normal g directed from K into T and its original
application q, including the full shared-side interval. Then

    det(q,g)<0  implies  g_y<=0.                          (3)

There is no force-balance, degree, load, or boundary hypothesis on T.
There is no prescribed contact owner and no selected-normal premise.
The proof below covers every actual K feature and every side endpoint.

Reflecting the chart in the vertical axis gives the equivalent left
version. If K has a maximum-x support point (-X,h), with X>-1/2 and
h>=0, and F_y<=0, then

    det(q,g)>0  implies  g_y<=0.                          (4)

The reflection reverses the moment and leaves the y component fixed.

## 2. The universal actual-neighbor support bound

Put

    d=sqrt(R^2-1/4)-1.

For any actual contained unit with center z and own orthonormal axes
u,v, its farthest-corner squared norm is

    |z|^2+1/2+|z.u|+|z.v|>=|z|^2+|z|+1/2.

Containment therefore gives |z|<=d+1/2. Every actual unit has
projection halfwidth at least 1/2 in every unit direction. If a unit
is contained in the half-plane g.x>=a, its center projection is at
least a+1/2, and hence

    a<=d<R-1.                                            (5)

The last inequality is strict because sqrt(R^2-1/4)<R. In particular,
every actual K-to-T contact has q.g<=d. This is a whole-body support
bound, with no assumption on T's degrees, normals, or circle mask.

We will also use the following elementary observation. If U=(A,B)
has A>0 and B>=0, while a unit vector g has g_y>0 and

    det(U,g)<0,

then g_x>0 and

    U.g>A.                                               (6)

Indeed A*g_y<B*g_x forces B>0 and g_x>0. Consequently
U.g>A*g_x+A*g_y^2/g_x=A/g_x>=A. This proves the strict statement,
including every possible normal-cone endpoint satisfying its premises.

## 3. The entire tilted-vertex case

Suppose the minimum-x support of K is a unique vertex. Write its
unchanged actual pose as

    K=P+[0,1]u+[0,1]v,
    u=(c,s), v=(s,-c), c,s>0, c^2+s^2=1.                  (7)

Both inward axes have strictly positive x components, and one points
up while the other points down. Equation (7) is the complete actual
nonaligned minimum-x vertex case. Define its other actual vertices

    U=P+u, V=P+v, W=P+u+v.

### 3.1. Locate the full physical circle mask

Because (2) holds for a nonzero nonnegative combination, some actual
physical circle corner has y<=0. The point U has y=h+s>0. Neither
P nor V can be a circle corner, since

    |U|^2-|P|^2=|W|^2-|V|^2
      =1+2Xc+2hs>0.                                    (8)

The strict inequality follows from X>-1/2, 0<c<1 and h,s>=0.
All four vertices are actually contained in the disk, so the strict
larger norm in (8) excludes the smaller one from its circle. Thus
the nonpositive-y physical circle corner must be W. In particular

    W_y=h+s-c<=0,
    c>=s, 0<=h<=c-s,
    R^2=(X+c+s)^2+(h+s-c)^2.                             (9)

This argument permits both W and U to be physical circle corners
and permits a zero coefficient at either. It uses only the existence
of a nonpositive-y circle corner forced by (2).

If X<=0, then 0<X+c+s<=c+s, because X>-1/2 and c+s>=1.
Equation (9) would give

    R^2<=(c+s)^2+(c-s)^2=2,

contrary to R>sqrt(2). Hence

    X>0.                                                 (10)

All x coordinates of K are therefore strictly positive. Also U has
nonnegative y and W has nonpositive y.

### 3.2. The upper vertex is beyond every possible neighbor support

Put A=U_x=X+c>0. From (9),

    R^2<=(A+s)^2+(c-s)^2.

The exact difference is

    (A+1)^2-[(A+s)^2+(c-s)^2]
      =2A(1-s)+s(2c-s)>0.                              (11)

Here A>0, s<1 and c>=s. Thus

    U_x>R-1>d.                                          (12)

Every actual outward normal at U that has positive y component and
negative moment has support greater than U_x by (6). Equation (12)
and the actual-neighbor bound (5) exclude all of them.

### 3.3. Complete vertex, side and normal-cone cover

Suppose g_y>0 at an original actual K-to-T contact. We check every
feature of K.

At P, the outward normal cone is generated by -u and -v. A vector
in this cone with positive y component has nonpositive x component.
Since P_x=X>0 and P_y=h>=0, its moment is strictly positive.

At V, the outward cone is generated by -u and v. Both generators
have negative y component, so g_y>0 is impossible there.

At W, the outward cone is generated by u and v. Every vector in
this cone has strictly positive x component. Since W_x>0 and
W_y<=0, a positive-y g has strictly positive moment.

At U, every negative-moment positive-y normal was already excluded
by (12) and (5). This covers its full closed normal cone.

For relative side-interior applications, the sides P--V and V--W
have outward normals -u and v, respectively, both with negative y
component. The side P--U has outward normal -v=(-s,c); its every
point has positive x and nonnegative y, so its moment is strictly
positive.

The last side U--W has outward normal u=(c,s). Write its unchanged
actual application as q=U+t v with 0<=t<=1. Since det(v,u)=1,

    det(q,u)=det(U,u)+t.

A negative moment at q therefore implies det(U,u)<0. The support
height q.u=U.u is the same as at U, and (6), (12), (5) again exclude
the actual neighbor. This argument retains every original mean and
both endpoints of the side interval.

All four sides, four vertices and all normal-cone endpoints have now
been covered. No contact with g_y>0 can have negative moment, which
proves (3) in the entire tilted case. The equality W_y=0 and the
diagonal orientation c=s were retained in (9)--(11).

## 4. The entire aligned-side case, including arbitrary original means

If the minimum-x face is a side, the actual unit is

    K=[X,X+1] times [B,B+1],
    B<=h<=B+1, h>=0.                                    (13)

The actual side parameter in (13) is unrestricted. Since X>-1/2,
every physical circle corner lies on the right side x=X+1: the
squared-norm increase from the left side is exactly 2X+1>0.

Condition (2) forces a nonpositive-y physical circle corner. The
upper coordinate B+1 is nonnegative by (13). If it were zero, the
lower coordinate -1 would have strictly larger absolute value, so
that upper zero corner could not be a circle corner. Consequently
the lower right corner must be physical, with

    -1<=B<=-1/2,
    R^2=(X+1)^2+B^2.                                    (14)

The equality B=-1/2 is the full physical two-corner case. Its original
weights, including a zero one, remain unrestricted subject to (2).

Since X+1>1/2 and R>sqrt(2), equation (14) gives X+1>1, so X>0.
Let U=(X+1,B+1) be the upper right vertex. It has U_x>0 and
U_y>=0. Also

    R^2<=U_x^2+1<(U_x+1)^2,
    U_x>R-1>d.                                          (15)

On the top side the normal is North, and its moment is the strictly
positive application x coordinate. At the upper left vertex, every
positive-y outward normal has nonpositive x component, so its moment
is strictly positive. At the upper right vertex, a positive-y
negative-moment normal contradicts (6), (15), (5). The two lower
vertex cones and the bottom side have nonpositive y components, and
the vertical side normals have zero y component. This exhausts all
actual aligned features, including both original side endpoints.

Thus (3) holds also in the full aligned-side case. Sections 3--4
exhaust every actual unit frame, proving (3) and its reflected form (4).

## 5. A full-star consequence with no endpoint side-ownership premise

Let K be a physical boundary unit with an actual maximum-x support
point (-X,h), where X>-1/2 and h>=0. Retain its full original force
equation in the form

    F-sum_i lambda_i N_i+sum_j mu_j g_j=0,                 (16)

where F is its nonzero full nonnegative circle resultant, every
lambda_i and mu_j is positive, N_i are the unchanged incoming unit
directions, and g_j are the unchanged outgoing unit directions.
Every original pair force is present in one of these sums.

Suppose every incoming direction has (N_i)_y>=0 and every outgoing
original contact has strictly positive origin moment

    det(q_j,g_j)>0.                                      (17)

Then

    F_y>=0.                                              (18)

Indeed, if F_y<0, the reflected geometric theorem gives
(g_j)_y<=0 for every outgoing contact, including all original means.
The exact y projection of (16) would give

    F_y=sum_i lambda_i (N_i)_y-sum_j mu_j (g_j)_y>=0,

a contradiction. If at least one incoming direction has strictly
positive y component, the same reasoning under the assumption F_y<=0
uses the nonstrict premise (2) and gives the stronger conclusion

    F_y>0.                                               (19)

No incoming direction is assumed to be an own axis of K. No outgoing
neighbor is required to touch the circle. The only moment information
used is the original strict sign in (17). True degrees are arbitrary;
no two-force law, resultant replacement or concurrence is introduced.

## 6. Exact preservation and verification boundary

The geometric result is self-contained. It uses only actual unit
geometry, actual containment in the original circle, genuine common
support half-planes, and the full nonnegative physical circle mask.
The star consequence is the direct projection of the entire stated
original equation. In the repository's physical certificate the force
and moment conventions are those of `PHYSICAL_CONTACT_STRESS.md`,
current SHA-256
`d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5`.

This theorem applies for all R>sqrt(2), without an upper radius bound.
It makes no statement about a whole original graph/load family's
remaining feature union. A caller must still prove its support point,
the original-origin coordinate inequalities, the full incoming signs,
and every outgoing original moment sign. No original fine or coarse
gate is changed by this source.

No pose sampling, numerical optimization, computational exclusion,
force deletion, mean replacement, normal selection, Lean compilation,
CI, workflow, metadata edit, commit or publication is used. This new
source requires its own complete independent and root reviews.
