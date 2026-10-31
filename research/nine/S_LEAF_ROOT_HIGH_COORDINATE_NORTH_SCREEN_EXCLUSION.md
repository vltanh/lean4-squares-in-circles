# A shallow S-root north contact is clear, and the ordered high-coordinate root is impossible

Date: October 27, 2026.

**Status: complete local hand proof, submitted for full root and separate
independent review.** The physical screen uses no neighboring force
equation. Its ordered-root consequence keeps the actual genuine leaf
and both other forces at a true degree-three root. It does not yet
close the entire C5 S1234 family: the lower-coordinate root domain
is stated explicitly in Section 6.

Keep the same nine physical interior-disjoint closed unit squares and
the original containing circle. The accepted same-nine lower bound
reduces to

    2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    r=R-sqrt(2),
    14/15<d<61/60.                                      (1)

In particular R^2=d^2+2d+5/4. No physical square is removed when
using this lower bound.

## 1. The purely physical north-contact statement

Let an actual genuine tilted S leaf have inner midpoint P=(U,V),
radial direction e=(U,V)/d, and transverse direction f=(-V,U)/d.
Suppose its actual root and leaf are

    A=[U-1,U] times [V-1,V],
    L=P+[0,1]e+[-1/2,1/2]f,

where

    U^2+V^2=d^2,       U>4/5,       0<V<9/20.           (2)

The root and its other neighbors may have arbitrary actual degrees
in this section. No origin-interior assumption is needed here.

**Physical screen.** There is no physical circle-touching unit T
with an actual north contact at a point

    Q=(x,V) in A intersect T,       U-1<=x<=U,
    T subset {y>=V}.                                    (3)

All actual side-mean endpoints and circle masks are included.

Every point of a physical boundary unit has norm at least r, by
comparison with any actual circle corner of that same unit. Thus

    x^2>=r^2-V^2>9/64.

Indeed sqrt(2)<9051/6400, because its squared comparison has
reserve 601/40960000, and consequently

    r^2>(2-sqrt(2))^2>549/1600,
    r^2-(9/20)^2>9/64.

Since x>=U-1>-1/5, the negative alternative is unavailable:

    3/8<x<=U<61/60.                                    (4)

This is a bound on the original actual mean, not a replacement mean.

## 2. If T owns the north contact

Then T is aligned and has the form

    T=[z,z+1] times [V,V+1],       x-1<=z<=x.

Physical avoidance of the real L forces z+1<=U. If z+1>U, then
at height V+eta for a sufficiently small positive eta the inner
leaf edge is at x=U-(V/U)eta<U, and its open horizontal section
extends to the right of U. That interval meets the open section
of T, since z<=x<=U<z+1. This would give interior overlap.
The argument includes equality at a side endpoint by using
positive eta.

By (4), z>x-1>-5/8, whereas U>4/5. Every actual T corner
therefore has squared norm at most

    U^2+(V+1)^2=d^2+2V+1<R^2,                          (5)

the last reserve being 2(d-V)+1/4>0. This contradicts the
physical circle contact.

## 3. The complete tilted T frame and its real leaf screen

Otherwise Q is T's unique bottom vertex. Both possible tilts,
without ordering their axes, are parametrized by

    T=Q+[0,1](c,s)+[0,1](-s,c),
    c,s>0,       c^2+s^2=1.                            (6)

Put g=U-x>=0. The right upward edge of T first crosses the
actual inner supporting line of L at parameter

    t_*=g/(c+(V/U)s).

### 3.1. The edge does not cross before its endpoint

If g>=c+(V/U)s, then x+c<=U. From (4),

    c<=U-x<61/60-3/8=77/120,
    s>3/4.

The second inequality follows from
(77/120)^2<7/16. The actual opposite corner has coordinates

    X=x+c-s,       Y=V+c+s.

They obey

    -5/8<X<61/60-3/4=4/15,
    0<Y<9/20+sqrt(2).

Thus

    X^2+Y^2
      <25/64+(9/20+sqrt(2))^2
      <4-1501/11200<4,                                (7)

where sqrt(2)<99/70 was used in the second comparison.
The other three corners have absolute horizontal coordinate
at most U and height at most V+1, so (5) applies. This
excludes the entire noncrossing alternative, including t_*=1.

### 3.2. The edge crosses before its endpoint

Now 0<=t_*<1. At the crossing its actual transverse leaf
coordinate, measured from P, is

    f dot (Q+t_*(c,s)-P)=g*d*s/(U*c+V*s)>=0.

If this number were less than 1/2, the actual T edge would
enter int(L) immediately after that crossing. Therefore,
including the actual inner-side endpoint of L,

    g*s>=(U*c+V*s)/(2d),
    x<=U-V/(2d)-(U/(2d))k,       k=c/s>0.             (8)

This is an actual edge crossing argument. It assumes no chosen
separating normal between T and L, no center model and no force
equation at T.

We first prove

    k<1.                                               (9)

If k>=1, then U<=d and d<61/60 give

    x<=U(1-1/(2d))-V/(2d)
      <31/60-(30/61)V=:E(V).

The comparison E(V) is positive on 0<=V<=9/20. On that interval
the concave quadratic

    12/35-V^2-E(V)^2

has positive values 1913/25200 and 99625/1875384 at its two
endpoints. It is therefore positive throughout. But
r^2>(2-sqrt(2))^2>12/35, using sqrt(2)<99/70, so the original
boundary point satisfies

    x^2>=r^2-V^2>12/35-V^2>E(V)^2,

contradicting 0<x<E(V). This proves (9) over the entire angle
interval.

## 4. Every tilted T corner is strictly internal

The point Q itself has norm at most d<R. The left adjacent
corner Q+(-s,c) has horizontal absolute value at most U:
its lower bound is x-s>x-1>-5/8>-U, and its upper bound is
at most x<=U. Its height is at most V+1, so (5) excludes a
circle contact there.

For the right adjacent corner Q+(c,s), put t=U/(2d).
Equation (2) gives t>24/61>3/8. Equation (8) implies

    x+c<=U-V/(2d)+c(1-t/s)
         <167/120-(30/61)V.                            (10)

Here the elementary complete-angle bound c(1-t/s)<3/8 is
proved as follows. On its positive part, the maximum of
sqrt(1-s^2)(1-t/s) occurs at s^3=t and equals
(1-t^(2/3))^(3/2). Since t>3/8, this is less than
1/(2sqrt(2))<3/8. The nonpositive part is immediate.

The first coordinate in (10) is positive. The squared norm
of that corner is therefore bounded above by the convex quadratic

    [167/120-(30/61)V]^2+(V+1)^2.

Its reserves below 4 at V=0 and V=9/20 are respectively
15311/14400 and 5655823/10716480. A convex function on a
closed interval is no larger than its larger endpoint value.
Hence this corner is also strictly inside D_2.

Finally, the opposite corner's first coordinate is

    X=x+(k-1)/sqrt(1+k^2).

Its lower bound is X>x-1>-5/8. By (8),

    X<=U-V/(2d)-(U/(2d))k+(k-1)/sqrt(1+k^2).

The last expression is increasing in 0<=k<=1. Its derivative is

    -U/(2d)+(1+k)/(1+k^2)^(3/2)>0:

indeed 1+k>=1+k^2 on this interval, so the second term is
at least 1/sqrt(1+k^2)>=1/sqrt(2)>1/2>=U/(2d).
Consequently

    X<=U-(U+V)/(2d)<=U-1/2<31/60<5/8,

where U+V>=d. The opposite corner's height is below
9/20+sqrt(2), so the same strict bound (7) applies.

Every actual corner in every possible frame is now strictly
inside D_R. This contradicts physical circle contact and proves
the physical screen (3), including all original masks and all
zero individual corner weights.

## 5. Ordered genuine S3 roots with U>4/5

Suppose now that A has its true three positive forces: its genuine
S leaf and two physical boundary neighbors T_1,T_2. Use the
actual tilted own frame

    A=[U-1,U] times [V-1,V],
    U>=V>0,       U^2+V^2=d^2,
    U>4/5.                                             (11)

Write theta=arg(e), where 0<theta<=pi/4. Keep the actual
applications p_i, actual normals n_i and positive magnitudes mu_i.
Assume their actual occupied-arc order, cut at the real leaf,
and their unchanged origin moments are

    theta<arg(n_1)<=arg(n_2)<theta+2pi,
    det(p_1,n_1)>0,       det(p_2,n_2)<0.              (12)

All angles here are compatible lifts in that real root order.
These are geometric order and actual moment hypotheses, not a
force deletion. The complete root equations are

    alpha e+mu_1 n_1+mu_2 n_2=0,
    mu_1 det(p_1,n_1)+mu_2 det(p_2,n_2)=0,
    alpha,mu_1,mu_2>0.                                 (13)

**Ordered-root consequence.** Equations (11)--(13) are impossible.

The real leaf port (U,V) belongs to no third unit. Its root
inward sector is the southwest quadrant and the actual leaf
inward sector is the northeast-facing half-plane. The two
remaining tangent gaps have angles theta and pi/2-theta,
both strictly below pi/2. A third unit's connected inward
sector has angle at least pi/2 and cannot fit. In particular
the +e root support cannot be another positive contact.

The northwest root vertex is ineligible for a boundary neighbor:

    |(U-1,V)|^2=d^2+1-2U<d^2-3/5<r^2.                (14)

For the final inequality, the positive comparison
2d+77/20>2sqrt(2)R follows by squaring: its squared reserve is

    1929/400-(3/5)d-4d^2
      >1929/400-(3/5)(61/60)-4(61/60)^2
       =281/3600>0.

Since r^2-d^2+3/5=2d+77/20-2sqrt(2)R, this is exactly (14).

The two normals cannot be parallel. The +e direction is excluded
above; a parallel balance therefore has both equal to -e,
acting at the southwest vertex. Its origin moment is
(V-U)/d<0. The inequality U>V follows from U>4/5 and
d<61/60. This contradicts the full torque in (13).

Projecting the nonparallel force equation onto f shows that
f dot n_1 and f dot n_2 are nonzero and opposite. Their
actual lift order in (12) therefore gives

    f dot n_1>0,       f dot n_2<0.

The first force line and the radial leaf line meet at q e.
Taking the full torque about that intersection shows that the
second force line passes through it too. Thus

    det(p_1,n_1)=q det(e,n_1)=q(f dot n_1)>0,
    q>0.                                               (15)

No degree-two or isolated-triangle equation has been imposed
on A.

Here V<=d/sqrt(2)<1, while U<61/60; no assumption that O
belongs to the root has been introduced. The complete positive-f
first-normal feature cover now leaves
only North. Strict northeast uses the unshareable leaf point.
Strict northwest uses the ineligible vertex (14). A West
contact would have height qV/d>0; every such point on the
left side has norm at most the ineligible northwest vertex.
A strict southwest normal (-c,-s) with positive f component
has s/c<V/U. If U>=1, its actual southwest moment
(1-U)s-(1-V)c is immediately strictly negative. If U<1,
the same moment satisfies

    (1-U)s-(1-V)c
      <c[(1-U)V/U-(1-V)]
       =c(V-U)/U<0,

contradicting (12). The remaining own axes lie on the negative-f
side and cannot be n_1. Hence n_1 is North.

The full x and y components of (13) then make n_2 strictly
southwest, at the actual point (U-1,V-1). Its physical boundary
norm forces V<9/20. Indeed |U-1|<1/5 in the entire original
range, including U>=1. Otherwise

    |(U-1,V-1)|^2<1/25+(11/20)^2
       =137/400<12/35<r^2,

with exact reserve 1/2800 in the middle comparison. Thus the
physical hypotheses of Sections 1--4 hold for the actual North
neighbor T_1, a contradiction. This proves the ordered-root
consequence with the full original forces and all actual means.

## 6. Exact C5 S1234 caller and retained remainder

For the original cycle

    A--B_1--B_2--B_3--B_4--A

with a genuine S leaf at A and all four B_i positively loaded,
the two actual root neighbors have true degree two and physical
boundary neighbors along the path. The positive physical
embedding puts their actual occupied root arc in the same
orientation as the boundary path, and the real boundary leaf
is in the exterior face.

The geometric port-order argument in
GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, Section 1, applies
to this actual path without using that source's zero total
hub-force equation. Cut the root boundary at the real leaf
point, which is unshareable as above. Label the path in the
counterclockwise occupied-arc order. The degree-free
boundary-pair moment theorem in
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1, gives positive
origin moment on each directed boundary-path edge. The two
true endpoint torque equations therefore give exactly (12).
Every B_i equation and every actual circle load is retained;
no internal spoke is introduced. Weak physical junctions are
covered by the same original port-order/uncrossing convention.

Consequently the entire tilted-root portion with U>4/5 is
excluded by Section 5, including every non-origin-interior root.
The lower-coordinate
portion U<=4/5 is **not** excluded by this source.

For orientation only, the existing quarter-disk capacity
argument excludes the strict domain in which A contains a
slightly larger disk than D_(1/4). In the origin-interior
tilted chart with U>=V this includes U<3/4: both other radial
margins then also exceed 1/4 in the present d window. Its
endpoint U=3/4 is retained. A complete S1234 assembly must
therefore still handle the remaining root coordinates and
the aligned domain through its literal complete sources.
No whole fine or coarse gate is
closed here.

The physical screen and the ordered-root consequence may be
used in another graph only after their actual geometric,
degree and ordered-moment hypotheses are proved there.
In particular a transmitter is not treated as a physical
boundary edge. All original completion squares remain, and
no shared metadata, remote state, normal, mean, compilation
or CI is changed.

