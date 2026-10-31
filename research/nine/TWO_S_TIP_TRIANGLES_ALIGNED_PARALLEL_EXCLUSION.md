# Two S tip leaves: an aligned root cannot have parallel triangle reactions

Date: October 27, 2026.

**Status: accepted complete hand original-family exclusion after full
root and separate independent reviews in
REVIEW_TWO_S_TIP_TRIANGLES_ALIGNED_PARALLEL_ROOT_2026_10_27.md and
REVIEW_TWO_S_TIP_TRIANGLES_ALIGNED_PARALLEL_ROOTED_BLOCKS_2026_10_27.md.**
This closes the entire
high-radius aligned-parallel S-root alternative in the remaining
no-intact attachment of C2.33.b2. It includes both aligned and
tilted central hubs and every actual side mean and physical mask.
It does not by itself exclude the case in which both genuine S
roots are tilted.

## 1. The unchanged original graph and the parallel wall

Keep the same nine original physical unit squares, compatible
selected certificate and radius window. The exact positive edges
are

    HA,AB,BH, HC,CD,DH, AL,CM.

Both L,M are genuine S leaves. The actual degrees are
H4,A3,C3,B2,D2,L1,M1; both additional physical squares stay
arbitrary and in place. Write

    d=sqrt(R^2-1/4)-1,    epsilon=d-1,    r=R-sqrt(2).

The low and critical domain d<=1 is already excluded by
`TWO_S_TIP_TRIANGLES_LOW_RADIUS_EXCLUSION.md`. Thus

    1<d<61/60,    0<epsilon<1/60,
    R^2>17/4,    r>129/200,    R<25/12.                (1)

The complete high-radius clearance and origin-interior theorems
in `TWO_S_TIP_TRIANGLES_HIGH_RADIUS_HUB_CLEARANCE.md` and
`TWO_S_TIP_TRIANGLES_HUB_ORIGIN_INTERIOR.md` give physical H
clearance and O in int H. They retain all possible H circle
loads until the actual small-port exclusion. They also prove
that each actual triangle has nonzero common cycle moment and
zero full external origin moment at every vertex.

Assume A is aligned with its genuine east-pointing leaf and its
two actual triangle reactions are parallel. Their physical
outward signs agree; the real east leaf makes both west. The
unchanged actual applications are

    P=(epsilon,y) in A intersect B,
    Q=(epsilon,-w) in A intersect H,

after reflecting vertically. With their original positive
magnitudes mu,nu, the true A moment equation is

    mu y=nu w.                                         (2)

Both whole B,H are in x<=epsilon and attain that support.
B is physically boundary, and every one of its points has norm
at least r. Consequently its actual port has nonzero height.
The weighted mean equation permits the displayed reflection
with y,w>0. Since both original applications lie in one A side
of length one,

    y+w<=1,
    y>16/25,    0<w<9/25.                              (3)

For the strict bound use
(129/200)^2-1/3600>(16/25)^2 and (1). No actual side mean has
been moved to a vertex or midpoint.

Let g be the original B-to-H normal, gamma>0 its magnitude,
and T its actual application. The normal g is not horizontal.
Indeed g=e_x would require the entire H to lie in x>=epsilon
while its maximum x is epsilon; g=-e_x would put H to the left
of B's minimum x, which is strictly below epsilon, again
contrary to H's actual maximum. Thus B's two actual force lines
are nonparallel.

The conditional loaded-tip part of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, makes
their concurrence a strictly positive multiple of B's full
circle resultant. That conditional proof needs no boundary
neighbor once nonparallelism is established. The AB line is
horizontal through P, so this concurrence has height y>0.
Since the true B equation is

    F_B=-mu e_x-gamma g,

we obtain g_y<0. Therefore the actual H-to-B normal

    n=-g

has n_y>0. Put N=nu e_x+gamma n, the full H pair sum for
triangle HAB. The other actual H pair sum, for HCD, is -N by
the unchanged physically clear H equation.

The genuine other root C contains its original inward point
epsilon e_M. If n_C is the actual H-to-C unit normal, its
original separating support therefore satisfies

    0<h_H(n_C)<=epsilon(e_M.n_C)<=epsilon.              (4)

The first inequality follows from O in int H. This concerns
the same real C and the same real HC normal, irrespective of
whether C is aligned or tilted.

## 2. A complete triangle-face observation at an origin-interior hub

We record the full geometric statement used for HCD. At a unit
K containing O openly, take an actual triangle with nonzero
cycle moment and zero full external origin moments. Keep its
original pair sum M and both real ports.

The physical proper-port and side-normal facts in
`RADIAL_TRIANGLE_CONCURRENCE.md`, Section 1, give the following
complete cover. Either the two normals are perpendicular K-owned
axes, or both actual ports lie on one K face and both normals
have strictly positive components along that face's outward axis.
For a nonparallel pair this follows by considering one owned
axis and its nonobtuse partner, or two strict vertices, which
cannot be opposite. Two nonparallel owned axes are exactly the
perpendicular exception. A parallel pair has the same outward
sign; nonzero cycle moment makes the actual ports distinct, so
their common exposed feature is a genuine side and its normal
is the side axis. Actual side means and their endpoints are
included in this cover.

Suppose the pair shares a face of positive height A. Use own
coordinates with that face x=A and write the actual ports
(A,z_i) and normals n_i with (n_i)_x>0. For a nonparallel pair,
the accepted radial concurrence theorem gives

    q=-tau M,    tau>0,
    (A,z_i)=q+a_i n_i,    a_i>=0.

The full zero origin moment gives

    A M_y=sum_i mu_i z_i(n_i)_x.

Hence k=M_y/M_x is a positive weighted mean of the numbers
z_i/A. The proper-line slope is

    (n_i)_y/(n_i)_x
      = A/(A+tau M_x) * (z_i/A)
        + tau M_x/(A+tau M_x) * k.

A positive vertical normal uses the upper endpoint, so this
slope is at most z_i/A; a negative vertical normal uses the
lower endpoint, giving the reversed comparison. Multiplication
by the correctly signed vertical component gives in both cases

    z_i(n_i)_y >= A (n_i)_y^2/(n_i)_x,
    h_K(n_i)>=A/(n_i)_x>=A.                            (5)

The horizontal case is included. For a parallel pair (5)'s
needed conclusion h_K(n_i)>=A is immediate, with equality.
Thus, whenever one actual neighbor contains a point of norm
epsilon, a common triangle face has height at most epsilon.
This is the same exact moment/proper-port inequality used in
the accepted far-side cap proof; no neighbor degree or circle
load is imposed here. In the perpendicular exception, the
actual normal toward that neighbor instead directly bounds
one of the two owned face heights by epsilon.

## 3. A physical boundary unit on this wall lies wholly above 1/2

We use the force-free wall observation from Section 4 of
`TIP_LEAF_BOWTIE_S_ALIGNED_PARALLEL_EXCLUSION.md`, with its
local proof recalled to make the transfer explicit. It requires
only the actual B, (1), B subset {x<=epsilon}, and its actual
point P=(epsilon,y) with 0<y<=1. It uses no intact petal.

If B is aligned, its horizontal interval is
[epsilon-1,epsilon]. Its farther horizontal endpoint has
absolute value 1-epsilon<1. A circle corner therefore has
vertical magnitude greater than sqrt(13)/2>3/2. Because the
vertical interval has length one and contains y>0, that far
corner must be the upper one. The entire B is above 1/2.

Otherwise P is B's unique rightmost vertex, and for c,s>0,
c^2+s^2=1 its actual frame is

    B=P+[0,1](-c,s)+[0,1](-s,-c).                     (6)

P and both adjacent vertices have squared norm below 17/4:
for the upper adjacent vertex the bound is
2+2s+epsilon^2<4+1/3600<17/4, and for the lower it is
2+epsilon^2<17/4. Thus its only physical circle corner is the
opposite vertex. Its horizontal magnitude is less than sqrt(2),
so its vertical coordinate Y satisfies |Y|>3/2. Since
Y=y+s-c>-1, in fact Y>3/2. The lowest B coordinate is
y-c=Y-s>1/2. In either orientation we have proved

    every point of the actual B has height >1/2.       (7)

This includes all actual physical circle masks, irrespective
of their individual weights.

## 4. An aligned hub gives a direct two-coordinate center contradiction

First suppose H is aligned with the vertical wall. Its whole
chart is

    H=[epsilon-1,epsilon] times [t,t+1],    -1<t<0.

Its actual AH normal e_x is H-owned. The physical triangle
nonobtuse fact gives n_x>=0, while Section 1 gives n_y>0.
If n_x>0, the actual HB application is H's upper-right vertex,
whose x coordinate is epsilon. B then contains this point and
P on its maximum-x support. If they differ, this support is a
genuine B side, and its owned normal e_x has negative scalar
product with the other B normal -n, contrary to the physical
triangle owned-normal lemma. If they coincide, those two actual
B normals belong to one square normal cone of angle at most
pi/2 and likewise cannot have negative scalar product. Both
possibilities are excluded. Consequently

    n=e_y,    N=nu e_x+gamma e_y.                      (8)

The other H pair sum is strictly southwest. In the complete
cover of Section 2, its common face must be west or south;
the west face has height 1-epsilon>epsilon and cannot serve
the actual C in (4). If the pair is the perpendicular exception,
its axes are west and south and C again cannot use the west
one. Thus in every original interface

    -t<=epsilon.                                      (9)

The actual B lies north of the original HB support,
y>=t+1>=1-epsilon, and it still lies in x<=epsilon.
Its actual center c_B therefore satisfies

    (c_B)_x<=epsilon-1/2<-29/60,
    (c_B)_y>=3/2-epsilon>89/60.

Every contained unit has center norm strictly below 91/60,
as in `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1.
But the displayed two coordinates give

    |c_B|^2>(29^2+89^2)/3600=8762/3600>8281/3600.

This contradiction excludes the entire aligned-H case.

## 5. A tilted hub has two shallow faces and a tightly controlled HB normal

Now H is tilted. Its unique rightmost vertex is the actual
AH point Q=(epsilon,-w). Write its actual inward axes

    u=(-a,b),    v=(-b,-a),
    a,b>0,      a^2+b^2=1,
    H=Q+[0,1]u+[0,1]v.

In these own axes about the unchanged origin put

    U=epsilon a+bw,
    V=epsilon b-aw.

The actual H intervals are [-U,1-U] and [-V,1-V]. Since O is
in int H,

    0<U<epsilon+w<2/5,
    0<V<epsilon.                                      (10)

The actual H-to-B normal n has positive world vertical component.
Its entire feature cover is particularly short. If it is H-owned,
its scalar product with the other H normal e_x must be nonnegative;
among the four axes only -v also has positive world vertical
component. If it is strict at a vertex, the opposite vertex
Q+u+v is excluded by the physical triangle opposite-vertices
fact; Q+v has only negative-vertical outward normals. It cannot
use Q itself: B would then contain the distinct points P,Q on
x=epsilon. B would be aligned, with a vertical interval of length
one containing both positive and negative heights. All its
corners would have norm below sqrt(2), contradicting its physical
circle contact.

Thus the real HB application is either Q+u with a strict normal,
or its original mean on the side from Q to Q+u with normal -v.
The first triangle's two ports share exactly that face, and

    N_v<0.

The other actual pair sum -N has positive v component. A common
face for that other pair cannot be the near-v face; its outward
components would both be negative. Neither far face can serve
C by (4)--(5), since 1-U>3/5 and 1-V>59/60. It must therefore
use the near-u face. In the perpendicular exception, its
positive v component uses +v; C cannot use that high face or
the high +u face, so its other actual normal is -u. Both
complete alternatives give

    U<=epsilon,    (-N)_u<0,    N_u>0.                 (11)

In particular

    w<=epsilon(1-a)/b=epsilon b/(1+a)<epsilon.          (12)

The HB normal cannot now be -v, because that would make
N_u=-nu a<0. Hence its actual application is T=Q+u and its
actual normal has the strict form

    n=kappa u-lambda v,
    kappa,lambda>0,    kappa^2+lambda^2=1.             (13)

The true H moment for this original pair is zero. In own
coordinates T=(1-U,-V), while det(Q,e_x)=w. Consequently

    (1-U)lambda-V kappa=(nu/gamma) w.

The strict inequality N_u=-nu a+gamma kappa>0 from (11) gives
nu/gamma<kappa/a. Since w>0, substitution yields

    lambda/kappa
      < (V+w/a)/(1-U)
      = b U/[a(1-U)]
      <= b epsilon/[a(1-epsilon)].                    (14)

Every coefficient in this estimate belongs to the original
actual H equations. No mean or normal has been reselected.

## 6. If B is aligned, its center is already outside the allowed disk

Suppose B is aligned, with its actual maximum-x face
x=epsilon. Its owned AB normal is e_x. Nonobtuseness with
its other actual normal -n gives n_x<=0. If n_x<0, then
-n has positive x and negative y, so its actual B application
is B's lower-right vertex of x coordinate epsilon. But the
same point T=Q+u has x coordinate epsilon-a<epsilon.
This is impossible. Thus n=e_y.

In (13) this means kappa=b and lambda=a. Equation (14) gives

    a^2<epsilon,    b>1-epsilon.

By (12) the actual HB height is

    T_y=b-w>1-2epsilon>29/30.

B lies north of that support and in x<=epsilon. Its actual
center satisfies

    (c_B)_x<-29/60,
    (c_B)_y>29/30+1/2=88/60.

It follows that |c_B|^2>8585/3600>8281/3600, again contradicting
the strict center bound |c_B|<91/60. All actual aligned B
side means are included.

## 7. If B is tilted, one of its unchanged corners lies outside the circle

It remains that B has the actual frame (6). Write

    j=(-c,s),    k=(-s,-c),    c,s>0,
    B=P+[0,1]j+[0,1]k.

Its AB normal e_x strictly exposes P. Its other original normal
-n has negative world vertical component. The complete physical
triangle feature cover at B leaves only the lower adjacent vertex
P+k or the owned side normal -j, whose face runs from P to P+k.
Indeed the upper adjacent vertex has only positive-vertical
outward normals; the opposite strict vertex is excluded; and
the only owned axis which is both nonobtuse to e_x and has
negative vertical component is -j. The same point P is excluded
by T_x=epsilon-a<epsilon.

Put W=y+w<=1. If T=P+k, comparison of the coordinates of
T=Q+u gives

    s=a,    c=b,    W=2b.

But T belongs to B, so the force-free wall bound (7) gives
T_y=b-w>1/2 and hence b>1/2. This would give W>1,
contradicting the original A unit-side interval. Every endpoint
case with T=P+k is excluded for this same geometric reason.

Thus T is on the actual side from P to P+k, and its original
normal is n=j. For its unchanged side parameter 0<rho<1,

    T=P+rho k,
    a=rho s,
    W=b+rho c=b+a c/s<=1.

Using a^2=1-b^2, this yields

    c/s <= (1-b)/a = a/(1+b).                          (15)

The components of this same actual n=j in H's frame are

    kappa=ac+bs,
    lambda=as-bc.

Equation (15) makes kappa<=s and lambda>=as/(1+b), so

    lambda/kappa >= a/(1+b).

Together with (14),

    (1-b)=a^2/(1+b)<b epsilon/(1-epsilon),
    b>1-epsilon>59/60.                                (16)

Consequently a^2<2epsilon<1/30 and a<11/60. Equation (15)
then gives c/s<11/119<1/10, so

    c<1/10,    s>99/100.

By (12), (16), and W>=b, the actual height y=W-w satisfies

    y>1-2epsilon>29/30.

Consider the actual opposite B corner

    Z=P+j+k=(epsilon-c-s, y+s-c).

These elementary strict bounds give

    |Z_x|>99/100-1/60=73/75,
    Z_y>29/30+99/100-1/10=557/300.

Therefore

    |Z|^2 > (73/75)^2+(557/300)^2
          =395513/90000
          >390625/90000=(25/12)^2>R^2.

This contradicts containment of the unchanged physical B.
It does not rely on Z having a positive circle weight or being
the previously selected circle corner.

## 8. Exact scope of the resulting closure

Sections 4--7 exhaust aligned and tilted H, and inside the
tilted case aligned and tilted B, including the full normal
and actual side-mean alternatives. Thus a genuine aligned
S root A cannot have parallel triangle reactions in this
complete original high-radius S/S layout. Exchanging the two
actual decorated triangles gives the identical result at C.

The whole other triangle was retained through its actual pair
sum -N, its nonzero cycle moment, full external torque systems,
and the actual C epsilon point. No intact-petal pressure or
loaded degree-two equation was imposed on C. Both arbitrary
completion squares remain present. No selected point normal,
actual mean, circle atom, positive force or physical unit moves.

This is a human geometric core exclusion. It uses no new scalar
certificate, sampled pose, Lean compilation, CI, remote write
or shared-ledger mutation. The all-tilted S/S family remains
separate until its own complete proof is supplied.

