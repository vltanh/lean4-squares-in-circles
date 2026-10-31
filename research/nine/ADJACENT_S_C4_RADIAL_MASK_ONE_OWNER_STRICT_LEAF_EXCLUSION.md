# A radial C excludes the strict tilted-root leaf in the one-owner adjacent-S C4

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root and
separate independent review.** It closes the entire C-two-corner /
D-unique / exactly-one-AB-owner domain in which the nonowner B has its
strict lower adjacent genuine leaf. The owned B leaf and the other radial
placement remain separate.

Keep the same nine actual units and full original component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

with genuine S leaves, clear A,B, positive C,D circle totals, and

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60,       R^2<=Q_*=1105/256.

C has two physical circle corners and D one. The sole AB owner is A.
Use the accepted all-mask leaf reduction and radial-boundary owner theorem.
The West A type is separately excluded by
ADJACENT_S_C4_RADIAL_MASK_ONE_OWNER_HORIZONTAL_LEAF_EXCLUSION.md.
Thus A's actual genuine application is its strict outer lower vertex.

## 1. The two actual roots and all original means

Normalize the unchanged AB normal to East and its common cycle moment
positive. In world coordinates,

    A=[-X,h] times [-v,1-v],       X=1-h,
    d*e_L=(-X,-v),       X^2+v^2=d^2,
    P_AB=(h,-k),       |h|<=epsilon,       0<k<v<13/50.

The original point is a fixed B vertex and a relative-interior A-side
point. Write B's actual inward frame there as

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1.

In the positively oriented (j,f) frame,

    B=[xi,U] times [-w,1-w],       U=1+xi,
    d*e_M=(U,-w),       U^2+w^2=d^2,
    h=xi*s-w*c,       k=xi*c+w*s.                         (1)

This is the strict lower adjacent B leaf, so w>0 and
-epsilon<xi<epsilon.

Because C is radial, BC is the original B-owned North contact. Keep
its complete actual point

    Q_BC=(t,1-w),       t=xi+ell,       0<ell<1.

The radial corner norm and the true B3 force and torque give

    t^2=U^2+2w-3/4,       t>1/2,
    c/s=w*(U-t)/[U*(t-U+1)].                            (2)

In particular t<U. To verify the last identity directly, write the
genuine M force as beta*(U,-w), the AB magnitude as mu and BC as nu.
Then beta*U=mu*s, nu=mu*c+beta*w, and nu*ell=beta*w.
All of (2) holds at the unchanged original ell.

The relative-interior inequality k<v has a useful physical consequence.
Using h^2+k^2=xi^2+w^2=d^2-2U+1 and the A radius gives

    U+h>1,       xi*(1+s)>w*c>0.                         (3)

Therefore

    xi>0,       U>1,       0<w<11/60,

and the two actual leaf identities give

    v^2+w^2+2w*c+2xi(1-s)+h^2+xi^2
        =2(d^2-1)<121/1800.                             (4)

No root equation or geometry was replaced in (3)--(4).

## 2. One elementary scalar bound: c/s<1/15

Put T0=sqrt(1/4+2w). Since U>1 and U<d, (2) gives

    c/s < w*(d-T0)/(T0-epsilon).

All denominators are positive. We claim this is less than 1/15.
It suffices to show

    (15w+1)*sqrt(1/4+2w) > (61/4)w+1/60.                (5)

Both sides are positive. Their squared difference is

    P(w)=450w^3-(1861/16)w^2+(1079/120)w+899/3600.

It is positive over the entire interval 0<=w<=11/60 by a single
positive-basis identity. With z=60w/11 in [0,1],

    P(w)=(899/3600)(1-z)^3
         +3(17263/21600)z(1-z)^2
         +3(35/768)z^2(1-z)
         +(195/256)z^3>0.

This is an exact scalar identity, not a pose subdivision. Hence

    c/s<1/15,       c<1/15,       s>119/120.             (6)

## 3. The full original mean gives w<1/6 and the needed k bound

Suppose w>=1/6. Then

    xi=(d^2-w^2-1)/(U+1)<7/2400,
    xi*(1+s)<7/1200.

On the other hand, throughout w<11/60, equation (2) gives

    t^2<2341/3600<(13/16)^2.

Since U>1 and t-U+1<t, the same exact ratio in (2) gives

    w*c=s*w^2*(U-t)/[U*(t-U+1)]
        >(119/120)*(1/36)*(3/16)/[(61/60)(13/16)]
         =119/19032>7/1200.

The last reserve is 133/317200. This contradicts (3), proving

    w<1/6.                                              (7)

Now t^2=d^2-w^2+2w-3/4 increases with w on this range, so

    t^2<(61/60)^2-1/36+1/3-3/4<(77/100)^2,

with final reserve 7/1875. Thus (2),(6) also give

    c/w>2737/9394=:K0.                                 (8)

Indeed use U-t>23/100, U<61/60, t-U+1<t<77/100,
and s>119/120.

The actual k satisfies the following whole high-depth implication:

    v>43/240  ==>  k<3/20.                             (9)

For if k>=3/20, then from k^2+h^2=xi^2+w^2 and xi<epsilon,

    w^2>9/400-1/3600=1/45.

Equations (4),(8) would imply

    121/1800>v^2+w^2+2wc
       >(43/240)^2+(1+2K0)/45
        =121/1800+1927/38649600.

This proves (9) with every original mean retained.

## 4. The actual radial C direction in world coordinates

In B's (j,f) frame, the actual C radial direction has positive
coordinates (s0,c0), with

    s0,c0>0,       s0^2+c0^2=1,
    1-w=d*c0-s0/2,       t=d*s0+c0/2.                   (10)

This is the actual inner minimum-North corner. If s0<=0 then
t=d*s0+c0/2<=1/2, contrary to t>1/2; also c0<=0 would give
1-w=d*c0-s0/2<=1/2, contrary to 1-w>5/6. Thus both radial
coordinates are strictly positive, with the axis endpoints excluded.

By (7), 1-w>5/6. If s0>=3/10 then
c0<=sqrt(91)/10<191/200, giving
d*c0-s0/2<9851/12000<5/6. Hence

    s0<3/10,       c0>19/20.

In world coordinates put

    e=(e_x,e_y)=s0*j+c0*f.

Equations (6),(10) give

    0<e_x<11/30,       e_y>2213/2400>9/10.              (11)

Let J e=(-e_y,e_x). The complete original CD cover is:

* a strict inner C vertex
  Q_C=d*e+(1/2)J e; or
* the C-owned transverse side, at Q_C+z*e with 0<=z<=1.

The actual D-to-C normal g has g_x>0 in both cases. In the owned
case g=-J e=(e_y,-e_x). This is exactly the full radial-boundary
feature cover, expressed in the present world frame.

The actual inner corner satisfies

    -1/2<Q_C,x<-139/1800<-epsilon,
    1<Q_C,y<17/15.                                      (12)

For the upper horizontal bound use
d*e_x-e_y/2<(61/60)(11/30)-9/20=-139/1800.
For Q_C,y>1, use e_y>1-e_x^2 and
d*e_x<61*11/1800<1/2:

    d*e_y+e_x/2>d+e_x(1/2-d*e_x)>d>1.

Finally |Q_C|^2=d^2+1/4<4621/3600<(17/15)^2.
Every point of C's retained transverse side has height above one.

## 5. Both strict upper AD vertices are excluded

Let the full genuine A leaf force be alpha*(-X,-v), alpha>0,
and let mu>0 be the original AB magnitude. The full AD vector is

    (alpha*X-mu, alpha*v),

so its vertical component is positive. Its complete features are
North, strict Northwest, or strict Northeast.

### Strict Northwest

Its actual point is (-X,1-v). The unchanged force and moment equations
give the unit incoming D normal proportional to (-r,1), where

    r=X*(v-k)/[v(1-v+k)],       0<r<X/(1-v).             (13)

At this actual minimum support point of D, the inward unit segment in
that normal direction belongs to D, including all side and vertex
owners. Its far endpoint has squared norm

    d^2+2-2v+2 S,
    S=[X*r+(1-v)]/sqrt(1+r^2).

The complete scalar argument in Section 4 of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md applies to this
literal formula with a=X, root depth v and original mean k. Its
hypotheses are exactly X>59/60, v<4/15, (13), and (9).

For clarity, its whole bound is as follows. If v<=43/240,
S>=1-v>d-3/8+v. Otherwise k<3/20. For v<=1/4 this gives
r>4/25 and S>1361/(60sqrt(641))>107/120>d-3/8+v.
For v>1/4 it gives r>3/8 and
S>529/(60sqrt(73))>1>d-3/8+v.
Thus the actual inward unit-segment endpoint is outside the circle.
No degree or circle-mask premise at D is used in this step.

### Strict Northeast

The actual point is Q=(h,1-v). Its C-tangent projection satisfies

    Q dot J e=-h*e_y+(1-v)e_x
       <=epsilon+e_x<23/60<1/2.

Thus D cannot be beyond C's transverse support, and CD must use Q_C.
The genuine D2 proper rays give q_D,x>=h at the Northeast AD normal,
but q_D,x<=Q_C,x<-epsilon<=h at CD, by g_x>0.
This contradiction excludes the whole feature without a D-owner assumption.

## 6. The actual North mean is within one unit of Q_C

Only A-owned North remains. The full A3 force and moment fix its
original mean exactly:

    P_AD=(-X0,H),
    H=1-v>11/15,
    X0=X*k/v,       0<X0<X<61/60.                       (14)

This is a derived actual mean, not a moved endpoint.

We claim

    |Q_C-P_AD|<1.                                       (15)

Its horizontal difference E=Q_C,x+X0 is greater than -1/2.
If v<=1/5, (12),(14) give

    E<1691/1800,       0<Q_C,y-H<1/3,
    |Q_C-P_AD|^2
      <(1691/1800)^2+1/9
       =1-20519/3240000<1.

If v>1/5, then (1),(6),(7) give
k<epsilon/15+1/6<151/900. Therefore

    X0<(61/60)(151/180),
    E<8377/10800<4/5,
    0<Q_C,y-H<2/5.

The squared distance is then below 4/5. This proves (15) throughout
the entire original North-side mean range.

## 7. A D-owned North axis contradicts C's full circle cone

If D owns this vertical contact axis, its actual vertical interval is
[H,H+1]. Since its unique-corner radial concurrence has x=-X0<0,
its actual unique circle corner is its upper-left corner. Write
D=[-T,1-T] times [H,H+1].

The original g has positive x component. If g_y<0, its D application
is the lower-right vertex of height H<1, while all possible CD points
have height greater than one by (12). If g_y>0, its application is
the upper-right vertex, of height H+1>26/15. The C-owned transverse
normal has negative y, so the present case would have to use Q_C,
whose height is below 17/15. Both cases are impossible.

Thus g is the actual East D axis and CD uses Q_C. Let q_C be C's
genuine proper radial concurrence. The BC line is the original line
Q_BC+rho*f, rho>=0. The CD line is horizontal through Q_C, and
Q_C-Q_BC=J e. Therefore

    rho=e_x/s=s0+(c/s)c0<11/30.                         (16)

In C's actual radial frame, q_C has coordinates

    (d+rho*c0, -1/2+rho*s0).

Its full two-corner circle resultant, including either zero individual
weight, lies in the closed cone generated by (d+1,1/2) and
(d+1,-1/2). The lower cone inequality consequently requires

    rho*[c0+2(d+1)s0]>=1.                               (17)

But (6),(10),(16) give

    rho*[c0+2(d+1)s0]
      <(11/30)*(221/100)=2431/3000<1.

This contradicts (17). C was never replaced by a unique-corner body.

## 8. The complete tilted D feature is excluded by the actual corner proof

If D does not own the vertical axis, P_AD is its strict minimum-y
vertex. Reflect the world vertical coordinate. Then its actual chart is

    P=(-X0,-H),
    D=P+[0,1](p,-q)+[0,1](-q,-p),
    p,q>0,       p^2+q^2=1,

and the actual radial C direction becomes (e_x,-e_y). Its other
inner corner is the reflected Q_C.

The complete local argument in Sections 8--10 of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md applies with
these exact substitutions. Here are all its substantive premises and
conclusions, to make the scope explicit.

The genuine D2 concurrence is on the vertical line below P, inside
D, and is a positive multiple of its unique actual circle corner.
Since P dot(-q,-p)>0, the only possible circle corners are the adjacent
P+(-q,-p) and opposite P+(p-q,-p-q). The latter forces p<=q
and, by the original proper-ray inequality,

    R>=sqrt(2)+H>sqrt(2)+11/15>R,

a contradiction. Thus the adjacent circle corner is the actual one,
and its other own coordinate is less than -1/2. The unchanged full
D2 force then makes the D-to-C normal have strictly positive component
along (p,-q). Therefore every actual CD application lies on D's
opposite own side, at distance at least one from P.

The strict C inner-corner feature is excluded by (15). In the
C-owned transverse-side feature, the original normal and support
signs force the actual D right vertex. Keeping its actual C-side
parameter z, the proper concurrence identity gives the radial increment

    A_r=(e_y*q/X0)*[H+q+(e_x/e_y)(p-X0)].

It is strictly positive because

    H-(e_x/e_y)X0
       >11/15-(11/27)(61/60)=517/1620>0.                (18)

The corresponding C-tangent increment B_t is positive, and the actual
two orthogonal D sides give A_r^2+B_t^2=2. The actual D circle
corner is consequently

    (d+z+A_r)e_C+(1/2+B_t)j_C,

in C's reflected radial frame, where z>=0 is the unchanged mean.
Exactly as in the local proof,

    |Z_D|^2-R^2
      >1+sqrt(2)-2d+(2d-1)A_r>11/30.

Thus this final feature also violates the actual containing radius.
No normal, mean or D force has been shortened; the reflected local
argument uses only (14)--(15),(18), the real radial C and the true
unique-corner D2, all supplied here.

## 9. Whole stated interface and remaining frontier

The complete all-mask reduction leaves exactly the present strict B
leaf or its separately retained owned leaf. With C radial, its original
BC contact is North in both. This proof treats the whole strict B leaf:
the two genuine-root identities and unchanged B3 mean yield Sections
1--4; Section 5 excludes both strict upper AD vertices; Sections 6--8
cover its entire original North mean and every actual D orientation.

Hence no original C-two-corner / D-unique / exactly-one-AB-owner
component with a strict lower adjacent B leaf exists. All C weights,
actual contact means and all nine units remain. The C-radial owned-B-leaf
type and the D-radial placement are not counted by this theorem.

No numerical pose, changed physical mask, deleted edge, compilation,
CI, remote write or shared-metadata edit is used.

