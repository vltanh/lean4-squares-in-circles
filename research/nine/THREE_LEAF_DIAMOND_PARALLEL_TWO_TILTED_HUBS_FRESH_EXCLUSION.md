# A parallel three-leaf diamond cannot have two tilted hubs

Date: October 27, 2026.

**Status: complete fresh hand proof of the entire two-tilted-hub
parallel-tip interface, submitted for full independent and root review.**
The one-tilted-hub interface is not claimed here.

## 1. Original graph, full degrees, and actual parallel means

Keep the original nine actual unit squares in the centered circle, with

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,  0<epsilon<1/60.

The positive graph is the diamond HK, HB, KB, HD, KD with distinct
genuine S leaves at H,K,B. Its true degrees are H4/K4/B3/D2. The two
other physical packing squares remain arbitrary and present. No force
at either hub is removed. Every side mean and physical circle mask,
including zero individual corner weights, remains original.

The complete `GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md`
applies to the actual middle B3, with its two genuine near hub neighbors.
We consider its full parallel alternative, normalized so B has its own
East S leaf and both B-to-hub normals are West. Its actual means are

    P_H=(epsilon,t),   P_K=(epsilon,-u),
    t,u>0,  t+u<=1,   mu_H*t=mu_K*u.                 (1)

Both hubs in this theorem are tilted relative to East. Thus P_H,P_K
are their unique rightmost vertices. Label their actual inward axes

    f=(-c,-s),  j=(-s,c),       c,s>0, c^2+s^2=1,
    F=(-C,S),   J=(-S,-C),     C,S>0, C^2+S^2=1,

so the actual units are

    H=P_H+[0,1]f+[0,1]j,
    K=P_K+[0,1]F+[0,1]J.                            (2)

Every genuine S root contains its actual point epsilon times its real
leaf direction. Therefore each hub meets the closed epsilon disk.
They and B are physically clear, since epsilon+sqrt(2)<R.

D is positively loaded. Otherwise its original true unloaded degree
two gives a channel of width at least one between H and K. Their two
actual near points bound that width by 2 epsilon<1, a contradiction.
In particular D is a physical boundary unit, and each actual point of D
has norm at least R-sqrt(2)>129/200. No D2 force equation is subsequently
used in this proof.

The purely geometric triangle facts used below are the complete
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` and Section 2 of
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`. Only their actual physical
triangle statements are imported: an owned axis makes the other normal
nonobtuse; two strict opposite root vertices cannot have touching
neighbors. No external-moment hypothesis at H or K is imposed.

## 2. Complete actual HK feature and mean cover

Write Q_H=P_H+f and Q_K=P_K+F for the facing adjacent vertices.
At H the original HB normal is strict East at P_H. An H-owned HK
normal must have nonnegative East projection by the physical H-B-K
triangle. The only possible owned axes are -f and -j. The first has
positive vertical component, so the actual lower point P_K is strictly
behind its support through P_H; it is impossible. The remaining owned
axis is -j and its original application is P_H+eta*f, 0<=eta<=1.

A strict HK vertex cannot be P_H, because K's sole point on x=epsilon
is the distinct P_K. The upper adjacent vertex P_H+j is impossible:
each strict outward normal there has positive vertical component, and
its support is strictly beyond its value at P_H, whereas P_K is below
P_H. The opposite vertex is excluded by the physical H-B-K triangle;
the parallel-opposite-normal endpoint also separates B and K by a
positive unit width. Hence a strict HK port on H is exactly Q_H.
Reflection gives the whole K cover: Q_K or a K-owned -J side mean.

Both hubs cannot own HK: the H-to-K -j normal has positive x, while
the K-to-H -J normal also has positive x, so they cannot be negatives.
There are exactly three original possibilities:

* Both strict: Q_H=Q_K, hence c=C, s=S, t+u=2s.
* H owns HK: Q_K=P_H+eta*f, where
  eta=C/c in (0,1], C<=c, S>=s, and t+u=S+eta*s.
* K owns HK: Q_H=P_K+eta'*F, where
  eta'=c/C in (0,1], c<=C, s>=S, and t+u=s+eta'*S.

Every full owned mean is retained in these equalities. In the second
case K's strict vertex cone requires c*C-s*S>0; the reflected
condition holds in the third. In the first, s<=1/2 by (1).
Consequently, in every case, with theta=atan(s/c), Theta=atan(S/C),

    Sigma=theta+Theta<pi/2.                          (3)

At H the actual HK unit normal has own components (G,-N), G>=0,N>0.
At K its reverse has components (G',-N'), G'>=0,N'>0. The shared
normal lies between -j and J, so

    N,N'>=cos(Sigma).                                (4)

The actual applications are eta_H*f at H and eta_K*F at K relative
to their B vertices. At least one of eta_H,eta_K equals one; if one
is smaller than one, its corresponding G or G' is zero. This preserves
all original HK endpoint cases.

The actual near points also give the useful bounds

    t<=epsilon+2*epsilon*s/c,
    u<=epsilon+2*epsilon*S/C.                        (5)

Indeed for P_H+alpha*f+beta*j in the epsilon disk, its x coordinate
gives c*alpha+s*beta<=2 epsilon, while its y coordinate gives
t<=epsilon+s*alpha-c*beta. The reflected argument is identical.

## 3. Whole genuine-leaf feature cover on either tilted hub

For H put

    E=epsilon*c+t*s>0,   T=-epsilon*s+t*c,
    P_H.f=-E,           P_H.j=T.                     (6)

The near vertex P_H has norm below d because t<1. The near own-axis
supports are below d; the far +f height 1-E is below one. A radial
S leaf at Q_H=P_H+f would give

    t^2-2*s*t=2*epsilon*(1+c)>0,

so t>2s. Its radial support cone would also require t*c<=epsilon*s.
But t<1 then implies s<1/2 and c>sqrt(3)/2, contradicting these two
inequalities. Thus the complete remaining genuine H leaf types are:

    V: the strict upper adjacent vertex P_H+j,
       t^2+2*c*t=2*epsilon*(1+s);

    S: the owned far +j side,
       t*c=epsilon*(1+s),  T=epsilon;

    O: the strict opposite vertex P_H+f+j.           (7)

If an opposite radial normal reaches an own-axis endpoint, it is
already in the S type; the +f endpoint was excluded above. No actual
root equation was used to obtain (7). K has the reflected same cover.

We split the whole domain according as c,C are both at least 1/4
or one is smaller. By (3), they cannot both be smaller than 1/4.

## 4. Both c,C>=1/4: exact small-frame bounds and leaf types

Let M=max(s,S). The complete HK cover gives M<=t+u. Equations (5)
therefore imply

    M<=2*epsilon+16*epsilon*M,
    M<(30/11)*epsilon<1/22.

In particular c,C>219/220. Repeating the same inequality with this
stronger denominator gives

    s,S<9*epsilon/4<3/80,
    c,C>999/1000,
    t,u<11*epsilon/10,
    |P_H|,|P_K|<1/40.                               (8)

For example the exact refinement reserve is

    9/4 - 2/(1-(4/60)/(219/220)) = 261/2452>0,
    1-(3/80)^2-(999/1000)^2 = 2371/4000000>0.

Also sin(Sigma)<3/40 and cos(Sigma)>99/100. Equation (6) gives

    0<E<21*epsilon/20<1/50,   T>-epsilon*s.

Both far own coordinates of the opposite vertex exceed 49/50 and
99/100, respectively. Its norm is strictly larger than d. Thus the
O leaf type is impossible here; each hub has only V or S.

Their exact identities in (7) further give

    19*epsilon/20<t,u<11*epsilon/10.                 (9)

For V, substituting t<=19 epsilon/20 in its identity would give
2<=19/10+(361/400)epsilon, whereas the right side is below two by
at least 2039/24000. For S the lower bound follows from t>=epsilon.
Thus the original B force ratio in (1) lies strictly between 5/6 and
6/5 in either direction.

## 5. Small frames: full actual HD and KD feature cover

We prove that HD is at the lower adjacent Q_H or on the far +f side,
with its original mean retained. The reflected claim holds for K.

The near vertex P_H is too central for boundary D by (8). The
opposite vertex has both positive far own coordinates greater than
9/10 and cannot be shared by any contained unit. To verify that last
physical fact directly, a right-angle tangent sector avoiding H's
Southwest quadrant has an inward unit axis in the closed Northeast
quadrant; for a side interior use its inward unit normal. The actual
neighbor therefore contains a point of squared norm greater than
(9/10)^2+(9/10)^2+1+2*(9/10)=221/50>1105/256.

The upper adjacent vertex is also unavailable to D. In type V it is
the actual radial S-leaf application; its strict radial vertex sector
and the leaf's inner-side half-plane leave only two sectors of angle
less than ninety degrees. In type S the vertex is in the relative
interior of that same real leaf side, since its transverse coordinate
is -E and |E|<1/50. The one remaining right-angle sector forces a
third unit's axes to be -f,-j. Every corner of that unit is within
|P_H|+sqrt(2)<R, so it is physically clear and cannot be D.

An H-owned +j normal is impossible by the actual H-K-D triangle,
since the HK j-component is strictly negative. If HD were -f,
the same triangle forces G=0. Then the complete H4 f equation has
the strictly negative B term, a zero HK term, a nonpositive real
leaf term, and a strictly negative D term, a contradiction.

It remains to exclude an H-owned -j mean at P_D=P_H+lambda_D*f.
The original D norm lower bound and (8) give

    31/50<lambda_D<=1.                              (10)

The actual normal-segment point W=P_D-j belongs to D. We show that
it belongs to the open interior of K, a physical contradiction.

If H owns HK, Q_K=P_H+eta*f, eta=C/c. Use K's inward axes -F,J
at Q_K and write Delta=lambda_D-eta. W has relative coordinates

    sin(Sigma)-Delta*cos(Sigma),
    cos(Sigma)+Delta*sin(Sigma).                     (11)

Here Delta>-19/50 and

    Delta<=1-C/c
      =((S-s)/c)*(s+S)/(c+C)<tan(Sigma/2).

For Delta>=0 this last inequality puts both coordinates strictly
between zero and one, using sin(Sigma)=tan(Sigma/2)*(1+cos(Sigma)).
For Delta<0 their bounds follow from sin(Sigma)<3/40 and
cos(Sigma)>99/100: the first is below 91/200, and the second is
above 99/100-(19/50)*(3/40)>0 and below one.

If K owns HK, write eta'=c/C and Delta=lambda_D-1, so
-19/50<Delta<=0. In the actual K coordinates based at P_K, W is

    eta'+Delta*cos(Sigma)-sin(Sigma),
    cos(Sigma)+Delta*sin(Sigma).                     (12)

The first is greater than 999/1000-19/50-3/40>0 and strictly
less than one; the second again lies strictly between zero and one.
If both ports are strict, Q_H=Q_K and (12) applies with eta'=1.
Thus every original near-side mean, including its endpoints, is
excluded. Reflection proves the same at K.

We have established the complete actual D force form, in each hub's
own coordinates,

    F_HD=(A,-B_0),  A>0, B_0>=0,
    P_HD=P_H+f+lambda*j,  0<=lambda<=1,
    B_0>0 implies lambda=0.                         (13)

The same statement holds at K with F,J. The full far-side mean in
(13) is not replaced by a vertex.

## 6. Small frames: unchanged H4/K4 moments make both D ports close

At H let the genuine leaf force have magnitude alpha. In type V its
own unit components are (-e,l)=(-E/d,(1+T)/d); its moment about
P_H, in the common own-frame determinant convention, is alpha*m
with m=E/d. In type S take e=0,l=1,m=E. The actual S side application
has relative coordinates (E,1), so that moment also follows directly
from the unchanged mean. In both types

    0<m<21*epsilon/20,
    l-m>19/20.                                     (14)

For V use l=sqrt(1-(E/d)^2)>99/100; for S use 1-E>49/50.
Let gamma be the actual HK magnitude and mu the B magnitude at H.
Its full four-force equation and full moment about P_H give

    A=mu*c-gamma*G+alpha*e,
    B_0=alpha*l-mu*s-gamma*N,
    B_0+lambda*A=alpha*m-eta_H*gamma*N,

    alpha*(l-m)
      =mu*s+gamma*N*(1-eta_H)-lambda*A.             (15)

No force or moment in the original H4 star has been deleted. K has
the identical reflected identities, with its own original parameters
and the same gamma.

At a hub with eta=1, which always exists by Section 2, (15) gives
alpha/mu<(20/19)s<(5/2)epsilon. Its other identity, together with
N>99/100, gives gamma/mu<3 epsilon squared. Equation (9) and the
original B3 ratio transfer the bound gamma/mu<4 epsilon squared
to the other hub. Applying the final identity in (15) there gives

    alpha/mu
      <(20/19)*(9*epsilon/4+4*epsilon^2)
      <(5/2)*epsilon.

The last exact coefficient reserve is 5/2-139/57=7/114. Thus both
hubs satisfy, at every actual mean endpoint,

    gamma/mu<4*epsilon^2,
    A>(99/100)*mu,
    0<=B_0/A<4*epsilon^2,
    0<=lambda<4*epsilon^2.                          (16)

For A, use c>999/1000 and
999/1000-1/900-99/100=71/9000>0. For B_0 and lambda use
B_0+lambda*A<=alpha*m<(21/8)*mu*epsilon^2.

Reverse the two actual H/K-to-D normals to obtain D's own outward
normals. At the H port its unnormalized components are

    (c*A-s*B_0, s*A+c*B_0).

They are strictly positive; at K the y sign is strictly negative
and x strictly positive. Their absolute y/x slopes are less than
1/10 by (8),(16), so their dot product is strictly positive.

Both actual D ports satisfy

    x<epsilon-999/1000<-29/30,
    |y|<(67/20)*epsilon+4*epsilon^2<=41/720<1/4.

Their facing hub corners coincide unless one HK mean is owned.
In the latter case their distance is 1-C/c or 1-c/C, and is less
than 3 epsilon squared because

    1-C/c=(S^2-s^2)/(c*(c+C)),
    6*(999/1000)^2-81/16=462753/500000>0.

Adding the two actual far-side displacements in (16) shows that
the actual D-port distance is below 11 epsilon squared, hence below
one. These are exactly all hypotheses of the full force-free
`CLOSE_SUPPORT_PORTS_STRADDLING_NORMALS_FRESH_EXCLUSION.md`.
Its actual opposite corner contradiction excludes the entire
c,C>=1/4 branch.

## 7. One c<1/4: the entire original large-tilt branch

Reflect and exchange H,K if needed so c<1/4. Both strict HK ports
would give c=C and t+u=2s>1, impossible. H-owned HK would give
C<=c and Sigma>pi/2, also impossible. Therefore K owns HK and

    Q_H=P_K+(c/C)*F,
    t+u=s+(c/C)*S,
    S<c, C>s>24/25.                                 (17)

Equation (5) first gives u<(8/5)epsilon<2/75, hence t>14/15.
The V leaf vertex P_H+j then has x magnitude greater than 283/300
and y greater than 14/15, so its norm exceeds d. Thus H has only
the complete S or O type from (7).

For O, its actual radial norm d gives c+s<=1+2 epsilon. Since
s>1-c^2 and c<1/4, this implies c<8 epsilon/3. For S, its exact
identity t*c=epsilon*(1+s), with t>14/15, gives the stronger
c<15 epsilon/7. Consequently in both cases

    0<S<c<8*epsilon/3<2/45,
    s,C>999/1000,
    u<11*epsilon/10.                                (18)

The last bound follows by substituting into (5); its coefficient
reserve is 11/10-[1+(16/3)/(60*(999/1000))]=991/89910.

Use the actual K axes w=-F=(C,-S), v=-J=(S,C), and put

    p=P_K.w=epsilon*C+u*S,
    k=P_K.v=epsilon*S-u*C.

Then

    K=[p-1,p]w+[k-1,k]v,
    0<p<21*epsilon/20<7/400,
    -11*epsilon/10<k<epsilon*S.                     (19)

The full genuine K leaf cover now leaves only its South type.
Indeed the near vertex and near axes are too central; owned West
would require p=-epsilon. The upper-left vertex has squared norm
less than 1+(11 epsilon/10)^2<d^2. The lower-left vertex has two
own coordinate magnitudes greater than 9/10 and has norm greater
than d. Thus K's actual leaf is owned South or strict lower-right,
and its real radius equation sharpens (19) to

    -epsilon<=k<0.                                  (20)

Its genuine leaf w component is nonnegative. K's original B force
has strictly positive w component, and its original H force is
the owned +v axis by (17). The complete K4 w equation therefore
makes the KD w component strictly negative. The physical K-H-D
triangle makes its v component nonnegative. Thus the original KD
normal is exactly West or strict Northwest in this actual frame.
No K3 equation has been substituted.

## 8. The real H leaf lies near West in the actual K frame

In type S the genuine H direction is j. Its v component is
c*C-s*S=cos(Sigma), strictly between zero and c, and its w
component is -sin(Sigma)<0.

In type O its actual leaf point Z=P_H+f+j satisfies, using (17),

    Z.v=k+c*C-s*S=k+cos(Sigma).

Equations (18),(20) give -epsilon<Z.v<c. Its w component is
P_H.w-cos(Sigma)-sin(Sigma)<epsilon-s*C<0. Dividing by the
actual d>1 bounds the absolute genuine direction's v component
by 2/45 in both leaf types. Its direction therefore differs from
West by less than 1/9; for instance
sin(1/9)>=1/9-(1/9)^3/6>2/45.

The actual H-leaf center ell consequently satisfies

    -91/60<ell_w<-161/108<-7/5,
    |ell_v|<91/540<1/5.                             (21)

Here every real S-leaf center has radius d+1/2 in (3/2,91/60),
and cos(1/9)>161/162. This is the actual leaf, not a substituted
aggregate force or invented boundary square.

## 9. Every actual D frame overlaps that real H leaf

Every contained unit center has radius below 91/60. Every physical
boundary unit center in this high domain has squared radius greater
than 11/6: |c_D|>=R-1/sqrt(2), and
(sqrt(17)/2-1/sqrt(2))^2=19/4-sqrt(17/2)>11/6,
using sqrt(17/2)<35/12. These are physical bounds independent of
all corner weights.

For KD West, D lies in w<=p-1, so c_D.w<=p-3/2<-37/25.
Its center norm bound gives |c_D.v|<1/3, since

    1/9-[(91/60)^2-(37/25)^2]=37/30000>0.

Together with (21), the two centers have squared distance less
than (7/60)^2+(8/15)^2<1. Their open incircles overlap.

For KD strict Northwest, its original K port is

    P=(p-1,k)=(-X,Y),
    49/50<X<1,   |Y|<1/50.                          (22)

Write z=c_D-P. The actual square gives |z|<=1/sqrt(2)<71/100.
From the boundary-center lower bound and |P|^2<1+1/2500,

    P.z>1/6-1/5000,
    -X*z_w>1/6-9/625>3/20.

The exact latter reserve is 17/7500. Since X<=1, z_w<-3/20.
Writing a=ell-P, equations (21),(22) give

    -27/50<a_w<-53/108,
    |a_v|<19/100.

Thus

    z.a>(3/20)*(53/108)-(71/100)*(19/100),

and the actual center difference obeys

    |c_D-ell|^2
      =|z-a|^2
      <1/2+(27/50)^2+(19/100)^2
          -2*[(3/20)*(53/108)-(71/100)*(19/100)]
      =3421/3600=1-179/3600<1.                      (23)

This again contradicts physical interior disjointness. The cap includes
every D orientation, side owner, actual application mean and physical
circle mask; it invokes no D concurrence or reduced force equation.
It excludes the whole large-tilt branch (17).

## 10. Complete interface conclusion and remaining scope

Sections 2--9 cover all two-tilted-hub parallel B contacts, including
both strict HK corners, either original owned HK mean, every endpoint,
all genuine hub-leaf features and every D support feature. The actual
H4 and K4 forces were retained wherever equations were used. The
physical D2 load was established without an extra boundary assumption.
All nine squares remain present.

Therefore the entire parallel-tip / two-tilted-hub interface is
impossible. Combined with the independently reviewed
`THREE_LEAF_DIAMOND_NONPARALLEL_AND_OWNED_PARALLEL_FRESH_EXCLUSION.md`,
only the parallel B interface with exactly one tilted hub remains for
the whole A8 attachment. This source does not claim that last case or
change the shared cover, ledger, compilation, CI or remote state.
