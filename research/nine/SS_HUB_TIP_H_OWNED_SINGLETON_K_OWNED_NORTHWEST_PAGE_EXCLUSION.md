# A K-owned northwest central return has no northwest boundary page

Date: October 27, 2026.  
Author: rooted_final_review.  
Original comparison head: 50c0cd616eb494ade100f055ad518cdbd33c7275.

**Status: complete analytic candidate, pending separate full independent
review.** This excludes the entire northwest HC page in the remaining
H-owned singleton HB / K-owned singleton HK / northwest BK feature.
Both genuine B leaves, both singleton CK owners, the full shared CK
mean and the exceptional free-HC/shared-CK placement are included.
The original H4/B3/C2/K3 equations are retained. No computational
certificate, new normal selection or K2 equation is used.

## 1. Exact original domain and the K-owned central chart

Retain the original nine-unit S/S hub-tip diamond, with positive edges

    HK, HB, BK, HC, CK, HL_H, BL_B,

true H4/K3/B3/C2, both genuine radial S leaves, positive K and C
circle loads, and the three additional physical units. All original
selected normals, actual singleton applications and actual shared
means remain fixed. The complete original mask reductions make K
and C physically unique. The original radius chart is

    R^2=(d+1)^2+1/4, d=1+delta,
    0<delta<1/60, 17/4<R^2<=1105/256, R<25/12.       (1)

Assume the actual singleton HB is owned by H, with H-to-B normal
E1. The accepted whole-owner lower-leaf/positive-page theorem,
before any central-owner restriction, gives

    v_B=(alpha,-beta), w_B=(beta,alpha),
    alpha,beta>0, alpha^2+beta^2=1, beta<1/2,
    P=P_HB=x_B v_B-u_B w_B=(h,-L),
    h=alpha x_B-beta u_B, |h|<=delta, x_B<=delta,
    L=beta x_B+alpha u_B>0, u_B=alpha L-beta h,
    Q=P_BK=P+w_B=(h+beta,Y), Y=alpha-L,
    X=1-h, X^2+A^2=d^2,
    H=[h-1,h] x [-A,G], G=1-A,
    0<L<A<=2sqrt(delta)<31/120, G>89/120.             (2)

All physical K and C circle points have positive height. The
actual H-to-K and H-to-C normals have nonnegative height; the
actual H-to-K normal also has nonnegative horizontal component.
HK is a physical singleton and H,K have distinct frames. The
actual HK and HC applications on H are distinct, including every
actual shared-page mean endpoint.

The two complete genuine B rows, with their unchanged B3 parameter,
are

    vertex: (1+x_B)^2+u_B^2=d^2, 1+x_B>0,
            0<u_B<2sqrt(delta),
            r_B=u_B/(beta+L);

    aligned: x_B=delta, 0<u_B<1,
             actual leaf direction v_B,
             r_B=u_B/beta.                            (3)

The original owned-singleton normal form gives

    m_BK=(w_B-r_B E1)/|w_B-r_B E1|,
    r_B>0, beta r_B<1,
    [beta/(1+alpha)]^3<=delta.                        (4)

Its actual BK is a singleton owned by K at the displayed Q.

Assume now that K alone owns HK and that BK points northwest.
Write the actual K frame and actual side positions as

    m=m_BK=(-c,s), t=(s,c),
    c,s>0, c^2+s^2=1,
    K=S+[0,1]m+[0,1]t,
    R_H=P_HK=(h,G)=S+ell m, 0<ell<1,
    Q=S+theta t, 0<theta<1.                          (5)

Here the actual H-to-K normal is t. Indeed it is a K axis with
nonnegative original horizontal and vertical components, and t
is the only such axis in this strict K frame. Its H support is
the upper-right vertex R_H; K ownership makes the real K-side
position ell strict. Similarly, K owns the real BK side, so theta
is strict. These are actual physical positions, not solved-for
replacement applications.

Equating the two expressions for Q-R_H gives exactly

    beta=ell c+theta s,
    Y-G=theta c-ell s,
    ell=beta c+s(G-Y),
    theta=beta s-c(G-Y),
    k=c/s, r_B=beta+alpha k,
    A=L+(1-alpha)+beta k-ell/s.                       (6)

In particular the sign before beta c in the ell formula is
positive. No right/up-return height hypothesis is assumed.

**Theorem 1.1.** In this entire original feature, the actual HC
normal cannot point strictly northwest. Equivalently, the entire
HC feature at the actual upper-left H vertex

    W=(h-1,G)=(-X,G)

is impossible. The conclusion covers C-owned HC and, when CK is
shared, the entire free HC normal cone as well.

The H-owned E2 page is a separate complementary feature and is
not excluded by this theorem alone.

## 2. The actual K circle corner on the entire central domain

This lemma uses only (1)--(6), actual containment and physical K
boundary contact. It uses no page owner, C equation, K force
equation or assumption about K's degree.

First A>h. If h<=0 this follows from A>0. If h>0, then h<1
and the real H leaf equation gives

    A^2-h^2=d^2-1+2h-2h^2>0.

Consequently

    |R_H|^2=h^2+G^2=d^2+2(h-A)<d^2.                 (7)

Both minimum-t K vertices are at distance less than one from
R_H. Their norms are therefore less than d+1<R, so neither
can touch the circle.

Set a_m=R_H.m=-ch+sG. If a maximum-t, minimum-m vertex
were a circle point, comparison with the other endpoint of the
same unit m edge would require

    ell-a_m>=1/2.                                    (8)

This necessary comparison includes a possible equality of the
two endpoint norms. We exclude it on the whole angle domain.

Put t_0=beta/(1+alpha). The exact cubic bound (4) and

    (9/35)^3-1/60=173/514500>0

give t_0<9/35. Since beta=2t_0/(1+t_0^2),

    beta<315/653<29/60,
    29/60-315/653=37/39180>0.                        (9)

If c<=beta, then s>=alpha>6/7. Using ell<1,

    ell-a_m<1+c delta-sG
              <61/60-(6/7)(89/120)=8/21<1/2.

If beta<=c<1, (6) gives ell<beta/c. For the entire closed
interval [beta,1] consider the continuous function

    F(c)=beta/c+c delta-G sqrt(1-c^2).

It is strictly convex on the open interval, since

    F''(c)=2beta/c^3+G/(1-c^2)^(3/2)>0.

Its endpoint values satisfy F(beta)<8/21 and
F(1)=beta+delta<1/2 by (9). Convexity therefore gives
ell-a_m<F(c)<1/2 everywhere in this second interval too.
This contradicts (8).

Every actual K circle point is thus the same actual opposite
corner

    z_K=R_H+t+(1-ell)m,
    (z_K)_x=h+s-(1-ell)c,
    (z_K)_y=G+c+(1-ell)s.                          (10)

The argument retained the full ell,theta intervals and did not
infer a three-force concurrence at K.

## 3. The whole northwest HC owner cover

In the stated feature HC is a singleton at W. It cannot be
H-owned, since its normal is strictly oblique to H's frame.

If CK is also a singleton, its actual application at C is
different from the HC application. Otherwise the complete actual
C2 coincident-star calculation gives the retained radial-D
exception, and equality in

    R=|z_K|<=|P_C|+|z_K-P_C|
              <=R-sqrt(2)+sqrt(2)=R

would make the distinct contained K and C share a circle point.
This is impossible. The original common fixed-singleton selector
therefore supplies the actual HC and CK owners at those two
distinct fixed physical points. This is the complete fixed-point
part of the accepted page-owner source, and uses no additional
normal selection or premise on the central owner.

Thus HC is C-owned if CK is singleton. If CK is shared, C and
K are coframed and all its real shared means remain. HC can then
be C-owned or free. Sections 4--10 treat every C-owned HC case,
including shared CK. Section 11 treats the entire remaining free
HC/shared-CK placement without replacing its normal.

## 4. The signed transverse C coordinate is positive

Suppose C owns HC. Its complete actual frame is

    n_C=(-u,v), t_C=(v,u), u,v>0, u^2+v^2=1,
    C=W+[0,1]n_C+[-lambda,1-lambda]t_C,
    0<lambda<1,
    a=W.n_C=Xu+Gv>0,
    B_0=-W.t_C=Xv-Gu.                              (11)

Keep the original positive magnitudes omega for HC and gamma
for CK, with actual C-to-K normal w. The full actual C2 force is

    kappa_C z_C=omega n_C-gamma w.                  (12)

The genuine proper incoming line has
q_C=W+ell_C n_C=r_C z_C in C, r_C>0. The unique physical
C circle corner has nonzero own coordinates. Hence B_0!=0,
and its transverse circle coordinate has sign -B_0.

We first exclude the entire negative sign without a CK owner
restriction. If B_0<0, then Gu>Xv, and

    a-X=v[G-Xv/(1+u)]>0.

The actual point W+n_C belongs to C. Its squared norm exceeds
the containing radius by

    |W+n_C|^2-R^2=3/4-2A+2(a-d)
      >3/4-31/60-1/15=1/6>0,                     (13)

because d-X=delta+h<=2delta<1/30. This contradicts actual
containment. Therefore B_0>0 and the actual unique circle is

    z_C=W+n_C-lambda t_C,
    z_C.n_C=a+1, z_C.t_C=-B_0-lambda.              (14)

In particular its strictly larger-than-one-half transverse own
coordinate gives a<d. The following full bounds follow from the
same actual circle equation:

    a^2+B_0^2=d^2+1-2A,
    83/120<B_0<X<61/60,
    u<1/3, v>14/15, v>47/50, a>G,
    lambda^2+2B_0 lambda+2(a-G)
         =2d-11/4+4A<19/60,
    lambda<1/5.                                   (15)

Here B_0^2>1-2A>29/60>(83/120)^2, with reserve
71/14400. The function a(u)=Xu+Gsqrt(1-u^2) is increasing
up to the actual u, since its derivative has sign B_0>0.
At u=1/3 its value is greater than

    (59/60)/3+(89/120)(14/15)=51/50>61/60.

This proves u<1/3. Then v^2>8/9>(47/50)^2, with reserve
119/22500. Also

    a-G=u[X-G u/(1+v)]
       >(1411/1740)u>(4/5)u.                      (16)

The last reserve is 19/1740; the first lower bound uses
X>59/60, G<1 and 1+v>29/15. Finally, at lambda=1/5,
lambda^2+(83/60)lambda=19/60, proving its strict bound in
(15). Positivity of the left side of the circle identity also gives

    A>A_0:=43/240.                                 (17)

No proper-sign inference about K entered these bounds.

## 5. Both entire K-alone-owned CK possibilities are impossible

For a singleton CK, keep the original owner supplied in Section 3.
If K alone owns CK, its axis w must satisfy w.t>=0 by the
physical triangle side-normal rule with actual K-to-H normal -t.
Thus w is m,-m or t. The choice w=m is impossible by the same
rule at C, since n_C.m>0. Define

    D=vc-us, J=vs+uc>0, eta=1-lambda>4/5.          (18)

The transverse component of (12), using B_0>0, requires
w.t_C>0. This leaves precisely the following two full cases.

### 5.1. The axis w=t

The triangle rule at C gives D=n_C.t<=0. Equality makes the
C/K frames coincide with this axis contact and is incompatible
with a K-alone-owned singleton. Thus D<0. The actual C support
is Z=W+eta t_C, and its proper C2 line gives

    ell_C=eta(-D)/J.

The exact identity

    J-v=c[u-vc/(1+s)]>0

uses D<0, equivalently u>c. Hence
0<(-D)/J<u/v<5/14. Comparing the actual radial n_C and t_C
coordinates of q_C gives exactly

    B_0=a lambda+eta[(-D)/J](B_0+lambda).

Its right side is less than

    61/300+(5/14)(73/60)=893/1400<83/120,

with reserve 113/2100. This contradicts (15), and excludes
the whole axis regardless of its actual K-side position.

### 5.2. The axis w=-m

Now n_C.w=-J<0 and w.t_C=D>0. Its actual C support is
again Z=W+eta t_C, and the true C2 concurrence gives

    ell_C=eta J/D<=1.                              (19)

The final inequality is the genuine q_C in C property; it does
not assert strict interiority. Retain the actual K-owned side mean:

    Z=R_H+(1-ell)m+zeta t, 0<zeta<1.

Its two exact projections give

    ell=1-c+eta D,
    zeta=eta J-s.                                  (20)

Thus eta J>s and (19) gives D>=eta J>s. Since D<c, we have
c>s and c^2>1/2. Also ell>eta D>eta s. The original central
relation beta=ell c+theta s therefore gives

    beta k=beta c/s>eta c^2>2/5.                   (21)

Both real B leaves satisfy u_B>=beta r_B. They also have
x_B>=-delta: this is immediate for the aligned row; in the vertex
row, (3) gives
(1+x_B)^2>d^2-4delta=(1-delta)^2 with 1+x_B>0.
Therefore, without restricting either original leaf interval,

    L=beta x_B+alpha u_B
      >-beta delta+alpha beta r_B
      >-1/120+alpha^2 beta k
      >-1/120+(3/4)(2/5)=7/24>31/120>A.             (22)

The final reserve is 1/30. This contradicts (2), and removes the
entire second axis. No K force equation was used in either exit.

## 6. The entire C-owned CK chart and its unchanged mean

If C owns CK, (12) has nonzero transverse component, so w is
one of +/-t_C. The minus sign cannot occur: the actual point
R_H in K satisfies

    R_H.(-t_C)=B_0-v<B_0+lambda=max_C(-t_C),

contradicting the opposite support inequality for a contact in
that direction. Thus w=t_C. This covers every shared CK as well
as the remaining singleton owner.

Put z=1-ell, so 0<z<1. Since t_C.t=J>0 and t_C.m=-D,
a negative D would make the sole minimum-t_C point of K be
S=R_H-ell m. But

    S.n_C=a-u-ell J<a,

so S does not belong to C. Consequently D>=0.

For D>0 the actual CK point is R_H+z m. Its unchanged C-side
representation gives

    Z=W+eta t_C+rho n_C,
    eta=v-zD, lambda=1-v+zD,
    rho=zJ-u, 0<=rho<=1.                           (23)

The relaxed closed rho bounds retain its strict singleton position.
For D=0 the frames coincide, n_C=m and t_C=t, so u=c and
v=s. Their actual shared segment has the complete representation

    eta=v, lambda=1-v,
    Z=W+eta t_C+rho n_C,
    0<=rho<=z-u, z>u.                              (24)

Indeed its C-side n_C interval is the intersection of [0,1] with
[-u-ell,z-u]. Its positive physical length gives exactly z>u.
The actual force mean retains every point of the interval (24).

Both physical types have the same necessary relations

    lambda=1-v+zD,
    gamma/omega=(B_0+lambda)/(a+1)=B_0/(a+rho),
    a+rho=B_0(a+1)/(B_0+lambda).                    (25)

The first force ratio is from the two own-axis projections of
(12). The moment ratio uses precisely
det(W,n_C)=-B_0 and det(Z,t_C)=-(a+rho). In particular
rho is never replaced by the singleton value in the shared row.

## 7. A uniform convex circle comparison gives c<1/4

Combining the exact circle identity with (15)--(16) gives

    (83/60)lambda+(8/5)u<4A-43/60,
    lambda+u<(240A-43)/83.

By (23)--(24),

    zvc=lambda-(1-v)+zus<lambda+u.

Since v>47/50, the actual quantity j=zc satisfies

    0<j<q(A):=(12000A-2150)/3901
               =kappa(A-A_0), kappa=12000/3901>3,
    A_0=43/240<A<A_1:=31/120,
    q(A_1)=Q_0:=950/3901<1/4.                     (26)

The actual K circle from Section 2 is

    z_K=(h+s-j, 1-A+c+(j/c)s).                    (27)

All divisions by c here are legitimate because BK is strictly
northwest in the feature being proved.

### 7.1. The whole interval c>=1/2

Here s<=sqrt(3)/2<13/15 and j<Q_0<1/4, so

    |h+s-j|<1/60+max(s,j)<53/60.

The actual vertical coordinate is positive and

    1-A+c+(j/c)s
      <1-A+c+2q(A)s
      <=1-A+sqrt(1+4q(A)^2).

The final function is convex in A on [A_0,A_1]. At A_0 its
value is 437/240<223/120. At A_1 it is less than

    89/120+67/60=223/120,

because

    (67/60)^2-(1+4Q_0^2)
       =532625089/54784083600>0.

Hence the real circle point would satisfy

    R^2=|z_K|^2<(53/60)^2+(223/120)^2<17/4,

with final reserve 47/2880. This excludes the entire interval.

### 7.2. The whole interval 1/4<=c<=1/2

The actual horizontal coordinate is positive, because
h+s-j>-1/60+6/7-1/4>0. Replace only h by its strict upper
bound 1/60 in its squared norm. The real H equation gives
A^2<=4delta and therefore

    R^2>17/4+A^2.

Consider the continuous comparison

    F(A,c,j)=(1/60+s-j)^2
              +(1-A+c+(j/c)s)^2-A^2.              (28)

For fixed A,c it is convex in j. By (26), its maximum on the
necessary closed j interval occurs at 0 or q(A).
At j=0, simply omitting -A^2 gives

    F(A,c,0)<(61/60)^2+(3/2)^2<17/4,

with reserve 3479/3600. At j=q(A), F is convex in A:
its A^2 coefficient is

    kappa^2/c^2-2kappa s/c
       =(kappa/c)(kappa/c-2s)>0.

Its maximum therefore occurs at A_0 or A_1. The first endpoint
is the already treated j=0. At the other endpoint set

    h_*=1/60, G_*=89/120,
    F_1(c)=(h_*+s-Q_0)^2
               +(G_*+c+(Q_0/c)s)^2-A_1^2.

The exact derivative on the entire interval is

    F_1'(c)=2G_*-2Q_0^2/c^3-2h_*c/s
                        -2G_*Q_0/(c^2s)<0.        (29)

Indeed c^2s<=sqrt(3)/8<7/32<Q_0; the first and last terms
already have strictly negative sum. All other displayed terms
are negative too. Thus the maximum is at c=1/4.

There s=sqrt(15)/4<31/32, and both squared coordinates in
(28) are positive. Consequently

    F_1(1/4)
      <(1/60+31/32-Q_0)^2
         +(89/120+1/4+4Q_0(31/32))^2-(31/120)^2
      =14828289979129/3506181350400
      =17/4-72980760071/3506181350400.              (30)

This contradicts (27)--(28) and the strict R^2-A^2>17/4.
Every endpoint of the two angle intervals was retained.
We have therefore proved uniformly

    c<1/4, k=c/s<1/sqrt(15)<4/15.                 (31)

The argument used two convexity comparisons and one derivative
sign over complete continuous intervals, with no coefficient
certificate or angle sampling.

## 8. Both real B leaves make the actual central displacement small

The actual relation r_B=beta+alpha k and both rows (3) give
u_B>=beta r_B>beta^2. Combining x_B<=delta with h>=-delta
therefore yields

    beta^3<delta(1+alpha)<1/30,
    beta<1/3, alpha>14/15, alpha^2>8/9.            (32)

Define the auxiliary positive scalar

    epsilon=1-alpha, t_0=beta/(1+alpha),
    b_*=L+epsilon+beta k=A+ell/s>A.                (33)

We reproduce the complete local two-leaf calculation from the
accepted vertical-central source, using only (2)--(4),(31)--(32):

    (1+h)^2+b_*^2<d^2.                            (34)

For the actual vertex row, eliminating its real B3 parameter
u_B=(beta+alpha k)(beta+L) with u_B=alpha L-beta h gives

    d^2-(1+h)^2-b_*^2
      =2t_0(1-k)L
        +epsilon[2beta-epsilon
                   +2(alpha-beta)k-(1+alpha)k^2].  (35)

The first term is positive, epsilon<beta, and

    2(alpha-beta)-(1+alpha)k
       >2(14/15-1/3)-2(4/15)=2/3>0.

Thus (35) is positive on the entire genuine vertex row.

For the actual aligned row put r=r_B=beta+alpha k. Its original
coordinates remain h=alpha delta-beta^2r and
L=beta delta+alpha beta r. Exact expansion gives

    [d^2-(1+h)^2-b_*^2]/beta^2
      =2delta[(1-beta)/(1+alpha)-k]+F_B,
    F_B=2r-3r^2+2rt_0-(t_0+k)^2,
    r=t_0+alpha(t_0+k).                           (36)

The bracket in the delta term exceeds 1/15. Also
0<t_0<r<3/5, r<2t_0+4/15, and
(t_0+k)^2<(9/8)(r-t_0)^2. The comparison

    f(r,t)=2r-3r^2+2rt-(9/8)(r-t)^2

is strictly increasing for 0<=t<r. For 0<r<=4/15 this gives
F_B>f(r,0)>=9r/10>0. For 4/15<=r<3/5, use
t_0>(r-4/15)/2 and obtain

    F_B>B(r)=(26/15)r-2r^2-(9/32)(r+4/15)^2,
    B''=-73/16,
    B(4/15)=6/25, B(3/5)=87/800.

The concave quadratic is positive throughout that closed interval.
This proves (34) for the whole aligned row, including every actual
allowed original slider. No aligned vertex was substituted.

Now compare (34) with (1-h)^2+A^2=d^2 and b_*>A. Their
difference gives h<0. Their sum gives

    A+b_*<2sqrt(d^2-1)<11/30.

Together with A>A_0 and (33), this proves

    h<0, A<11/60, G>49/60,
    ell/s=b_*-A<11/30-2A<1/120,
    ell<1/120, z=1-ell>119/120.                   (37)

These are consequences of both original radial equations and the
actual central position; they are not imposed on the original chart.

The unchanged C circle budget is now less than 1/60. By
(15)--(16) and zvc<lambda+u,

    lambda<1/83, u<1/96,
    c<(120/119)(50/47)(1/83+1/96)
       =22375/928438<1/40,
    s>99/100.                                     (38)

The last c reserve is 16719/18568760; the s comparison follows
from 1-1/1600>(99/100)^2. All denominators have proved positive
lower bounds.

## 9. The actual K circle has a large horizontal-to-vertical ratio

The physical lemma (10), with the full actual z=1-ell, now gives

    (z_K)_x=h+s-zc
       >-1/60+99/100-1/40=569/600>9/10.

Its height is positive and at most R<25/12. Thus the actual
circle direction obeys

    (z_K)_x/(z_K)_y>54/125.                       (39)

No individual pair force or whole K force law was omitted in
identifying this corner; Section 2 was entirely physical.

## 10. The full original H/B moments and K3 give the opposite ratio

Keep the real mean rho from (23) or (24), and put D_C=a+rho.
The original C2 identity (25), even with its loose lambda<1/5,
gives

    D_C=(a+1)/(1+lambda/B_0)
      >(209/120)/(1+24/83)
      =17347/12840>1>G.                           (40)

Let mu_HB,tau,nu be the actual positive HB,HK,BK magnitudes.
The genuine H and B leaves act on radial lines through the origin
and have zero origin moment at their unchanged applications. The
complete H4 and B3 moments are therefore

    L mu_HB+tau(hc-Gs)-B_0 omega=0,
    -L mu_HB+nu D_Q=0,
    D_Q=det(Q,m)=(h+beta)s+Yc>0.                  (41)

No H3 equation has been used. Combining them with the full C2
mean identity gives

    gamma D_C=nu D_Q+tau(hc-Gs)>0.                (42)

The unchanged true K3 force, with all three pair loads present, is

    kappa_K z_K=tau t+nu m+gamma t_C.              (43)

Eliminating only its horizontal central term with (42) gives the
exact identity

    kappa_K G(z_K)_x
      =nu(D_Q-Gc)+tau hc+gamma(Gv-D_C).            (44)

The actual two-side central relations (6) give

    D_Q-Gc=hs+beta/s-ell c/s<beta/s.

By h<0 and (40), both other terms in (44) are strictly negative.
Hence kappa_K G(z_K)_x<nu beta/s. The full vertical component
of (43) is kappa_K(z_K)_y=tau c+nu s+gamma u>nu s.
All quantities divided by are positive, so

    (z_K)_x/(z_K)_y<beta/(Gs^2)
      <(1/3)/[(49/60)(99/100)^2]
      =200000/480249<54/125.                      (45)

The final reserve is 933446/60031125. This contradicts (39)
and excludes the whole C-owned HC feature, with both genuine
B leaves and the entire actual shared rho interval intact.

## 11. The entire free-HC/shared-CK corner is also impossible

By Section 3, a remaining free HC requires CK to be shared.
Use the actual m,t coordinates relative to R_H. K is

    [-ell,1-ell] x [0,1],

and the actual H point W has coordinates (c,-s). A free HC
normal means W is also an actual C vertex. The four signed
shared translations of a coframed unit are exhaustive.

Across the maximum-t side, C has t>=1, whereas W has t=-s.
Across the minimum-m side, C has m<=-ell<0, whereas W has
m=c>0. Both placements miss W.

Across the minimum-t side, C has t in [-1,0]. Since -s is
strictly between those endpoints, W cannot be a C vertex.
That placement can only belong to the already treated C-owned
HC feature, not the actual free normal now under consideration.

Across the maximum-m side write

    C=R_H+[1-ell,2-ell]m+[zeta,zeta+1]t,
    -1<zeta<1.

For W to be a vertex, its m coordinate c<1 must be the lower
endpoint, so ell=1-c. Its t coordinate -s must likewise be the
lower endpoint: the upper-endpoint choice gives zeta=-s-1<-1,
inconsistent with positive physical shared length. Thus the full
remaining placement is exactly

    ell=1-c, zeta=-s,
    C=W+[0,1]m+[0,1]t,
    w=C-to-K=-m.                                  (46)

Retain the actual free H-to-C normal n. Since its actual minimum
on C is the vertex W and it is not a C axis,

    n.m>0, n.t>0.

The full C2 force is now kappa_C z_C=omega n+gamma m.
Both own circle coordinates are strictly positive. Actual
containment therefore makes its actual circle corner

    z_C=W+m+t.

Section 2, with 1-ell=c, simultaneously identifies the actual
K circle as z_K=R_H+c m+t. Direct subtraction gives the exact
whole-angle identity

    |z_C|^2-|z_K|^2
      =-2h(c+s^2)+2Gs(1-c)+2c+(1-s)^2.             (47)

The first term is greater than -1/15, since h<1/60 and
c+s^2<2; this bound does not presume the later h<0 from the
C-owned branch. If c<=1/2, then s>6/7 and 1-c>=1/2, so
the second term is greater than 89/140. The difference is
therefore greater than 239/420>0. If c>=1/2, the third term
is at least one, and the difference is greater than 14/15>0.

Both actual circle norms equal R, contradicting (47). The full
actual free cone was kept through its force equation; neither its
direction nor any shared CK application was reselected.

## 12. Complete original feature and exact review boundary

The accepted full H-owned HB theorem supplies (1)--(4), both
real B leaf rows, the lower H leaf, positive physical page heights
and actual normal signs before any central restriction. The full
central singleton theorem and the actual loaded-page separation
theorem retain HK and HC as their original applications.
K ownership and northwest BK then give the entire exact central
chart (5)--(6), with both strict actual side sliders.

Section 2 is a reusable physical corner lemma on that whole chart.
Sections 3--10 exclude all C-owned northwest HC, first covering
both K-alone-owned CK axes and then the entire C-owned CK
feature including the shared equality and both actual mean
endpoints. Section 11 exhausts the only additional free-HC
possibility through all four physical shared CK translations.

This proves the complete stated northwest page exclusion. The
complementary H-owned E2 page is not claimed here. No original
gate, load, mask, extra unit, actual mean or true degree is removed
by an unproved inference. No ledger, remote source, Lean file or
CI workflow is edited. There is no new computational packet.

The complete direct sources and their precise use are:

| Complete input | SHA256 | Scope used |
| --- | --- | --- |
| SS_HUB_TIP_H_OWNED_SINGLETON_VERTICAL_C_OWNED_PAGE.md | e80e37f301f1ac7e492cf9650a5f7f43295639aa843b548dd61c8e633d5c5660 | Whole-owner Theorem 1.1 only: exact genuine H/B chart, positive K/C physical page and actual normal signs; no vertical central-owner conclusion imported |
| TWO_S_ROOT_TRIANGLE_OWNED_SINGLETON_ADJACENT_PORT_NORMAL_FORM.md | 2397a468e15cb7043a4774f4ce5bfc3dabb34b0d85937991f444819b4cf2ac88 | Entire real B leaf cover, actual B3 parameter, cubic angle bound and original K-owned BK join |
| SS_HUB_TIP_CENTRAL_SINGLETON_DISTINCT_FRAME_NORMAL_FORM.md | 89ff6eee18061f7ef57fea5acd8da87ce42ff3c24185d478da113c181e77fae0 | Whole physical singleton HK and distinct H/K frames |
| LOADED_BOUNDARY_PAGE_DISTINCT_ROOT_APPLICATIONS.md | 3401781bde8a3d908e8c869f179da8618189fb680979e3ff6ca44d7179a48168 | Original actual HK/HC applications stay distinct, including all shared means |
| UNIT_TRIANGLE_OWNED_SINGLETON_SHARED_RETURN.md | cda14432fafffe1985969229dccd7a15d1d04581b4e80e090862b9c79a1b942b | Only the complete two-fixed-singleton C2 owner argument in Section 5; shared CK is independently exhausted above |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing common selector at two actual distinct fixed C2 singleton applications, with no new selection |
| SS_HUB_TIP_H_OWNED_SINGLETON_VERTICAL_CENTRAL_EXCLUSION.md | 74fb39f76726e827438966dc324a03f50956f99169b1008f59f40e909a697619 | Provenance of the fully reproduced local two-leaf calculation; no vertical owner, strict central gap or K3 conclusion is assumed |
| SS_HUB_TIP_RADIAL_PAGE_FULL_EXCLUSION.md | 2bf0e377d1c17d28c7e49742b418ea6a60a8b9fbe7dad56249e73cf0e96a8d9b | Whole original physical uniqueness of C |
| SS_HUB_TIP_LOADED_HUB_PHYSICAL_UNIQUENESS.md | ce1c5e44c1ac9334775e0775323830ea6eea0d63a56ebfb4f294960d43da79af | Whole original physical uniqueness of K and original radius domain |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Genuine true-C2 proper concurrence and positive radial sign with physical boundary neighbor K |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual physical triangle side-normal signs for every original owner |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full unchanged H4/B3/C2/K3 equations, moment conventions and actual shared means |
| FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md | a33b15a4a3e7894c256ee1877edfb47f6241fd208558765267113e56e12a1b4e | Full original graph, all positive loads, true degrees and all nine physical units |

The immediately used new complete acceptance records are

| Full independent review | SHA256 |
| --- | --- |
| REVIEW_HIGH_ROOT_SIDE_AND_H_OWNED_VERTICAL_PAGE_TOPOLOGY_INDEPENDENT_2026_10_27.md | fc82d3e7a25588237e24fbde172da6de62de9e7045e7e709f2cefca79610e19f |
| REVIEW_SS_HUB_TIP_H_OWNED_VERTICAL_CENTRAL_CERT_INDEPENDENT_2026_10_27.md | f0077da6486eccbb64db3e9f337692cfc71097314cb5580b0f9a678d5a36101d |
| REVIEW_LOADED_BOUNDARY_PAGE_DISTINCT_APPLICATIONS_CERT_INDEPENDENT_2026_10_27.md | 8611ae03bb7abd3fb636ac4f219bba951592c138152d9dba38ad83b2c76c173c |

These accepted inputs do not substitute for the separate complete
independent review required for this new whole feature proof.
