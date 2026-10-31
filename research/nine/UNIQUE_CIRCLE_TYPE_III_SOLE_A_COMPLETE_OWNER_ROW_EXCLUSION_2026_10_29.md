# The entire genuine sole-A Type III owner row is excluded

Date: October 29, 2026 UTC. Author: root-triangles continuation, with
the large-p derivative supplied by roofs and the frozen small-p theorem
authored by roofs.

**Status: complete proposed hand theorem, frozen for full independent
review.** This source closes the entire genuine sole-A Type III row
g=nA. The actual upper and lower exterior points exclude every remaining
p>=2/5 and every genuine relative tilt k. The full small-p theorem then
supplies the exhaustive original owner-row join, including p<=0.

The middle interval is treated by a sum of two fixed projections for
0<=k<=1/5 and by one increasing projection for k>=1/5. All comparisons
are analytic on full continuous intervals, with every original mean
retained. No numerical pose, orientation mesh or packing certificate
is used. Neither complete D02 load family is declared closed.

## 1. Exact original physical domain and full stars

Retain all nine actual squares, the unchanged circle origin, every
original positive force, selected normal, complete application or mean,
true degree, physical circle mask and individual zero coefficient.
Throughout,

    79/40<=R<=sqrt(1105)/16,
    R<1039/500,
    (1039/500)^2-1105/256=6711/4000000>0.           (1)

The unique-PHYSICAL-circle Type III chart has

    V=[a-1,a] x [b-1,b], Z=(a,b), a>b>1/2,
    P1=(a-1,b), P0=(a-1,b-1), |Z|=R,
    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3 and V is loaded true2. The original roof
normals are strict at the displayed V vertices and owned by the hubs.
In A's actual oriented orthonormal frame put

    h=nA=(c,-s), e=tA=(s,c), c,s>0, c^2+s^2=1,
    nD=K h+H e, tD=-H h+K e,
    H>0, K<0, H^2+K^2=1.

The genuine sole-A interface is the original g=h. Its actual geometry
and original applications are

    A=P1-[0,1]h+[-r,1-r]e, 0<r<1,
    D=P0-[0,1]nD+[-t,1-t]tD, 0<t<1,
    W=P1-(S/H)e=P0+(1-t)tD,
    t=1-s/H, S/H<r<1, H>s, H>S,
    pi/2<alpha+beta<2pi/3, beta>pi/4.              (2)

S is nD's original vertical component. This is a genuine singleton:
W lies in the relative interior of A's side and is the strict D
vertex specified by the original physical feature. No shared-AD mean
is inserted into (2).

Let mu,nu,rho>0 be the original AV,DV,AD magnitudes. Their complete
original V2, A3 and D3 equations imply

    mu h+nu nD=kappa Z, kappa>0,
    mu det(P1,h)+nu det(P0,nD)=0,

    F_B=-(mu+rho)h,
    Q_B=P1-h-z_A e, z_A=rho(S/H)/(mu+rho),

    F_C=rho h-nu nD,
    Q_C=P0-nD-t tD,
    nu t=rho(H+K)>0.                             (3)

Q_B is the actual original back-side point or full mean fixed by the
entire A torque. Q_C is the actual strict D support vertex fixed by
the full exterior force. The original equations at B,C and every
other body remain; no reduced equation is imposed on an exterior unit.

Use the following identities of those original data:

    k=-K/H, J=sqrt(1+k^2), H=1/J, K=-k/J,
    p=(Z.h)/(Z.e)=(mu/nu)J-k,
    x=p+1, v=1+k, T=sqrt(x^2+v^2),
    c=x/T, s=v/T, Y=R/sqrt(1+p^2),
    Z=(pY,Y), P1=(pY-c,Y-s),

    0<k<1/sqrt(3), p>-k,
    u=S/H=c+ks<r<1, sJ<1,

    eta=(1+k-sJ^3)/(1-k),
    N=eta-k=J^2(1-sJ)/(1-k)>0,
    z_A=uN/(p+k+N)=u(eta-k)/(p+eta).               (4)

The scalar N is not the actual intervening unit, denoted N_original
in the literal callers below. The quantities p+k, p+eta and every
physical denominator in (4) are positive. The full torque equation,
not a chosen contact coordinate, determines z_A.

The useful original geometric consequences are

    k<eta<1,
    k<(1-c)/s=s/(1+c),
    (2p+1)k+k^2+k^3<1.                           (5)

For completeness, u<1 gives c<1-ks. Squaring positive sides yields
s>2k/(1+k^2); hence sJ^3>2k and eta<1. Its lower bound is N>0.
The final inequality follows by squaring x+kv<T and dividing by
v>0. These are necessary domains of the original feature, not
realizability assertions.

## 2. Actual exterior points and unchanged projections

A real unit square with minimum support at an actual point or full
side mean P in unit direction n contains P+n. In each of its own
unit coordinate intervals, every nonzero component of n moves inward
by at most one; a zero component preserves the original coordinate.
This includes every support owner and both side-mean endpoints.

Apply that fact to (3). The actual B and C contain

    X_B=(pY-c-2, Y-s-z_A),

    X_C=(pY-c+(1+k)/J+eta/sqrt(1+eta^2),
         Y-c-(1+k)s+(k-1)/J-1/sqrt(1+eta^2)).     (6)

To check the second expression directly, in A's frame
nD=(-k/J,1/J), tD=(-1/J,-k/J), t=1-sJ, and
P0=(pY-c+s,Y-s-c). Thus Q_C has coordinates
(pY-c+(1+k)/J, Y-c-(1+k)s+(k-1)/J).
Its actual outward D-to-C vector is a positive multiple of
eta*h-e, giving precisely the displayed actual point after adding
its unit normal.

Define the fixed auxiliary unit directions and projections

    n_B=(-12,5)/13, n_C=(21,-20)/29,
    P_B=n_B.X_B, P_C=n_C.X_C, F=P_B+P_C,
    T_C(eta)=(21eta+20)/sqrt(1+eta^2).

Containment requires P_B<=R and P_C<=R. Their exact scaled formulas are

    13P_B=24+12c-5s-5z_A
               +R(5-12p)/sqrt(1+p^2),

    29P_C=R(21p-20)/sqrt(1+p^2)
               -c+20(1+k)s+(41+k)/J+T_C(eta).   (7)

The directions are geometric proof directions. They do not replace
any extracted stress normal, and the actual squares remain present.

Here and below a prime in a fixed-p comparison means differentiation
with respect to the scalar k. The exact derivatives are

    c'=-cs/T, s'=c^2/T,
    eta'=[2-sJ(A_k+B_k c^2)]/(1-k)^2,
    A_k=1+3k-2k^2, B_k=(1-k)J^2/(1+k),
    T_C'(eta)=(21-20eta)/(1+eta^2)^(3/2)>0.       (8)

All scalar comparison paths retain the required signs. At fixed p,
s and J increase with k. Also

    u'=s+c(kc-s)/T=s(1-c/T)+k c^2/T>0,

since T>1>c whenever p>=2/5. Thus decreasing k from its original
value preserves sJ<1 and u<1, and hence k<eta<1. No auxiliary
value is asserted to describe a different physical packing.

## 3. Every p>=1/2 is excluded by C

For p>=1/2, (5) implies k<2/5: at k=2/5 the increasing left side
with p=1/2 is 128/125>1. Thus throughout the comparison path

    s<7/10, c>7/10, J<27/25.

For example the worst s comparison uses
s^2<=196/421<49/100, while c^2>=225/421>49/100.
Since 0<=k<=2/5,

    B_k<=1-k,
    A_k+B_k c^2<=2+2k-2k^2<=62/25.

Consequently the eta' numerator in (8) is strictly positive:

    2-sJ(A_k+B_k c^2)
       >2-(189/250)(62/25)=391/3125>0.           (9)

The derivative of the geometric part of 29P_C is exactly

    d[-c+20(1+k)s+(41+k)/J]/dk
      =s[40-20s^2+(p+1)/T^2]+(1-41k)/J^3
      >30s-41k.

The genuine inequality in (5) and c>7/10 give
k<s/(1+c)<10s/17. Hence this derivative is greater than
(100/17)s>0. The T_C contribution also increases by (8),(9), so
P_C is strictly increasing on the whole scalar path from zero to
the actual k.

At k=0 its expression is exactly the shared-source comparison with
m=p and q=1-s_0, where

    T_0=sqrt((p+1)^2+1), c_0=(p+1)/T_0,
    s_0=1/T_0, eta_0=1-s_0.

Section 4 of the complete shared-A source proves that this endpoint
projection exceeds R for every p>=1/2. Its increasing-p calculation
is valid on the whole interval, and its exact endpoint excess at
p=1/2 is greater than 1/8 in the 29-scaled expression. We use this
scalar endpoint inequality, not a physical conversion of the genuine
sole owner into a shared owner. The original k and means stay in (3).

This excludes every original p>=1/2, including p=1/2.

## 4. The entire middle band and its comparison geometry

It remains, after the frozen small-p theorem, to consider

    2/5<=p<=1/2.                                (10)

The following formulas are proved with both endpoints retained so
the original joins are explicit. Equation (5) implies k<9/20,
because even at p=2/5 the increasing polynomial exceeds one at
k=9/20. It is also enough to use the weaker p>=1/3 implication
already proved in the small-p source.

Throughout this whole middle-band comparison domain,

    T<21/10, 2/3<c<5/6, s<3/4,
    c^2<7/10, J<11/10.                          (11)

Indeed x is between 7/5 and 3/2 and v between 1 and 29/20.
For the two lower/upper frame comparisons use
c^2>=784/1625>4/9 and s^2<=841/1625<9/16.
The upper c comparison follows from c^2<=9/13<25/36.
The other bounds follow by squaring positive quantities.

The small-k rectangle needed first is

    2/5<=p<=1/2, 0<=k<=1/5.                     (12)

There the stronger bounds are

    T<2, c^2>=49/85, c^2<=9/13,
    s<2/3, J<51/50.                             (13)

All explicit scalar expressions are defined on this whole rectangle.
In particular sJ<1 there. Along each path from a genuine point the
remaining original inequalities are preserved as explained after (8).

## 5. The actual B mean decreases throughout the whole small-k rectangle

This section proves z_A'<0 on (12). It uses exact continuous
derivative bounds, not values at finitely many tilts.

### 5.1. The entire derivative interval 1<eta'<6/5

First prove eta'>1. At fixed x=7/5, let

    f_0(k)=J/sqrt((7/5)^2+(1+k)^2).

The actual J/T is at most this function. Direct differentiation gives

    f_0'=[(49/25)k+k^2-1]/(J T^3)<-1/12

on 0<=k<=1/5. For an exact uniform check, the numerator is at most
-71/125, while J<51/50 and T<37/20; and

    852/125-(51/50)(37/20)^3=143097/400000>0.

Also f_0(0)=5/sqrt(74)<7/12, with integer squared reserve 26.
Integration gives

    J/T<(7-k)/12,
    sJ<(1+k)(7-k)/12.                           (14)

Using c^2<=9/13 in (8), the subtracted product is strictly smaller
than

    (7-k)[22+43k+22k^2-35k^3]/156.

Its difference below 1+2k-k^2 has numerator

    (1-5k)(2+43k-52k^2+7k^3)>=0.                (15)

The second factor is positive throughout [0,1/5], and the first is
nonnegative. The strict inequality in (14) retains strictness even at
k=1/5. Thus sJ(A_k+B_k c^2)<1+2k-k^2, which is precisely eta'>1.

For the upper bound, eta' increases with p on (12). To check this
sign directly, keep k fixed and write the subtracted factor as

    J*s[A_k+B_k(1-s^2)].

Its derivative in s has positive bracket
A_k+B_k-3B_k s^2>=A_k-B_k/3>=2/3, using (13), A_k>=1 and
0<B_k<=1. Since s decreases with p, eta' increases with p.
It therefore suffices to bound eta' at p=1/2.

At that endpoint c^2>=25/41 and

    J/T>=sqrt(104/369)>53/100,
    104/369-(53/100)^2=3479/3690000>0.

The first ratio decreases with k over [0,1/5], since its derivative
has the sign of (9/4)k+k^2-1<0. Its lower endpoint value in the
displayed inequality is at k=1/5.

Consequently sJ(A_k+B_k c^2) is greater than

    (53/100)[(1+k)A_k+(25/41)(1-k)J^2].

Subtracting 2-(6/5)(1-k)^2 from this lower bound gives

    [218-2473k+8418k^2-5671k^3]/4100.

This is strictly positive throughout [0,1/5]. Indeed its numerator
is at least the quadratic

    218-2473k+(36419/5)k^2,

whose global minimum is

    218-2473^2/[4(36419/5)]
       =1178723/145676>0.                       (16)

This proves eta'<6/5. The complete small-k interval therefore has

    1<eta'<6/5, 0<N'=eta'-1<1/5.                (17)

At k=0, N=1-s_0 lies strictly between 2/5 and 9/20 on (10).
The two endpoint squared comparisons are 666>625 and 1600>1573.
Integrating (17) gives the whole-rectangle estimates

    2/5<N<49/100,
    p+k+N<119/100.                              (18)

### 5.2. The whole logarithmic derivative bound for u

In (4), u=(x+k(1+k))/T. Its exact logarithmic derivative is

    L_u:=u'/u=(1+2k)/(x+k(1+k))
                    -(1+k)/(x^2+(1+k)^2).      (19)

This expression decreases with x for fixed k. Its x derivative is

    -(1+2k)/(x+k(1+k))^2
       +2x(1+k)/(x^2+(1+k)^2)^2<0.

For the strict sign, use 2x(1+k)<=x^2+(1+k)^2 and

    [x+k(1+k)]^2<(1+2k)[x^2+(1+k)^2].

The latter follows by bounding 2kx(1+k) by
k[x^2+(1+k)^2]; its remaining difference is positive for
0<=k<=1/5. Thus the maximum in x is at 7/5.

At x=7/5, L_u increases with k on [0,1/5]. Differentiating (19),
the first term's derivative is at least 825/1681, while the second
term's derivative is at most 25/74. Their positive difference is
19025/124394. Hence the whole maximum is

    L_u<=L_u(7/5,1/5)=349/697<51/100,
    51/100-349/697=647/69700>0.                 (20)

### 5.3. Strict decrease of the unchanged original mean

The exact formula z_A=uN/(p+k+N) is positive. Its logarithmic
derivative satisfies

    (p+k+N) z_A'/z_A
       =(p+k)N'/N+(p+k+N)u'/u-1.

Using (17),(18),(20) and p+k<=7/10, its right side is less than

    7/20+(119/100)(51/100)-1=-431/10000<0.        (21)

Thus z_A'<0 throughout the entire rectangle (12), including the
one-sided comparison derivatives at its boundary. No global decrease
for larger k is asserted or used.

## 6. The summed projections increase with small k

For fixed p in (10), differentiate the complete actual expressions
(7). The radial terms are constant in this comparison. One obtains

    377 F'
      =335c'+(115+260k)s'+260s
           +13(1-41k)/J^3
           -145z_A'+13 T_C'(eta)eta'.            (22)

The final two terms are positive by (5),(17),(21). The geometric
part is strictly positive over the whole rectangle (12), without
using them. From (13), cs<=1/2 and T<2,

    335c'+(115+260k)s'+260s
      =[ -335cs+(115+260k)c^2+260(1+k)]/T
      >5399/68+(3484/17)k.

Also 13(1-41k)/J^3>-533k. Therefore

    377 F'>5399/68-(5577/17)k
              >=4687/340>0                     (23)

for every 0<=k<=1/5. Thus each original summed projection in this
domain is bounded below by its k=0 scalar endpoint.

## 7. The whole middle-band endpoint k=0 already exceeds 2R

At k=0, write

    c_0=(p+1)/sqrt((p+1)^2+1),
    s_0=1/sqrt((p+1)^2+1), eta_0=1-s_0,
    z_0=c_0 eta_0/(p+eta_0),
    T_M(q)=(273q+260)/sqrt(1+q^2).

These are the endpoint values of the same scalar functions, with
the genuine sole-A torque limit. In particular this is the shared
comparison mean z=0; a different shared mean is not substituted.
The exact identity from (7) is

    377(F(p,0)-2R)
      =1229+335c_0+115s_0-145z_0+T_M(eta_0)
        -R[754+(75p+115)/sqrt(1+p^2)].           (24)

The function z_0 decreases over the whole interval (10). Its
derivative numerator is

    p eta_0' c_0+eta_0 c_0'(p+eta_0)-eta_0 c_0.

Here eta_0'=c_0 s_0^2, c_0'=s_0^3, p<=1/2,
2/5<eta_0<1/2, c_0>4/5 and s_0^3<1/4. The first two terms are
each strictly smaller than 1/8, while the last exceeds 8/25.
The numerator is therefore less than -7/100<0.

The following complete interval bounds can now be taken at their
appropriate scalar endpoints:

    c_0>8137/10000, s_0>5547/10000,
    z_0<1041/2500,
    eta_0>4187/10000,
    T_M(eta_0)>34526/100,
    (75p+115)/sqrt(1+p^2)<136401/1000.            (25)

Here c_0 and eta_0 increase with p, s_0 decreases, z_0 decreases
as just proved, and T_M increases for 0<q<1. The final ratio
increases on (10) because its derivative has numerator 75-115p>0.
For full exact checks, at p=2/5 one has c_0=7/sqrt(74),
eta_0=1-5/sqrt(74), and

    z_0=35(sqrt(74)-5)/(518-25sqrt(74)).

The positive comparisons supporting (25) are

    49*10000^2-8137^2*74=403094,
    4*10000^2-5547^2*13=283,
    976738^2-74*113525^2=310624394,
    74*5813^2-50000^2=531706,
    (3743051*100)^2-34526^2*117530969
         =2142024438956,
    (136401/1000)^2-305^2/5=232801/1000000.

For the z_0 comparison, its denominator is positive and the stated
inequality reduces to 113525sqrt(74)<976738. For T_M, its value
at 4187/10000 is 3743051/sqrt(117530969). The final ratio at
p=1/2 is 305/sqrt(5). Thus every bound in (25) follows from the
displayed positive comparisons and its complete interval monotonicity.

Substitute (1),(25) into the exact sum (24):

    377(F(p,0)-2R)
      >1229+335(8137/10000)+115(5547/10000)
         -145(1041/2500)+34526/100
         -(1039/500)[754+136401/1000]
       =4361/500000>0.                          (26)

Equations (23),(26) give F>2R throughout (10), 0<=k<=1/5.
But actual containment of both points would give F<=2R. This
excludes the entire small-k part of the middle band, with all its
joining endpoints included.

## 8. The whole larger-k middle band is excluded by C alone

Now suppose (10) and k>=1/5. All actual k still satisfy k<9/20.
First, P_C increases with k throughout the comparison domain.
By (11),

    A_k+B_k c^2<7/3.

To verify this uniformly, replace c^2 by 7/10 and multiply the
difference below 7/3 by the positive 30(1+k). Its numerator is

    P_1(k)=19-29k-51k^2+81k^3.

P_1 decreases on [0,9/20]. Indeed its derivative is a convex
quadratic negative at both endpoints, with values -29 and
-10277/400. Its endpoint value is

    P_1(9/20)=24029/8000>0.

Also sJ<33/40. Thus (8) gives

    (1-k)^2 eta'>2-(33/40)(7/3)=3/40>0.          (27)

The geometric derivative of 29P_C is greater than

    20s(1+c^2)-41k>(260/9)s-41k.

Since T<21/10 and k<9/20,

    41k/s=41kT/(1+k)<7749/290<28.

The last derivative is therefore greater than (8/9)s>0.
Together with T_C'(eta)>0 and (27), this proves the claimed
whole-path increase in k.

At fixed k=1/5, P_C also increases with p on (10). More generally
its p derivative wherever these scalar comparisons are used is

    29 partial P_C/partial p
      =R(21+20p)/(1+p^2)^(3/2)
          -s^3/(1+k)-20c s^2+T_C'(eta)eta_p,
    eta_p=J^3 c s^2/[(1-k)(1+k)]>0.

Using (11), R>=79/40 and (1+p^2)^(3/2)<3/2, the derivative is
strictly greater than

    (79/40)*29/(3/2)-1-45/4=389/15>0.           (28)

All needed signs persist when p decreases to 2/5 at k=1/5.
The condition sJ<1 holds throughout the displayed middle-band
rectangle. Also u_p=(s^2/(1+k))(s-kc)>0 here, since kp<1;
therefore decreasing p preserves u<1 and eta<1. No circle mask
or physical mean is changed in this scalar comparison.

It follows that every actual larger-k middle point has

    P_C(p,k)>=P_C(p,1/5)>=P_C(2/5,1/5).

At this single exact scalar endpoint,

    c=7/sqrt(85), s=6/sqrt(85), J=sqrt(26)/5,
    eta=3/2-(39/25)sqrt(26/85)>3/5,

    29[P_C(2/5,1/5)-R]
      =137/sqrt(85)+206/sqrt(26)+T_C(eta)
           -R[29+58/sqrt(29)].                  (29)

The complete positive comparisons are

    137/sqrt(85)>297/20,
    206/sqrt(26)>40,
    eta>3/5,
    T_C(eta)>163/sqrt(34)>279/10,
    58/sqrt(29)<54/5.

Their respective integer squared reserves are

    137^2*400-297^2*85=9835,
    206^2-40^2*26=836,
    225*85-26*676=1549,
    163^2*100-279^2*34=10306,
    54^2*29-58^2*25=464.

For eta, the comparison reduces to sqrt(26/85)<15/26;
T_C is increasing throughout (0,1). By (1),(29), the whole
endpoint excess is therefore greater than

    297/20+40+279/10-(1039/500)(29+54/5)
       =57/1250>0.                             (30)

Thus C alone contradicts containment over every remaining larger-k
middle point. The exact joining value k=1/5 is included in both
complete arguments; no unexamined tilt remains in (10).

## 9. Exhaustive whole-row join and literal original transfer

The frozen complete small-p theorem excludes every original p<=2/5,
including the not-initially-positive range p<=0. Section 3 here
excludes every p>=1/2. Sections 4--8 exclude every middle value
2/5<=p<=1/2 at every genuine k. These three continuous domains
exhaust every original real p, with all joining endpoints covered.

**Whole owner-row theorem.** The entire genuine sole-A Type III
feature g=nA is impossible in the original radius window. The
conclusion retains every original r in S/H<r<1, the original
torque-determined return mean z_A and its full physical interpretation,
all positive original magnitudes and every actual exterior owner,
degree and circle mask at B and C.

For D02.L135 and D02.L1345 retain the actual labels

    A=0, V=1, D=2, C=3, N_original=4, B=5,

and the complete rim A--V--D--C--N_original--B--A with chord AD.
A,D remain unloaded true3; V,B,C remain loaded true2. N_original
remains unloaded true2 in L135 and loaded true2 in L1345. All three
other actual physical units remain. No equation at B, C or
N_original is shortened or needed by the actual-point contradiction.

The shared A-direction owner row has its own independently reviewed
complete theorem. Its endpoint scalar inequalities are used above,
while its positive shared mean interval is never substituted for
the genuine singleton in this theorem. The sole-D and shared
D-direction rows remain separate. Type I/II and the physical-two
roof domains likewise keep their original scope.

The existing initial common-selector hypothesis stays explicitly
conditional. This proof neither establishes its global compatibility
nor reselects an extracted normal. V's unique PHYSICAL circle corner
is required; a physical-two mask with an individual-zero coefficient
is not treated as unique. Whole-data reflection transports the
complete actual geometry, equations, labels and masks together.

This closes one entire original owner row in both literal callers.
It does not declare either full D02 load family, a coarse parent,
the sharp nine-unit theorem, equality classification or Lean closed.

## 10. Exact source pins and verification boundary

The complete operative inputs are:

| Source | SHA256 | Consumed scope |
| --- | --- | --- |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Entire genuine sole-A chart, complete V2/A3/D3, original angular and mean cover, literal callers |
| UNIQUE_CIRCLE_TYPE_III_SHARED_A_ROOF_DIRECTION_WHOLE_MEAN_EXCLUSION_2026_10_29.md | 3a5dd8bb9af22bd5247e076541745ca1cc0793b0e83b1fc8734d5deba0ac0948 | Complete scalar endpoint C inequality for p>=1/2 and provenance of the two fixed projection directions |
| UNIQUE_CIRCLE_TYPE_III_SOLE_A_ALL_TILTS_SMALL_RADIAL_RATIO_EXCLUSION_2026_10_29.md | d1c9580f2a122cc935a4eb5b7628e8df4799cd78a612789cbbf7914f76f8a25f | Entire p<=2/5 branch at every genuine k, including p<=0, full original return mean and all literal data |

The operative inputs were read completely, with the final small-p
scalar-path sentence and closed derivative endpoint checked at their
frozen current revision. Every
new derivative, polynomial coefficient bound and rational reserve
printed above was reconstructed analytically and checked with exact
rational arithmetic. The proof covers full continuous domains; no
selected physical pose or finite angle sample establishes an interval.

The large-p derivative strategy was supplied by roofs and is printed
and reconstructed in full in Section 3. The middle-band argument,
entire small-k mean derivative, endpoint sum and larger-k point proof
are authored here. A full separate noncontributor review is required
before adoption of this whole-owner-row source and its complete join.

No frozen source, metadata, ledger, original flag or remote state was
edited. No original force, mean, normal, physical mask, individual
coefficient, unit or true degree was deleted or changed. No numerical
pose search, angle mesh, packing certificate, Lean/Lake compilation,
CI/workflow action, external communication or merge was used.
