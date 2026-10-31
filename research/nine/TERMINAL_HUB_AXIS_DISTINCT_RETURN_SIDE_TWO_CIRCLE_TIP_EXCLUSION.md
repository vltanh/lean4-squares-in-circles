# A terminal hub axis excludes every two-circle tip with different return sides

Date: October 28, 2026 UTC. Author: review_parallel continuation.

**Status: complete proposed uniform hand exclusion, submitted for full root
and separate independent review.** This treats the entire physical-two-circle
V domain when the two directed normals into W are different W side axes.
It includes both incoming radial and tangent V masks before their complete
join. The original terminal application is proved too close to the circle
origin to belong to the actual boundary unit T. No pocket-capacity estimate,
pose sample or computational exclusion certificate is used.

## 1. Entire component and original statement

Put Q=1105/256 and assume 2<=R<=sqrt(Q). Retain the fixed original
circle origin, all actual closed unit squares with pairwise disjoint open
interiors, all selected normals, positive magnitudes, original applications
or complete shared-side means, physical circle corners and individual zero
circle coefficients.

An entire positive component has the loaded boundary path

    V=B_1,W=B_2,...,B_k=T, 3<=k<=6,

its consecutive path edges, and exactly the three additional spokes
UV,UW,UT. U is genuinely unloaded of degree three. Every B_i has positive
total circle load. The actual exterior order is U,V,W,...,T,U. V and T
retain their genuine degree two; W and all other internal path bodies
retain every original force and their true degrees.

Assume that UT is the sole U-owned normal, UV is V-side-owned and not
U-owned, and UW is W-side-owned and not U-owned. The actual UV and UW
singleton contacts are in the respective external sides' relative interiors.
Finally suppose:

1. V and W have nonparallel physical frames;
2. the original directed V-to-W normal is a W side axis different from
   the original directed U-to-W normal;
3. V has two physical containing-circle corners.

**Theorem.** These hypotheses are impossible.

No terminal physical mask is prescribed. UT may be physically singleton
or have positive shared length: its unchanged original application or full
mean is retained throughout. The theorem uses the true T2 equation only
through its original strict boundary-path moment sign. It uses no equation
at W or any other internal path body. All other actual packing units remain.

## 2. The complete actual hub chart and original W-normal cover

The true loaded V2 common-point theorem makes its UV application distinct
from its VW application and outside W. The full unloaded-U3 touching-return
separator makes T closed-disjoint from V and W. Thus the three original U
applications are distinct. Rotate a relative support chart to put the sole
U-owned UT normal West. This display does not translate the containing
circle origin.

Both other normals strictly expose U vertices. Opposite U vertices cannot
have touching returned units, by the complete unit-reach argument in the
separator source. Two left vertices give a negative horizontal force sum;
either horizontal adjacent pair gives vertical components with one strict
sign. Full positive U force balance therefore forces the two right vertices.
Reflect vertically, without exchanging V and W's true degrees, so that

    U=[0,1]^2 in relative coordinates,
    P_V=(1,1), P_W=(1,0), P_T=(0,t),
    v=n_UV=(a,b), m=n_UW=(c_0,-d_0),
    a,b,c_0,d_0>0,
    a^2+b^2=c_0^2+d_0^2=1.

The full actual U equations give

    t=a*d_0/(a*d_0+b*c_0), 0<t<1.                    (1)

This is the original application; if UT is shared it is still its original
mean. The short U boundary arc through the upper-left vertex has all its
normal directions in a half-plane with a strict positive component, so
it cannot be the occupied boundary-path arc under full U balance. The
actual occupied path goes clockwise through P_W and the lower U boundary.

Put

    u=(b,-a), f=(d_0,c_0),
    alpha=a*d_0+b*c_0>0,
    epsilon=a*c_0-b*d_0.

Let ell be the unchanged V-to-W normal. The radius-free triangle
side-normal theorem applied at W gives m.ell>=0. Since ell is a W
axis different from m, it is therefore f or -f; -m is excluded. At V,
the same geometric theorem with its own incoming axis -v gives
(-v).ell>=0. But v.f=alpha>0. Hence the entire original different-side
cover is

    ell=-f, ell.v=-alpha<0, ell.u=epsilon.           (2)

Write the actual side parameter of UV as r in (0,1), so

    V=P_V+[-r,1-r]u+[0,1]v.

Nonparallel V/W makes ell a strict V vertex normal. Its VW application
Q_VW is therefore one of the two endpoints on V's minimum-v side.
Write Q_VW=P_V+q*u, where initially q=-r or q=1-r. Since Q_VW belongs
to W and P_W is on W's minimum-m side,

    m.(Q_VW-P_W)=-d_0+q*alpha>=0.

Thus q>0, which forces q=1-r in (0,1), and (2) forces epsilon>0.
Consequently alpha^2+epsilon^2=1. Every actual original W-owned VW
contact is side-interior by the selected strict point-contact convention.
Thus W has the whole actual chart

    W=Q_VW+[-z,1-z]m+[0,1]ell, 0<z<1,
    z=q*alpha-d_0,
    m=alpha*u+epsilon*v,
    ell=epsilon*u-alpha*v.                          (3)

The UW point is on the minimum-m side and the VW point on the adjacent
minimum-ell side. No original normal or side point has been replaced.

## 3. Every initial physical two-circle V mask is covered

Let mu,nu>0 be the unchanged UV,VW magnitudes. V's full force is

    F_V=mu*v-nu*ell
       =-nu*epsilon*u+(mu+nu*alpha)*v.

Its u component is strictly negative and its v component strictly positive.
The physical farthest-corner rule therefore gives an actual V circle corner
(-x,y), with

    x,y>=1/2, R^2=x^2+y^2,
    V=[-x,1-x]u+[y-1,y]v,
    Q_VW=(1-x,y-1), P_V=(1-x-q,y-1).                (4)

There cannot be ties in both own coordinates at this radius. The complete
physical-two mask is therefore x=1/2 or y=1/2. Retain the entire original
resultant in the notation

    F_V=Lambda*(-xi*u+eta*v), Lambda>0,
    xi,eta>0.

If x=1/2 then 0<xi<=1/2 and eta=y. If y=1/2 then xi=x and
0<eta<=1/2. These signs follow from the positive pair magnitudes; neither
physical corner is deleted when its individual coefficient vanishes.

The complete force and origin-torque equations give

    mu=Lambda*(eta-xi*alpha/epsilon)>0,
    q*(eta-xi*alpha/epsilon)
       =eta*(1-x)+xi*(y-1).                         (5)

If y=1/2, then x>=sqrt(15)/2>1. The right side of (5) is strictly
negative, while its left side is strictly positive. Thus this entire
tangent-side mask is excluded, including all its original coefficient
endpoints. Only x=1/2 remains.

Use the actual u,v frame about O as the displayed plane coordinates.
Set d=y-1. The remaining whole actual units have

    V=[-1/2,1/2] x [d,d+1],
    Q_VW=(1/2,d), P_V=(p,d), p=1/2-h,
    h=q in (0,1),
    m=(alpha,epsilon), ell=(epsilon,-alpha),
    W=Q_VW+[-z,1-z]m+[0,1]ell.                     (6)

The full V torque is

    mu*p=nu*det(Q_VW,ell)
         =nu*(-alpha/2-d*epsilon)<0.

Consequently

    1/2<h<1,
    187/200<d<61/60.                               (7)

The two radius reserves are 231/40000 and 31/57600, from
15/4>(387/200)^2 and (121/60)^2+1/4>Q respectively.

## 4. The original U3 fixes the actual terminal application

In (6), North strictly exposes U at P_V. Its actual inward unit axes
can be written

    e=(C,-S), j=(-S,-C), C,S>0, C^2+S^2=1,
    U=P_V+[0,1]e+[0,1]j.                            (8)

The unchanged UW application is its adjacent vertex P_V+e. This is
the same P_W already proved in Section 2: the original downward U
side direction becomes e in the actual V frame. From (3), its genuine
coordinates on W's minimum-m side give

    h=C-(epsilon/alpha)*S+z/alpha.                  (9)

The U-to-T normal is the own U axis j, opposite the genuine side through
P_W. Write its unchanged point, including any actual shared mean, as

    P_T=P_V+j+t_* e, 0<=t_*<=1.

Let omega,tau>0 be the original UW,UT magnitudes. The full U force and
torque about P_V give

    omega*alpha=tau*S,
    mu+omega*epsilon=tau*C,
    omega*det(e,m)-tau*t_*=0.

Thus, with kappa=epsilon/alpha,

    S<alpha,
    t_*=S^2+kappa*C*S,
    P_T=(p-S+C*t_*, d-C-S*t_*).                    (10)

The strict S<alpha follows by squaring the positive inequality
alpha*C>epsilon*S from mu>0. All three original positive U forces
have been used; no terminal mean was selected to obtain (10).

The actual clockwise boundary-path order from Section 2 and the true T2
origin-torque equation give

    det(P_T,n_UT)>0.

This is the degree-free boundary-edge moment sign at T's actual loaded
path neighbor, with the endpoint orientation reversed. Since n_UT=j,

    B:=P_T.e<0.                                    (11)

The sign holds with every actual T mask, all original shared terminal
means and all zero individual circle coefficients. It is the only T
equilibrium consequence used below. A higher-degree T cannot inherit
(11) by deleting another force.

## 5. The complete physical W formula and one angular range

The force-free radial-inner-corner boundary theorem applies literally to
the actual chart (6): d>11/12, alpha,epsilon>0 and z>0. It first
proves the complete W physical mask, then gives its unique circle corner
and the exact equation

    d=F(alpha,1-z),
    F(gamma,tau)
      =(tau^2+tau*gamma+sqrt(1-gamma^2)) /
         [2*(1+gamma-tau*sqrt(1-gamma^2))].          (12)

The denominator is positive. F increases strictly in tau and decreases
strictly in gamma along the entire unit quarter circle. No W2 equation,
circle-weight choice or assumed W corner enters this invocation.

If alpha>=sqrt(3)/2, then z>0 and those monotonicities give

    d<F(sqrt(3)/2,1)=sqrt(3)/2<11/12,

contrary to (7). Hence the whole surviving domain satisfies

    0<alpha<sqrt(3)/2, epsilon>1/2,
    kappa>1/sqrt(3).                               (13)

Also (9), h<1 and C-kappa*S>0 give z<alpha. All comparison
parameters used below are in their stated closed or open ranges.

## 6. A continuous terminal-curve theorem reduces the whole actual domain to one endpoint

Fix the actual alpha,z,d. Put alpha=sin(w), epsilon=cos(w), with
0<w<pi/3. Write C=cos(theta), S=sin(theta); (10) gives 0<theta<w.
Equations (9)--(10) define the following algebraic curve for 0<theta<w:

    phi=w-theta,
    h(theta)=(sin(phi)+z)/alpha,
    p(theta)=1/2-h(theta),
    t_*(theta)=sin(theta)*cos(phi)/alpha,
    P(theta)=(p(theta),d)+j(theta)+t_*(theta)*e(theta),
    e(theta)=(cos(theta),-sin(theta)),
    j(theta)=(-sin(theta),-cos(theta)).              (14)

At the actual theta this is exactly the original P_T. Other values
in (14) are algebraic comparisons only; no physical packing or original
mean is moved and no earlier geometric theorem is applied to a new pose.

Since 0<z<alpha, there is a unique theta_1 in (0,w) with

    h(theta_1)=1,
    sin(w-theta_1)=alpha-z.

The actual h<1 makes theta>theta_1. Differentiating (14) gives exactly

    P'(theta)=K(theta)*e(theta),
    K(theta)=[2*cos(theta)*cos(phi)
               +sin(theta)*sin(phi)-alpha]/alpha.

The identity 2*cos(theta)*cos(phi)=cos(w)+cos(2theta-w)
and |2theta-w|<=w give

    K>=2*epsilon/alpha-1>0.                         (15)

Define G(theta)=P(theta).e(theta). Its complete expression and derivative
are

    G=(1/2-z/alpha)*cos(theta)-d*sin(theta)
          +sin(2theta-w)/alpha,
    G'=-(1/2-z/alpha)*sin(theta)-d*cos(theta)
          +2*cos(2theta-w)/alpha.

Because |1/2-z/alpha|<1/2, Cauchy's inequality and (7),(13) give

    G'>2/sqrt(3)-sqrt((61/60)^2+1/4)>0.              (16)

The last squared reserve is 179/3600. Thus G increases strictly on
the whole comparison interval. Its actual value is B<0 by (11), so
G<0 throughout [theta_1,theta]. From (15),

    d|P(theta)|^2/dtheta=2*K*G<0.

Consequently

    |P_T|^2<|P(theta_1)|^2.                         (17)

At the comparison endpoint, suppress the subscript and write
C=cos(theta_1), S=sin(theta_1). They still satisfy 0<S<alpha and

    z=alpha*(1-C)+epsilon*S,
    A:=P(theta_1).j=1+S/2-d*C,
    B:=P(theta_1).e=-C/2-d*S+S^2+kappa*C*S<0.       (18)

The last sign follows from the same strict increase of G. Since e,j are
orthonormal, |P(theta_1)|^2=A^2+B^2. The remaining sections bound these
two exact endpoint expressions on their entire continuous domain.

## 7. Every alpha>=1/sqrt(2)

We first prove the uniform displacement bound

    z<epsilon/5.                                   (19)

If z>=epsilon/5, monotonicity of F would give
d<=F(alpha,1-epsilon/5). On the whole interval
1/sqrt(2)<=alpha<sqrt(3)/2, direct cross multiplication by the positive
denominator shows that F(alpha,1-epsilon/5)<187/200 is equivalent to

    J(alpha):=174*(1+alpha)-494*epsilon
                 +(334/5)*epsilon^2+40*alpha*epsilon>0.

Its derivative along epsilon=sqrt(1-alpha^2) is

    J'=174-(668/5)*alpha+40*epsilon
          +(494*alpha-40*alpha^2)/epsilon>0.

Every displayed term is positive after retaining the first two together;
174-(668/5)*alpha>174-668/5>0. At alpha=1/sqrt(2),

    J=1137/5-160*sqrt(2)>39/35>0,

using sqrt(2)<99/70. Thus (19) follows from d>187/200.

Equations (18)--(19) imply S<1/5 and C>489/500; the latter squared
reserve is 879/250000. The endpoint bounds are therefore

    -1/60<A<3/16.                                  (20)

For the upper bound use
1+1/10-(187/200)*(489/500)<3/16, with reserve193/100000.
The lower bound uses d<61/60 and C<=1.

Since kappa>1/sqrt(3)>4/7, (18) also gives

    B>-1/2+S^2-[61/60-(4/7)*(489/500)]*S.

The quadratic decreases throughout 0<=S<=1/5 because its derivative
is at most 2/5-4807/10500<0. Its endpoint value is
-28957/52500>-83/150, with reserve31/17500. Since B<0,

    A^2+B^2<(3/16)^2+(83/150)^2<12/35.             (21)

The final exact reserve is 15353/10080000. This covers the whole upper
alpha interval, including alpha=1/sqrt(2).

## 8. Every 0<alpha<=1/sqrt(2)

Here kappa>=1. The useful full-domain displacement estimate is

    z<epsilon-(4/5)*alpha,
    z/alpha<kappa-4/5.                              (22)

If the first inequality failed, F's tau monotonicity would give
d<=F(alpha,1-epsilon+(4/5)*alpha). The comparison tau lies in [0,1)
throughout the entire stated alpha interval. Its denominator is positive.
Cross multiplication shows that this comparison value is below187/200
exactly when

    L(alpha)=348-462*alpha^2-146*alpha-174*epsilon
                 +(1104/5)*alpha*epsilon>0.

The full second derivative is

    L''=-924+[174-(1104/5)*alpha*(3-2*alpha^2)]/epsilon^3<0.

Indeed epsilon>=1/sqrt(2), so its positive term is at most
348*sqrt(2)<522<924; the remaining numerator term is nonpositive.
Thus L is concave on the whole closed comparison interval. At its two
endpoints,

    L(0)=174,
    L(1/sqrt(2))=1137/5-160*sqrt(2)>39/35.

Concavity puts every intermediate value above the chord of these positive
values. This proves (22), without angle samples or an exclusion table.

### 8.1. The true terminal sign forces S<1/2

Let lambda=z/alpha. Using the identity
lambda=1-C+kappa*S from (18), the complete endpoint B can also be
written

    B=(1/2-lambda)*C-1+2*S^2+2*kappa*C*S-d*S.

If S>=1/2, (22) and kappa>0 give

    B>(13/10)*sqrt(1-S^2)-1+2*S^2-(61/60)*S
       =g(S).

The entire possible interval is 1/2<=S<alpha<=1/sqrt(2).
On it

    g''=4-(13/10)/(1-S^2)^(3/2)>4-(13/5)*sqrt(2)>0.

Also g'(1/2)=59/60-13/(10*sqrt(3))>0 and
g(1/2)=13*sqrt(3)/20-121/120>3/40>0, using sqrt(3)>5/3.
Thus g is positive throughout that interval, contradicting B<0.
Consequently

    0<S<1/2.                                       (23)

### 8.2. The whole 0<S<=1/3 interval

Here C>=sqrt(8/9)>14/15. Equations (7),(18) imply

    -1/60<A<7/6-(187/200)*(14/15)<3/10.

The last reserve is3/500. Since kappa>=1, C+S>=1 and d<61/60,

    B=-C/2-d*S+S^2+kappa*C*S
       >-C/2-S/60
       >=-sqrt(1/4+1/3600)=-sqrt(901)/60.

The last comparison is Cauchy with C^2+S^2=1. Retaining B<0,

    A^2+B^2<(3/10)^2+901/3600<12/35,               (24)

with exact reserve13/5040.

### 8.3. The whole 1/3<=S<1/2 interval

Equations (18),(22) give

    kappa*(1-S)>9/5-C.

Since C<=sqrt(8/9)<33/35 and 1-S<=2/3,

    kappa>9/7.

The squared reserve for sqrt(8/9)<33/35 is1/11025. Also (23) gives
C>sqrt(3)/2>6/7. Therefore

    -1/60<A<5/4-(187/200)*(6/7)<9/20,              (25)

with last reserve1/700. The complete lower bound for B is

    B>-1/2+S^2+[54/49-61/60]*S.

The right side increases for S>=1/3. At1/3 it is
-3179/8820>-11/30, with reserve11/1764. Hence B<0 gives

    A^2+B^2<(9/20)^2+(11/30)^2<12/35,              (26)

with exact reserve149/25200.

Sections8.2--8.3 exhaust (23), with their common endpoint retained.
Together with Section7 they prove the whole endpoint inequality

    |P(theta_1)|^2<12/35.                           (27)

## 9. Actual terminal containment gives the contradiction

Equations (17),(27) concern the unchanged actual terminal point and give

    |P_T|^2<12/35.

But P_T belongs to the actual physical boundary unit T. For any one of
its actual circle corners Z_T, including one with zero individual circle
coefficient, the unit diameter gives

    |P_T|>=|Z_T|-|Z_T-P_T|>=R-sqrt(2)>=2-sqrt(2).

Both sides are positive. Since sqrt(2)<99/70, with squared reserve
1/4900,

    (2-sqrt(2))^2=6-4*sqrt(2)>12/35.

This contradicts the actual point bound and proves the theorem. Every
physical T mask and every genuine original UT mean is included.

## 10. Full original D02 join and scope limits

In original M6.B6.HEXAGON.D02.L01345 retain

    U=2, V=1, W=0, T=3,
    the entire loaded boundary path1,0,5,4,3.

The accepted complete owner assembly gives the sole U-owned UT axis,
externally V-owned UV and W-owned UW, and their actual relative side
interiors in the remaining singleton-UT interface. The true degrees
remain U3,V2,W3,5_2,4_2,T2. Every premise above is therefore literal
whenever V has two physical circle corners, V/W are nonparallel and the
original directed VW normal is a W side axis different from UW.

The complete tangent physical-two mask was excluded in Section3; the
entire inner-radial physical-two mask, both individual V circle-weight
endpoints and every continuous normal/side-position parameter were
included in Sections4--9. W's full physical mask was proved before its
circle equation was used. The original terminal mean never moved.

This is the whole stated original feature. It does not include a unique
physical V corner, equal directed UW/VW normals, a V-owned VW normal,
or parallel V/W. Those have their separate complete-source obligations.
No existing original fine row or coarse parent closes from this source
alone, and no new computational gate is introduced.

The local proof's real T2 boundary-path sign is essential. In particular
it is not transferred to the true T3 endpoint of an opposite-ear caller.
A higher-degree application would have to supply (11) from its own full
equation, with all original forces retained.

## 11. Exact operative sources and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original equations, strict singleton conventions, actual means and all physical circle coefficients |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Distinct actual V applications, true V2 and physical boundary W |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Closed-disjoint terminal and full radius-free adjacent hub-port cover |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete original different-W-axis cover in Section2 |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Whole actual W mask, exact physical F formula and its continuous monotonicities |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Only Section1's complete actual port order and original endpoint moment signs; no pocket-capacity conclusion is used |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Only its degree-free boundary-pair origin-moment lemma, retaining every actual mean and physical corner |
| D02_ENTIRE_INCOMING_HUB_AXIS_AND_SHARED_TERMINAL_EXCLUSION.md | 0b0e8b90ff7535e6e80f429e10ff7535190c2a74220022d1a9ad3676a8595c7f | Literal unchanged original singleton-UT entry, owner properties and exact true degrees |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Entire original graph/load domain with all three original completion squares retained |

All new physical implications, derivative identities, full intervals,
sign prerequisites and rational reserves are printed above. Exact rational
arithmetic was used only to transcribe the displayed comparisons. There is
no sampled pose, numerical optimization, angle mesh, scalar exclusion
certificate, changed normal, replaced mean, deleted force, discarded
physical corner, false W2/T2 equation, Lean/Lake compilation, CI, workflow,
ledger edit, commit, remote write or merge in this proof.
