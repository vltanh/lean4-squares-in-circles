# Recovered complete adjacent-circle exclusion for a W-owned common-hub-face return

Date: October 28, 2026 UTC. Recovery author: house continuation.

**Status: newly reconstructed complete hand proof, submitted for fresh root and separate independent review.** This is not an exact-byte restoration of COMMON_HUB_FACE_W_OWNED_ADJACENT_CIRCLE_TIP_EXCLUSION.md at historical SHA-256 845a04b72edb98de8c842f8a7f4c011e6327a1b456e560f0d92a7ca16b793a2a. The original proof and its old independent review are provenance only; the present new bytes require their own review.

The proof restores the whole unique upper-adjacent physical-circle feature, including an aligned W, every actual UW mean, the entire initial W physical-circle mask, and the complete actual loaded V2 equation. It creates no new original gate and does not close the other original U-normal features of D02.L01345.

## 1. Exact local physical theorem

Put

    Q=1105/256, 2<R<=sqrt(Q).

Keep distinct actual closed unit squares U,V,W contained in the unchanged disk D_R, with pairwise disjoint open interiors and physical contacts UV,UW,VW. Retain all original normals, positive magnitudes, common applications and shared-side means, physical circle corners, individual zero circle coefficients, true degrees and additional physical units.

The actual U-to-V and U-to-W normals are the same own side axis of U. The actual V is nonparallel to U and has its complete positive pair neighborhood exactly U,W, together with positive total circle load. The actual VW contact is a singleton at a V vertex and in the relative interior of a W side, with its unchanged normal owned by W. W physically touches the containing circle; its degree, circle loads and all other forces are arbitrary.

Rotate about the actual circle origin to make the common U support x=a, with U on its left. Let the actual UV point be P=(a,t). The entire minimum-x support set of W is strictly above or below P. Reflect all data to put it below P, and assume the actual entry bounds

    a>=-1/60, t>0.                                      (1)

These are hypotheses about the original applications, not a change of point or mean.

In the resulting actual V frame write

    e_1=(c,-s), e_2=(s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                            (2)

**Theorem.** V cannot have the unique physical circle corner

    Z=P+e_2.

This is the upper-adjacent corner relative to the unchanged UV vertex P. The whole local theorem uses only the actual V2 force and torque; no equation at U or W is shortened or used to assert a two-force property there. The original D02 caller supplies (1) before making any V-circle-mask choice.

## 2. Complete W-owned geometry and all actual means

The full physical chart is printed in Section 2 of COMMON_HUB_FACE_W_OWNED_TWO_CIRCLE_TIP_EXCLUSION.md. Its derivation is independent of V's circle mask. We restate that geometry and its mean endpoints explicitly.

If W is nonparallel to U, let P_W be its unique minimum-x vertex and choose its actual inward axes

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1.

For aligned W set C=1,S=0 and let P_W be its upper-left corner. Its original UW mean stays at its actual position on its minimum-x side.

The minimum-x support set of W cannot contain P. At such a common point the two inward tangent sectors would both contain East openly and hence overlap. Our reflection places that entire support set strictly below P.

At W, the original owned W-to-V normal and its original West normal toward U have nonnegative dot product by the complete physical triangle side-axis theorem. Thus the actual V-to-W normal has nonnegative East component.

For nonparallel W its candidates are f and g. The f candidate would make its minimum-f side P_W+[0,1]g the VW support. That side is below P and has x<=a+1. Every V vertex maximizing f is either P+e_2, above P, or P+e_1+e_2, with x>a+1. The side-exposure endpoint provides no additional singleton. Thus f is impossible.

For aligned W, North is excluded because W's minimum-North side is below P while V's maximum-North vertex is above P. East is excluded because its minimum-x side is x=a and V's maximum-x vertex is strictly to the right. Therefore every W frame has the actual unchanged normal

    n_VW=g.

Define

    gamma=C*c-S*s, eta=C*s+S*c.

The V-own components of g are (eta,-gamma). The stated singleton W-side-interior/V-vertex contact strictly exposes a V vertex, so gamma is nonzero. If gamma<0, it exposes V's rightmost vertex, whose x coordinate is greater than a+1 and hence beyond W's minimum-g side. Consequently

    gamma>0, eta>0, gamma^2+eta^2=1,
    M=P+e_1=P_W+alpha*f,
    alpha=c/C in (0,1),
    P_W=(a,t-delta), delta=s+c*S/C.                   (3)

For nonparallel W, P_W is its actual UW point. For aligned W, the original UW mean lies at or below P_W. The same actual U side contains that original mean and the point P above it, so it also contains P_W. Hence, in both cases,

    0<delta<=1.                                      (4)

P_W has not replaced the original UW mean in any equation.

Put

    r=S/C>=0, kappa=s/C>0,
    tau=1-alpha in (0,1), l=c-s*r=gamma/C>0.

The identities and inequalities needed below are

    alpha=gamma+r*eta,
    kappa=eta-r*gamma,
    tau<=1-gamma,
    r<=c/(1+s)<c<=alpha,
    0<kappa<1.                                      (5)

The bound for r follows directly from s+c*r<=1. The weak comparison c<=alpha retains the aligned endpoint C=1; no false strict inequality is imposed there. When r>0, the identity kappa=eta-r*gamma<eta<1 proves the final bound; for r=0 it is kappa=s<1. All original mean endpoints remain.

## 3. The full V2 equation forces the exact adjacent-circle ray

The original UV force line is horizontal through P. The actual VW force line through M in direction g meets it at

    q=P+l*East.                                     (6)

The two lines are nonparallel because C>0. In V's own coordinates the displacement q-P has components l*c and l*s, each strictly between zero and one, since 0<l<=c<1. Thus q lies in the open actual V.

There is only one physical V circle corner Z, with a positive total circle coefficient. Both unchanged pair-force lines pass through q. The full V torque about q therefore gives det(q,Z)=0. Its actual y coordinates satisfy q_y=t>0 and Z_y=t+c>t, so

    q=lambda*Z, lambda=t/(t+c) in (0,1),
    K=1/(1-lambda)>1,
    t=c*(K-1),
    a=K*(s-l)-s,
    Z=K*(s-l,c).                                   (7)

No physical two-circle resultant is substituted here. These are identities of the actual unique mask and the full original V2.

We first prove

    s-l>0.                                         (8)

Otherwise s<=l<=c, so s<=1/sqrt(2). From (5),

    l=c-s*r>=c/(1+s)>=sqrt(2)-1.

Equation (7), with K>1 and s-l<=0, gives a<=-l<=-(sqrt(2)-1)<-1/60, contrary to (1). This proves (8).

If r>0, squaring (4) and using c^2+s^2=1 gives

    2*r*(s/c)+r^2<=1.

Equation (8) gives s/c>1/(1+r). Therefore

    r^3+r^2+r-1<0.

This also holds at r=0. The polynomial is strictly increasing for nonnegative r, and its value at 6/11 is 7/1331>0. Hence

    r<6/11,
    S=r/sqrt(1+r^2)<6/sqrt(157)<12/25.               (9)

The last exact squared reserve is 108/98125>0.

## 4. The entire W physical-circle mask is forced to the right corner

In the actual orthonormal W frame define

    A=eta-gamma, D=gamma*(1+r),
    B=eta+gamma, H=(1+r)*eta-1,
    X=1+r-A.

Equations (3),(7) give

    Z=K*(A*f-D*g).                                  (10)

In particular A=(s-l)*C+c*S>0 by (8), so eta>gamma. Consequently

    0<A<1, 1<B<sqrt(2),
    H=A-tau, |H|<1,
    X-D=1-eta+r*(1-gamma)>0.                        (11)

The actual W center has f coordinate

    C*a+S*(t-delta)+1/2
      >=1/2-1/60-S
      >1/300,                                      (12)

using (1),(4),(9). Thus only W's two maximum-f corners can be physical circle points. They are

    Z_top=M+tau*f=Z-H*f+B*g,
    Z_right=Z_top+g=Z-H*f+(B+1)*g.                  (13)

The W center's g coordinate is -K*D+B+1/2. Suppose it were nonpositive. Then K*D>=B+1/2. The exact identity

    A*H+D*B=X

and |Z|=R give

    R^2-|Z_top|^2=2*K*X-(H^2+B^2)
      >2*K*D-(1+B^2)
      >=2*B-B^2
      >0.                                          (14)

Here all strict signs follow from (11). If that center coordinate were nonpositive, Z_top would be at least as far from O as Z_right; its minimum-f partners would be strictly closer by (12). Equation (14) would put every W vertex strictly inside D_R, contrary to W's physical boundary contact.

Therefore the actual W center has both f and g coordinates positive. Its unique physical circle corner is exactly Z_right. This covers every initial W mask, either zero individual circle coefficient, and the aligned W frame. No W force equation was invoked.

## 5. Both actual V adjacent vertices supply the missing containment bounds

Write the actual V circle corner in V-own coordinates as

    Z=-x*e_1+y*e_2.

Equation (7) gives the exact full-concurrence values

    x=K*gamma*alpha>0,
    y=K*(1-gamma*kappa)>0,
    gamma*alpha*y=x*(1-gamma*kappa).                (15)

The actual vertices Z+e_1 and Z-e_2 also belong to V and are contained. Comparing each squared norm with |Z|^2=R^2 gives

    x>=1/2, y>=1/2,
    x^2+y^2=R^2.                                   (16)

These are actual containment constraints. Merely equating two designated circle norms would not supply them.

In V's own frame the vector from Z to the actual W circle corner is

    Z_right-Z=A_1*e_1-B_1*e_2,
    A_1=1+eta+tau*gamma,
    B_1=1+gamma-tau*eta.

Using A>0, 0<tau<1 and gamma,eta>0,

    A_1>B_1>0,
    A_1+B_1>2.                                     (17)

The two actual circle equalities therefore give the line identity

    A_1*x+B_1*y=(A_1^2+B_1^2)/2.                    (18)

No geometric role is assigned to any auxiliary square.

## 6. A convex segment comparison supplies a purely algebraic large parameter

Put N=A_1^2+B_1^2. The line (18) clipped by x,y>=1/2 is the closed segment with endpoints

    (1/2,Y_*), (X_*,1/2),
    Y_*=(N-A_1)/(2*B_1),
    X_*=(N-B_1)/(2*A_1).                            (19)

Indeed N>A_1+B_1 by (17) and the sum-of-squares inequality, so both X_*,Y_* exceed 1/2. Moreover

    Y_*-X_*=
      (A_1-B_1)*(N-A_1-B_1)/(2*A_1*B_1)>0.          (20)

The function x^2+y^2 is convex on this actual closed segment. Equations (16),(19),(20) therefore yield

    R^2<=1/4+Y_*^2,
    Y_*>=sqrt(R^2-1/4).

Define the auxiliary scalar

    d_*=Y_*-1.

Then, because R>2,

    d_*>187/200,                                   (21)

using 15/4-(387/200)^2=231/40000>0. Direct expansion of (19) gives

    d_*=
      (tau^2+tau*gamma+eta)/
      (2*(1+gamma-tau*eta)).                        (22)

The scalar d_* is not the radial coordinate of an actual S square, nor is it asserted to be at most the original containing-circle parameter d. In particular no upper-radius bound is transferred to d_*.

The necessary upper comparison is instead derived from the actual y in (15). By (16) and the actual containing radius,

    y<=sqrt(R^2-1/4)<121/60,                        (23)

where (121/60)^2+1/4-Q=31/57600>0. From x>=1/2 and (15),

    1<=gamma*(2*alpha*y+kappa)
      <gamma*((121/30)*alpha+1),                    (24)

using kappa<1 and alpha>0. Thus, with A_0=30/121,

    gamma>30/151,
    tau<T(gamma):=1+A_0-A_0/gamma.                  (25)

The actual-circle estimate (23) and the auxiliary lower bound (21) are separate statements. This distinction is essential at the convex segment endpoint.

## 7. One complete algebraic interval excludes every surviving parameter

This section restates the continuous scalar argument from Section 5 of COMMON_HUB_FACE_W_OWNED_TWO_CIRCLE_TIP_EXCLUSION.md at its purely algebraic scope. Its inputs here are exactly

    gamma,eta>0, gamma^2+eta^2=1,
    0<tau<=1-gamma,
    d_*=(tau^2+tau*gamma+eta)/
        (2*(1+gamma-tau*eta))>187/200,
    gamma>30/151, tau<T(gamma).

No physical two-circle V mask and no upper bound on d_* is an input.

For fixed gamma,eta, the ratio in (22) increases strictly with tau. Writing E=1+gamma-tau*eta and N_0=tau^2+tau*gamma+eta, its derivative has the positive numerator

    (2*tau+gamma)*E+eta*N_0>0.

The upper bound tau<=1-gamma therefore implies

    d_*<=D_0(gamma),
    D_0(gamma)=
      (1-gamma+sqrt(1-gamma^2))/
      (2*(1+gamma-(1-gamma)*sqrt(1-gamma^2))).        (26)

The numerator decreases and the positive denominator increases, so D_0 is strictly decreasing on (0,1). At gamma=39/100, the radical is strictly below 921/1000, with exact squared reserve 341/1000000. The ratio in (26) increases with that radical, giving

    D_0(39/100)<76550/82819<187/200,

where the final reserve is 177153/16563800. This and (21) force

    30/151<gamma<39/100.                            (27)

Enlarge to I=[30/151,39/100]. On I, T is nonnegative and strictly increasing, with

    T(39/100)=963/1573<5/8,
    5/8-963/1573=161/12584>0.                       (28)

Put

    D=187/100,
    v(gamma)=1-gamma^2/2.

The radical eta is at most v.

Multiplying the positive denominator in (22), its lower bound (21) requires

    tau^2+gamma*tau+eta*(1+D*tau)-D*(1+gamma)>0.      (29)

The left side increases with each of tau>=0 and eta>=0. By (25),(28), every actual member would consequently have G(gamma)>0, where

    G=T^2+gamma*T+v*(1+D*T)-D*(1+gamma).

Its exact derivative on I is

    G'=A_0/gamma^2*(2*T+gamma+D*v)
          +T-D-gamma*(1+D*T).

All omitted terms in the following bound are nonnegative. Using gamma<=39/100, v>=1-(39/100)^2/2 and T<5/8 gives

    G'>
      [A_0/(39/100)^2]*D*[1-(39/100)^2/2]
        -D-(39/100)*(1+D*5/8)
      =8977019/89232000>0.                          (30)

Thus G is strictly increasing on the entire enlarged closed interval. But its exact upper-endpoint value is

    G(39/100)=-19954435473/4948658000000<0.           (31)

Equations (29)--(31) contradict one another throughout the whole interval, including every enlarged endpoint. This proves the theorem of Section 1.

## 8. Full original-feature join and unchanged scope

For the original six-body positive graph with rim

    01,12,23,34,45,50

and its single unchanged positive chord02 and positive circle-load set {0,1,3,4,5}, set

    U=2, V=1, W=0, T=3,
    boundary path V,W,5,4,T=1,0,5,4,3.

The true degrees are U3,V2,W3,5_2,4_2,T2. All three arbitrary completing squares of the same nine packing remain.

The complete same-hub-face owner normal form first excludes the both-parallel shared feature and exhausts the original nonparallel VW owners. Its remaining actual feature has V nonparallel to U and VW a W-side-interior/V-vertex singleton. This local proof applies to that actual feature; it performs no new normal selection.

Put the minimum-x W support below P by the same global reflection as in Section 1. If its unchanged actual UW mean is (a,z), then z<t. The full original U3 equations give

    n_UT=West,
    mu_T=mu_V+mu_W,
    P_T=(a-1,h),
    mu_T*h=mu_V*t+mu_W*z.

The actual occupied U arc contains the lower W port and runs clockwise from V to T. The complete endpoint moment argument of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, Section 1, uses this occupied order, the actual boundary path and the full original V2 and T2 equations. It gives

    t>0, h>0.

No origin-inside-U premise or two-force assumption at W is involved.

For every actual contained unit center z, the farthest-corner estimate gives |z|<=sqrt(R^2-1/4)-1/2. The actual T lies beyond its original minimum-West support at P_T, and its halfwidth is at least 1/2. Therefore

    1-a<=sqrt(R^2-1/4)-1<61/60,
    a>-1/60.

These are precisely the stronger actual entry bounds required in (1). The same-nine analytic lower-radius theorem already excludes R<=2.

If V's unique physical circle corner is P+e_2, every premise of the new theorem is now satisfied. This excludes its entire unique upper-adjacent-circle subdomain, including aligned W, every original UW mean, every initial W mask, either T circle mask and every completion placement.

The local proof also applies to any other actual component supplying the same literal local hypotheses and entry signs; it has no path-length or completion-capacity assumption. The whole original D02 row nevertheless has other U-normal configurations. This source alone does not close that row or a parent gate.

The complete same-axis assembly can use this new proof together with the separately accepted unique-opposite and physical-two-circle sources, but its historical reference to 845a04b72edb98de8c842f8a7f4c011e6327a1b456e560f0d92a7ca16b793a2a must be reconciled explicitly to this new file and new review. No old review is silently transferred to new bytes.

## 9. Exact direct sources and verification boundary

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| COMMON_HUB_FACE_W_OWNED_TWO_CIRCLE_TIP_EXCLUSION.md | b28c1dac6d90f960dc0415818a9e883ed95dd60768749bae10a5e4f60dca5365 | Complete physical W-owned chart independent of the V mask, and provenance of the scalar argument restated at its exact algebraic scope in Section 7 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual W-owned triangle normal sign, with all original support means |
| SAME_HUB_FACE_BOUNDARY_TRIANGLE_TIP_RETURN_OWNER_NORMAL_FORM.md | 5f70175b10e068bdaddcd135fdf0cf70ad48d5f256d4ca18b86e616cc3fd7eb6 | Complete selected original W-owned feature and parallel-case cover, only for the literal caller |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Actual occupied order and full true-endpoint moment signs, not its pocket-capacity conclusion |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original rim, chord, load set, true degrees and same-nine contract |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Whole original R<=2 exit retaining the same nine physical squares |

All new ray, physical-corner, clipped-segment and scalar arguments are printed in full. Exact fraction arithmetic checks the displayed rational identities only. No numerical pose search, interval pose certificate, angle mesh, replacement mean, removed force, fake S unit, Lean compilation, CI, workflow, ledger edit, commit or remote action is used.

