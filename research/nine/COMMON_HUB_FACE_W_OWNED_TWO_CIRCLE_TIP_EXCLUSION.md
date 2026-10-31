# A W-owned common-face return cannot have a two-circle boundary tip in the upper near-axis chart

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform physical-mask exclusion, frozen for full root and separate independent review.** This excludes the entire physical two-circle-corner mask of the actual loaded tip, including either zero individual circle coefficient. The other neighbor's entire circle mask and every actual shared-side mean are retained. The theorem is local, uses only the tip's full two-force equations, and has no degree or load restriction on its two other actual units.

The literal D02.L01345 common-axis caller is provided in Section 7. It receives a whole physical-mask exclusion, not whole original-row credit. The remaining unique adjacent-circle feature is a separate obligation.

## 1. Exact local physical statement

Put

    Q=1105/256, 2<R<=sqrt(Q),
    d=sqrt(R^2-1/4)-1.

Keep distinct actual closed unit squares U,V,W contained in the unchanged disk D_R, with pairwise disjoint open interiors and actual physical contacts UV,UW,VW. Retain every original support normal, common point or side mean, force, true degree, physical circle corner and zero coefficient. Extra physical units and contacts remain arbitrary.

The original U-to-V and U-to-W normals are the same own side axis of U. V is nonparallel to U and is positively circle-loaded with its complete positive pair neighborhood exactly U,W. The actual VW contact is a singleton consisting of a V vertex and a point in the relative interior of a W side, with the unchanged normal owned by W. W physically touches the containing circle; its degree, positive loads and every other equation are unrestricted.

Choose orthonormal coordinates about the same circle origin so that the common U support is x=a and U lies to its left. Let the actual UV point be P=(a,t). Reflect the entire coordinates if necessary to put the whole minimum-x support set of W below P. In this stated chart assume only

    a>=-1/2, t>=0.                                  (1)

These are explicit physical entry conditions, not a choice of a new application.

**Theorem.** Under these complete actual hypotheses, V cannot have two physical circle corners.

The original D02 caller supplies the stronger a>-1/60 and t>0 by its full U3 and boundary-path endpoint equations. The local proof below does not use an equation at U or W, a boundary-path length, or a completion-capacity premise.

The radius bounds give

    187/200<d<61/60.                                (2)

For the lower strict comparison, R>2 and
15/4-(387/200)^2=231/40000>0 give d>187/200.
For the upper one,
(121/60)^2+1/4-Q=31/57600>0 gives d<61/60.
Both original radius endpoints are thereby treated at their actual scope.

## 2. Complete actual W-owned chart, including aligned W and every UW mean

Write the nonparallel V in its actual inward frame at P:

    e_1=(c,-s), e_2=(s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                          (3)

The entire minimum-x support set of W is strictly below P. It cannot contain P: at P the inward tangent sector of V contains East openly, and another actual unit with that same minimum-x support and containing P would overlap it. The upper/lower alternatives are disjoint; the lower one is the explicit chart in Section 1.

If W is nonparallel to U, let P_W be its unique left vertex and write its actual inward axes as

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1.

For aligned W set C=1,S=0 and let P_W be its upper-left corner. The whole minimum-x side of W lies below P in this case. Its original UW mean is left unchanged and may be any actual point in the original shared interval.

At W, its owned outward axis toward V and its original outward normal West toward U satisfy the physical triangle owned-axis inequality. Consequently the original V-to-W normal has nonnegative East component.

For nonparallel W the only candidate inward own axes with that sign are f and g. The f choice cannot occur. Its minimum support side is P_W+[0,1]g, wholly below P and with x at most a+1. Every V vertex maximizing f is either P+e_2, above P, or P+e_1+e_2, with x>a+1. The side-exposure equality includes only these two vertices and gives no extra singleton. Thus none is on that actual W side.

For aligned W, North is excluded because W's minimum-North side is below P while V's maximum-North vertex is above P. East is excluded because W's minimum-x side is x=a and V's maximum-x vertex is strictly to its right. Therefore the original normal in every W frame is

    n_VW=g=(S,-C).

Define

    gamma=C*c-S*s, eta=C*s+S*c.

The V-own components of g are (eta,-gamma). The original singleton with a W-side-interior point strictly exposes its actual V vertex. Hence gamma is nonzero. If gamma<0, the exposed V right vertex has x>a+1, beyond W's minimum-g side. Thus gamma>0 and the actual VW point is

    M=P+e_1=(a+c,t-s).                              (4)

Since M is in the relative interior of the actual W side P_W+[0,1]f,

    alpha=c/C in (0,1),
    M=P_W+alpha*f,
    P_W=(a,t-delta), delta=s+c*S/C.                 (5)

For nonparallel W, P_W is the actual UW singleton. For aligned W, its original UW mean lies at or below P_W, while the same U side also contains P above it. That original side interval must therefore contain P_W too. In both cases the actual U side contains P and P_W and has length one, so

    0<delta<=1.                                    (6)

In particular P_W has not replaced any original mean in a force or moment equation.

Put

    r=S/C>=0, kappa=s/C>0,
    tau=1-alpha in (0,1), l=c-s*r=gamma/C>0.

The exact relations are

    gamma^2+eta^2=1, gamma,eta>0,
    alpha=gamma+r*eta, kappa=eta-r*gamma,
    alpha^2+kappa^2=1+r^2,
    tau<=1-gamma.                                  (7)

Two additional elementary bounds will be used. From (6),

    r<=c/(1+s)<c.

Thus S=r*C<c and alpha>r; (7) implies kappa<1.
Also alpha<1 gives C>c and r<s/c. Multiplying with
r<=c/(1+s) gives r^2<s/(1+s)<1/2. Hence

    r<1/sqrt(2)<3/4<d, 0<kappa<1.                  (8)

The case r=0 satisfies both conclusions directly. No equality frame or original mean endpoint has been discarded.

## 3. The entire physical two-circle V mask and its full resultant

Use V's actual own coordinates about O, and write

    A=P.e_1=a*c-t*s, B=P.e_2=a*s+t*c.

The sole entry condition (1) implies

    B>=-s/2>-1/2.                                  (9)

A contained unit at R>2 has two physical circle corners only when one own center coordinate is zero and the other is nonzero. Since B+1/2>0, the complete two-corner mask is therefore exactly

    A=-1/2, B=d,
    Z_-=-e_1/2+(d+1)e_2,
    Z_+= e_1/2+(d+1)e_2.                           (10)

The alternative zero second center coordinate is ruled out by (9), and the negative first-axis mask would require that same impossible equality. The actual two circle corners, including a corner with zero individual force coefficient, are retained.

The original UV line is horizontal through P. The original VW line through M in direction g meets it at the actual point

    q=P+l*East.

In V's own coordinates this is

    q=(-1/2+gamma*alpha, d+gamma*kappa).             (11)

Indeed l*c=gamma*alpha and l*s=gamma*kappa. Both offsets from P are strictly between zero and one: l<=c and c,s>0 give 0<l*c<1 and 0<l*s<1. Hence q is in the open interior of the actual V.

Normalize the full positive circle resultant at V by its positive total coefficient. Every permitted physical two-corner weighting gives

    F=xi*e_1+(d+1)e_2, -1/2<=xi<=1/2.              (12)

The full original V force and torque imply det(q,F)=0: both original pair lines pass through q, and torque about q retains the two radial circle atoms. The positive second coordinates in (11)--(12) give

    q=lambda*F,
    lambda=(d+gamma*kappa)/(d+1), 0<lambda<1.

Thus no unique-mask properness theorem is applied to a two-corner mask. The lower endpoint xi>=-1/2 in the entire original resultant interval yields the necessary inequality

    gamma*[2*(d+1)*alpha+kappa]>=1.                  (13)

This includes equality and either individual zero circle coefficient. No circle force or original contact force is dropped.

## 4. Every W circle-mask alternative is forced to its unique right corner

In the actual orthonormal W frame f,g, equation (10) gives

    M.f=gamma/2+d*eta,
    M.g=eta/2-d*gamma.

The f-coordinate of the actual W center is

    M.f+1/2-alpha
      =(1-gamma)/2+(d-r)*eta>0,                    (14)

by (8). Therefore only the two maximum-f W corners can be physical circle corners. They are the actual top and right corners

    Z_top=M+tau*f,
    Z_right=M+tau*f+g.

The top corner, in V's own coordinates, is

    Z_top=(1/2+tau*gamma, d+tau*eta).

Its exact excess squared norm above R^2=(d+1)^2+1/4 is

    tau^2+tau*gamma+2*d*tau*eta-2*d-1.

This expression increases strictly with tau>=0. Since tau<=1-gamma, its value is at most

    -gamma+2*d*((1-gamma)*eta-1)<0.                  (15)

Thus the top corner is strictly inside D_R. Every other W corner on its minimum-f side is strictly closer to O than the corresponding maximum-f corner by (14). Since W physically touches the circle, its entire physical mask must therefore consist of the unique right corner Z_right.

The actual right corner has V-own coordinates

    (1/2+tau*gamma+eta, d+tau*eta-gamma).

Its equality |Z_right|^2=R^2 is exactly

    2*d*E=N,
    E=1+gamma-tau*eta>0,
    N=tau^2+tau*gamma+eta,                           (16)

or

    d=(tau^2+tau*gamma+eta)/(2*(1+gamma-tau*eta)).

The denominator is positive because tau,eta<1. Every initial W physical mask, either zero individual weight, and the aligned W endpoint are included in this derivation. No full-force equation at W was used or shortened.

## 5. The circle equality and full V weighting contradict one another

### 5.1. The whole gamma range lies below 39/100

At fixed gamma,eta the ratio in (16) increases strictly with tau: its derivative numerator is

    (2*tau+gamma)*E+eta*N>0.

Using tau<=1-gamma gives

    d<=D_0(gamma),
    D_0(gamma)=
      (1-gamma+sqrt(1-gamma^2))/
      (2*(1+gamma-(1-gamma)*sqrt(1-gamma^2))).        (17)

The numerator decreases and the positive denominator increases as gamma runs from zero to one. Thus D_0 is strictly decreasing.

At gamma=39/100, the actual radical is strictly below 921/1000, because

    (921/1000)^2-(1-(39/100)^2)=341/1000000>0.

The ratio in (17) increases with this radical, so

    D_0(39/100)<76550/82819<187/200,

with final exact reserve 177153/16563800. This contradicts (2) if gamma>=39/100. Consequently every hypothetical original member has

    0<gamma<39/100.                                (18)

### 5.2. The complete physical resultant gives a coupled upper bound on tau

From d<61/60 and kappa<1, the necessary force inequality (13) gives

    1<gamma*((121/30)*alpha+1).

Set A_0=30/121. Then

    alpha>A_0*(1/gamma-1),
    tau<T(gamma):=1+A_0-A_0/gamma.                  (19)

Since alpha<1, the same inequality also implies

    gamma>30/151.

For the scalar comparison enlarge the whole actual range to the closed interval

    I=[30/151,39/100].

On I, T is nonnegative and strictly increasing, and

    T(39/100)=963/1573<5/8,
    5/8-963/1573=161/12584>0.                       (20)

No positive lower cutoff was assumed before it was proved from the full original V weighting.

### 5.3. One continuous monotonicity calculation excludes the entire interval

Put

    D=187/100, v(gamma)=1-gamma^2/2.

The actual eta=sqrt(1-gamma^2) is at most v. The radius lower bound d>187/200 and the exact equality (16) require

    tau^2+gamma*tau+eta*(1+D*tau)-D*(1+gamma)>0.     (21)

This left side is increasing in each of tau>=0 and eta>=0. By (19), every actual member would therefore satisfy

    G(gamma)>0,

where the complete enlarged comparison is

    G(gamma)=T(gamma)^2+gamma*T(gamma)
             +v(gamma)*(1+D*T(gamma))-D*(1+gamma).
                                                               (22)

On all of I its exact derivative is

    G'=A_0/gamma^2*(2*T+gamma+D*v)
          +T-D-gamma*(1+D*T).

Every dropped term in the following lower bound has a proved nonnegative sign. By (20), gamma<=39/100 and v>=1-(39/100)^2/2,

    G'>
      [A_0/(39/100)^2]*D*[1-(39/100)^2/2]
        -D-(39/100)*(1+D*5/8)
      =8977019/89232000>0.                           (23)

Thus the largest G on the entire closed interval I occurs at its upper endpoint. Direct rational arithmetic gives

    G(39/100)=-19954435473/4948658000000<0.           (24)

Equations (23)--(24) contradict (21)--(22) for every actual gamma. This is a full continuous comparison, including every enlarged endpoint; it is not a finite pose, orientation or parameter sample.

The contradiction proves the entire theorem in Section 1.

## 6. Exact feature and equation boundaries

The theorem requires only the full actual loaded V2 equation. The original U and W may have arbitrary degrees and circle loads; no transmitter or shortened force equation has been assigned to either.

All original UV and UW means remain unchanged. For aligned W, the use of its upper-left corner P_W is purely geometric: the actual U side contains it because that same side contains the original UW mean below and P above. No torque or force is evaluated at a replacement point.

The physical two-circle mask at V is kept as the whole closed resultant interval xi in [-1/2,1/2]. Both endpoints and the interior are included. W's physical circle mask is proved unique using every actual corner before its right-corner equality is used. The boundary status of W requires no selected positive coefficient at an initially chosen corner.

The weak chart guards a>=-1/2,t>=0 are explicitly sufficient for (9). Their equality endpoints are included. They are not asserted for a caller whose actual occupied order gives a different sign. The original D02 caller below has strict stronger guards for proved reasons.

## 7. Literal D02.L01345 and the larger common-face boundary-path scope

For the original positive hexagon with rim 0--1--2--3--4--5--0, its single positive chord02 and positive circle-load mask01345, use

    U=2, V=1, W=0,
    boundary path V,W,5,4,T=1,0,5,4,3.

The actual degrees are U3,V2,W3,5_2,4_2,T2. All three arbitrary completion units remain. In the original same-U-axis branch, the accepted owner normal form gives the nonparallel V and actual W-side-interior/V-vertex singleton, after the complete both-parallel shared feature has already been excluded.

Put W below P by a reflection of the whole physical data. Full U3 force makes the original UT normal West and full torque retains its original mean. The actual boundary-path order and both real loaded endpoint equations give t>0 and h>0 for P_T=(a-1,h). The physical contained endpoint T yields 1-a<=d, hence a>=1-d>-1/60. These are stronger than (1). The present theorem therefore excludes the complete two-physical-circle-corner V subdomain for every W frame, every actual UW mean, every T physical mask and every completion placement.

Exactly the same local join applies to the general actual component consisting of one unloaded U3, the complete boundary path V,W,...,T with 3<=k<=5 boundary units, and the original spokes UV,UW,UT, whenever the actual outer-face order and same-axis W-owned feature are those in the previously proved common-face theorem. The degrees V2,T2,W3 and every other boundary degree remain the original ones. No equation or geometric role is assigned to an extra unit.

Together with COMMON_HUB_FACE_W_OWNED_OPPOSITE_CIRCLE_NINE_ARC_EXCLUSION.md, this excludes two entire V physical-corner alternatives in that selected common-face feature. The unique upper-adjacent-circle V alternative remains a separate proof obligation. No whole original fine or coarse checkbox is changed by this manuscript.

## 8. Exact operative sources and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual W-owned triangle-axis sign in the complete chart |
| SAME_HUB_FACE_BOUNDARY_TRIANGLE_TIP_RETURN_OWNER_NORMAL_FORM.md | 5f70175b10e068bdaddcd135fdf0cf70ad48d5f256d4ca18b86e616cc3fd7eb6 | Only the literal selected W-owned feature in the original D02 caller; the local theorem is proved without importing an opposite-corner hypothesis |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Actual occupied-path order and full endpoint moment signs giving t,h>0; no capacity statement used |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, load mask, true degrees and same-nine contract |

The comparison source for the separately closed unique-opposite feature is COMMON_HUB_FACE_W_OWNED_OPPOSITE_CIRCLE_NINE_ARC_EXCLUSION.md at SHA256 ffddf725faa8b5b8475ad78bf7f903de10f964a9ae051b5a6dfda5edbf1a84f5. Its unique-opposite premise is not imported into any step of this theorem.

All new physical circle and full-resultant arguments, the entire scalar interval proof, and every rational comparison are printed above. Exact fraction arithmetic checked the displayed rational identities only. No computational pose certificate, numerical pose search, angle mesh, normal reselection, changed mean, removed force, Lean compilation, CI, workflow, shared-ledger edit or remote action is used.

