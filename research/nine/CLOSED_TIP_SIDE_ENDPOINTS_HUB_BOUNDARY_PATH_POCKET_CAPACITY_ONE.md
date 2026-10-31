# Closed tip-side endpoints at strictly exposed hub vertices have closing-pocket capacity one

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed geometric extension, submitted for independent review.** The two boundary-tip side parameters range over their whole closed intervals. The hub normals still strictly expose the corresponding hub vertices. The proof does not obtain these normal directions by changing an extracted certificate, and it does not claim that a free vertex/vertex normal can be replaced by a tip axis.

## 1. Exact larger physical statement

Put Q=1105/256 and assume 2<R<=sqrt(Q). Keep actual interior-disjoint closed unit squares in D_R, with the same origin, frames, physical circle corners, original application means and complete positive force and torque equations.

One complete positive component is

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

H is unloaded. Every B_i has positive total circle load. The actual outer-face order is H,B_1,...,B_k,H. Thus V=B_1 and T=B_k are true loaded degree two. Every internal body keeps its actual degree and every actual positive spoke. All completing units remain.

Assume that the unchanged H-to-V and H-to-T normals:

1. strictly expose vertices of H;
2. are own side axes of the corresponding actual boundary tips;
3. have their original applications anywhere on those closed tip sides.

Strict hub exposure makes each physical H-tip intersection a singleton. On a tip the singleton may be a side-interior point or either side endpoint. If n is the inward side normal of the tip and k=Jn, its exact chart is

    E=P+[0,1]n+[-rho,1-rho]k, 0<=rho<=1.             (1)

The new endpoints rho=0 and rho=1 are vertices of E. No strict exposure at that tip vertex is assumed. Every individual zero circle coefficient remains.

**Theorem.** The actual closing exterior pocket through H between V and T contains at most one whole additional unit square.

The statement is a theorem about these actual physical supports and complete equilibrium data. It may be used before a certificate selection, or in a setting allowing these closed support directions, only when the stated original data have independently been supplied. It is not a license to move a normal to a cone endpoint while retaining unsupported force magnitudes or torque equations.

## 2. The actual component inputs remain valid with closed tip endpoints

The physical boundary-contact graph has no cycle on at most six units. Thus the nonconsecutive V,T are closed-disjoint, and their two H applications are distinct. These are two distinct vertices of H, hence adjacent or opposite.

The full two-force properness theorem applies at each endpoint because its other positive neighbor is physical boundary. Its rectangle normal-line proof includes all closed vertex-normal cones and all side endpoints; it does not require a strict free normal at the endpoint under examination. With the original H-to-tip normal n and application P, it gives

    q=P+ell*n=lambda*F, ell>=0, lambda>0,             (2)

where F is the complete circle resultant. It does not assert q lies in a physical two-circle tip.

The degree-free boundary-pair moment theorem applies to the actual path contacts. Each endpoint's full torque therefore gives the same strict opposite signs for det(P,n) as in the general single-hub pocket proof. No internal path body is treated as degree two.

For clarity, closed tip endpoints cause no missing endpoint-port order. The all-owner common-point theorem gives the original H-V application P not in B_2, and likewise at T, since R^2>4>13/4. Any other B_i containing that P would give V an additional physical contact with a nonconsecutive path body, producing a forbidden physical boundary cycle of length at most k. Hence no other positive hub spoke occurs at either endpoint vertex. At other coincident hub applications, actual neighbor tangent sectors have disjoint interiors; their inward support normals, including weak cone endpoints, have the same weak angular order. This is the ordinary convex-square support order used in the general pocket proof. It needs no strict normal at a vertex of V or T.

Summing every original component equation gives

    sum F_i=0.                                      (3)

The full hub force and torque equations, the just-established port order, and the endpoint moment signs therefore give the adjacent and opposite charts below exactly as in Sections 5--6 of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md. Those coordinate calculations use only the hub supports and complete equations, not 0<rho<1. We print their needed conclusions and check every new endpoint use.

The boundary paths used below are changed only inside the actual closed H,V,T union. Every extra's open interior avoids that union. Its winding about the actual closing crosscut is therefore preserved. Original application means in every equation remain unchanged.

## 3. Adjacent hub vertices: complete closed-parameter argument

Rotate and reflect so the outer H arc is its top side, with

    P_L=(-X_L,h), P_R=(X_R,h), X_L+X_R=1,
    h>0, -1/2<X_L,X_R<3/2.

The short occupied arc is impossible by full hub force balance. The true endpoint moments and the unit-neighbor width bound give |x|<1 for x=(X_R-X_L)/2, exactly as in the general hub proof. At least one port has horizontal absolute coordinate at most 1/2. Its boundary-tip diameter bound gives

    h^2>=(2-sqrt(2))^2-1/4>9/100,

so h>3/10.

For the left tip write

    n=(-b,a), k=(-a,-b), a,b>0, a^2+b^2=1,
    N=b*X+a*h>-1/2,
    K=b*h-a*X>0,
    Z=K+rho, 0<=rho<=1.                              (4)

The strict K sign is its original endpoint moment. Equation (2) gives a negative k component of the full circle resultant. The positive n-center coordinate N+1/2 and the complete physical far-corner rule therefore imply

    Z>=1/2,
    R^2=(N+1)^2+Z^2.                                 (5)

This includes Z=1/2 with both physical outer corners and every individual weight endpoint. Its gap-facing corner is the actual point

    Z_L=P+n-rho*k,
    (Z_L)_y=h+a+rho*b>h.                             (6)

The strict height survives rho=0 because a>0. Its center has positive height as well, since its own components are N+1/2>0 and -(Z-1/2)<=0. Reflection gives the complete right endpoint chart.

The actual H top side and paths inside V,T to their gap-facing corners, together with their actual upper closing circle arc, form the closing occupied Jordan boundary. All of it lies in y>=h. Thus every whole pocket extra lies in that half-plane. In particular it has strict quarter-disk clearance. If even one extra is present, its vertical width gives h<=R-1<13/12<5/4.

We now use the two force-free arc estimates proved in Section 4 of ADJACENT_HUB_VERTEX_TIP_OWNED_ENDPOINT_POCKET_CAPACITY_ONE.md. They concern actual contained units and center radii, not a tip parameter:

    r=5/4, beta=arctan(5/16), chi=arctan(16/15).

Every actual boundary unit has its closed centered halfwidth-beta arc on the r circle strictly inside its open interior. Every quarter-clear unit has one connected open r-circle arc longer than pi/4. If R<=41/20, that length is greater than chi. The proofs include all own-frame and circle-mask transitions.

Here are the two closed-parameter checks needed for the actual routing and endpoint metric.

First, an outside left port |P|>=r cannot turn its center ray into the closing gap. Its exact determinant is

    det(P,c_V)=K/2+(1/2-rho)*N.

As in the original argument, |P|>=r and h<13/12 first give X>0 and N>0. If this determinant were negative, then

    rho>1/2+K/(2*N).

The closed bound rho<=1 still yields K<N strictly and rho>1/2. Hence N>5/(4*sqrt(2))>7/8, and (5) gives

    R^2=|P|^2+2N+1+2K*rho+rho^2
       >25/16+7/4+5/4=73/16>Q,

a contradiction. Thus the same outside-port center-ray statement holds at both rho endpoints. Equality of the determinant is allowed.

Second, the center-angle calculation of the original Section 7 uses only K<=Z, which follows from rho>=0. With the endpoint center angle delta measured from its outward horizontal direction, the exact same derivation gives

    X>=d*cos(delta)-(9/14)*sin(delta),                (7)
    d=sqrt(R^2-1/4)-1,

whenever tan(delta)<=28/17. No upper or strict lower bound on rho is used in that calculation. Its own-frame premise N+1/2>0 and its full circle equation are (4)--(5). In particular a physical two-corner center coordinate Z-1/2=0 remains included.

For completeness, the routing conclusion is about whole extra arcs. Put I equal to the part of the r circle above y=h. Endpoint connected circle intervals contain their radial center points. Disjoint radial-center-to-circle-corner segments in the upper annulus order the two center angles theta_R<theta_L. At a boundary of I, the outside-port determinant just proved prevents an endpoint center ray from lying past an unoccupied escape on the wrong side. Following I toward the corresponding center, the connected endpoint interval is terminal; the other endpoint interval cannot cross it without containing its radial center point in the wrong square. Before meeting that interval there is no occupied boundary crossing, so that part stays outside the actual Jordan pocket. Reflecting gives both bounds. Consequently every whole extra open arc lies in the single interval

    (theta_R+beta, theta_L-beta).                    (8)

This is precisely the actual-crosscut argument of the original Section 6; its only uses of an open tip-side parameter were (6) and the outside-port calculation, both checked on the closed interval above.

If two extras were present, (8) and the two arc estimates imply the following complete radius alternatives:

    R>=41/20:
      delta_L+delta_R<alpha_H=pi/2-2beta,
      cos(alpha_H)=160/281, sin(alpha_H)=231/281,
      d>49/50;

    R<=41/20:
      delta_L+delta_R<alpha_L=pi-2(beta+chi),
      cos(alpha_L)=83961/135161,
      sin(alpha_L)=105920/135161,
      d>187/200.

Both angle tangents are below 28/17. The decreasing positive concave function g(t)=d*cos(t)-(9/14)*sin(t), with the complete endpoint calculation of the original Section 8, gives respectively

    X_L+X_R>1+67/7025,

or

    X_L+X_R>1+1138649/94612700.

Both contradict X_L+X_R=1. The two closed radius subintervals cover the entire window, including their shared threshold. This proves the adjacent-vertex conclusion for 0<=rho_L,rho_R<=1.

## 4. Opposite hub vertices: full actual masks and strict separation

Put sigma=1/sqrt(2). Rotate the opposite-vertex chord horizontally and put the occupied hub arc below it:

    P_L=(-X,h), P_R=(Y,h),
    X,Y>0, X+Y=sqrt(2),
    c_H=(x_0,h), x_0=sigma-X=Y-sigma,
    A_H=(x_0,h+sigma), h>0.                          (9)

The original complete hub force and torque calculation gives, on the left,

    n=(-b,a), k=(-a,-b),
    0<=a<=b, a^2+b^2=1,
    K=b*h-a*X>0.

The new theorem explicitly retains strict exposure at the H vertex. Since a=b would be an H side axis, it follows that

    0<=a<b, a<sigma.                                (10)

This strict inequality is essential for the closed rho=1 endpoint below. We do not infer strictness at a tip vertex.

The complete actual left chart is (1), with

    N=b*X+a*h>0, Z=K+rho>=1/2,
    R^2=(N+1)^2+Z^2,
    Z_L=P_L+n-rho*k.                                (11)

These follow from the same full-resultant argument as (5). They retain every physical circle mask and weight endpoint.

Since X=N*b-K*a<=N, equations (11) give

    0<X<=d<61/60<41/40,

and reflection gives the same bound for Y. The gap-facing corner and the entire tip satisfy

    (Z_L)_y=h+a+rho*b>=h,
    (Z_L)_x=-X-b+rho*a<0,
    max_(z in V) z_x=-X+rho*a<x_0.                  (12)

The last strict bound now follows from rho<=1 and a<sigma. Thus it remains strict at rho=1. The whole right tip lies strictly in x>x_0 by reflection.

The sole newly weak height possibility in (12) is rho=0,a=0. It will be retained explicitly; no limiting perturbation is made.

The actual gap chain

    P_L -- P_L-rho*k -- Z_L

rises weakly in height, as does its reflection. A zero first segment at rho=0 is simply omitted. Together with P_L--A_H--P_R and the upper closing circle arc, these chains form the actual occupied closing boundary. Its whole bounded region lies in y>=h. The closing arc is the actual upper minor arc: both endpoint resultants have positive y component by (2), their closing resultant gap is less than pi by (3), and their gap-facing physical circle corners preserve this boundary order. The weak corner height h still gives the same closed half-plane.

Every whole pocket extra also has strict distance greater than 1/4 from O. Here is the geometric argument at its full scope. Each H roof side has positive unit-normal support at least

    |P_j|/sqrt(2)>=(2-sqrt(2))/sqrt(2)=sqrt(2)-1>1/4.

Both boundary units have distance at least R-sqrt(2)>1/4, and the outer circle also avoids the closed quarter disk. Thus the occupied boundary misses that disk with a strict margin. Homotope each endpoint portion, inside the strict half-plane F_j dot z>0, to P_j--q_j followed by its resultant ray. This half-plane contains the whole actual endpoint unit, since every physical circle corner z satisfies z dot x>=R^2-R*sqrt(2)>0 for every x in that unit. Equation (2) supplies q_j in the same half-plane. The global resultant balance and actual circular order keep the closing lift as the upper minor arc. The auxiliary loop has zero winding about O. The actual boundary therefore has zero winding throughout the connected closed quarter disk, which is outside the bounded pocket. Compactness gives the strict margin.

This is the full occupied-pocket argument with the actual closed-cone endpoint data. It does not rely on a strict normal at a tip vertex.

## 5. Opposite low roof: the complete limiter proof has closed parameter scope

Put r=5/4. Suppose |A_H|<=r. Then

    0<h<=r-sigma<11/20,
    |P_L|^2, |P_R|^2<433/320<r^2.                   (13)

The whole H roof is in the closed inner disk by convexity. On each gap chain, norm increases strictly along every nondegenerate segment: in the first its own coordinates are (N,-t), with K<=t<=Z and N,K>0; in the second they are (t,-Z), with N<=t<=N+1. Thus it has exactly one r-circle exit, including rho=0 when the first segment is absent.

Write a=sin(phi), b=cos(phi), 0<=phi<pi/4. The left exit has angle pi-eta, where

    eta=phi+min(arccos(N/r),arcsin(min(Z/r,1))).      (14)

The right exit has the reflected form.

Sections 4--8 of TIP_OWNED_HUB_BOUNDARY_PATH_ENDPOINTS_POCKET_CAPACITY_ONE.md prove the following pure limiter implication on exactly the displayed variables:

    X,Y>0, X+Y=sqrt(2), X,Y<41/40,
    0<h<=r-sigma,
    N=bX+a*h, K=b*h-aX>0,
    0<=a<=b, a^2+b^2=1,
    Z>=1/2, R^2=(N+1)^2+Z^2, 2<R<=sqrt(Q)
      ==> eta_L+eta_R>pi/2.                        (15)

Those scalar calculations use no rho at all after the listed constraints are obtained. In particular they do not assume a strict inequality K<Z. To make the closed endpoint application explicit, their complete limiter cover is:

- Two normal-side limiters give eta_j>=arccos(X_j/r). Since
  X^2+Y^2<(41/40)(X+Y)<123/80<r^2,
  their sum is greater than pi/2.
- At a tangent-side limiter put L=sqrt(r^2-Z^2)>=N and B=L*a+Z*b. The full tangent calculation gives X+B>10/7>sqrt(2). Its lower-N polynomial has the positive reserves 1/128 and 1/112 on its two continuous a intervals. In its upper-N comparison, a=0 is treated as equality X+B=N+Z, and N+Z>10/7 still follows from
  R^2<=(N+Z+1/2)^2+1/4
  and sqrt(15)>27/7. For a>0 the comparison is strict before that final bound. Thus a zero-angle tangent endpoint is included. A mixed pair of limiter types with sum at most pi/2 would give Y>=B, contradicting X+Y=sqrt(2).
- With two tangent-side limiters, put alpha=arcsin(2/5) and Phi=phi_L+phi_R. The entire scalar proof gives
  L_0(Phi)>U_0(Phi),
  where
  L_0= sqrt(15)/2+sqrt(4-r^2*cos(Phi+alpha)^2)-2
  and U_0=sqrt(2)+2(r-sigma)*sin(Phi/2).
  It holds on 0<=Phi<=pi/2-2alpha: L_0'<1/2, U_0'>1/2, and the right endpoint reserve is greater than 9/560. The exact fixed-sum minimum of the two square-root terms is proved there by comparing their derivatives, without an unwarranted global concavity assertion. If the two eta angles summed to at most pi/2, the actual normal coordinates would require the reverse inequality, a contradiction.

These three alternatives exhaust the minimum in (14), with equal limiter values permitted. This establishes (15) on the enlarged closed-tip-side domain by a literal application of the already proved scalar implication.

The complete routing also survives the new endpoints, with the following explicit boundary-strand check. The H roof is inside the inner disk. Each actual tip chain starts inside it and has strictly increasing norm up to its outer circle corner. Unless rho=0 and a=0, its nontrivial points after P have height strictly greater than h, so its annular portion is an ordinary interior crosscut of the upper strip. Two such disjoint crosscuts preserve the actual outer endpoint order on the inner circle.

If the left endpoint has rho=0 and a=0, its whole surviving chain P_L--Z_L instead lies on y=h. Its inner exit is exactly the left endpoint of the entire open cap y>h, at angle pi-arcsin(h/r). Every point of an extra's open interior has y>h, so its whole open r-circle arc already lies strictly to the right of that exit. The reflected statement handles a degenerate right chain. The other, strict-height strand, when present, supplies the other bound by its ordinary single-crosscut separation and the actual closing-side order. If both strands are degenerate, the two bounds follow directly from the open cap itself. Thus the disjoint interior-crosscut argument is used only for strands that really have that property.

The whole roof and both chains lie in y>=h in every case. Consequently every whole extra's connected open r-circle arc lies between the two actual exits, in an interval of length

    pi-eta_L-eta_R<pi/2.

A possible roof point on the inner circle is occupied and only reduces this interval. The strict quarter-clear arc theorem gives each extra an arc longer than pi/4. Two such disjoint whole arcs cannot fit. This proves the complete low-roof case.

## 6. Opposite high roof: the only changed comparison becomes weak and is sufficient

Suppose |A_H|>=r. The bounds X,Y<41/40 in (11) imply h>1/2 by the same exact roof comparison as the high-roof source; its rational reserve is 227/52800 using sigma>70/99.

Every whole extra lies above h, so each has one connected open r-circle arc longer than pi/4. If two extras were present, necessarily

    h<r/sqrt(2),                                    (16)

because the entire r-circle cap above height r/sqrt(2) has angular length pi/2.

Reflect so X<=sigma<=Y and x_0>=0. Put

    S_L=(X+h)/sqrt(2), S_R=(Y+h)/sqrt(2).

The two upper supporting lines of H give

    S_L^2+S_R^2=|A_H|^2>=r^2.

Thus the two open support caps on the inner circle are disjoint; each connected extra arc must lie entirely in one. The right cap has width at most pi/2, since

    Y+h=x_0+(h+sigma)>=|A_H|>=r.

It therefore holds at most one extra.

We exclude any extra arc in the left cap. If S_L>=r that cap is empty. Otherwise set

    S=S_L, v=sqrt(r^2-S^2), w=arccos(S/r).

The smaller port is strictly inside the inner disk:

    |P_L|^2=X^2+h^2<1/2+r^2/2=41/32<r^2.

Its actual tip chain has the unique exit (14), while the H roof exits at theta_H=3pi/4-w. The entire actual V is strictly left of x=x_0 by (10)--(12), including rho=1. The entire T is strictly right of that line.

Clip the upper occupied loop at x=x_0. Its clipping segment from A_H to the upper outer-circle point has norm at least r; the outer-circle portion has radius R>r. Under the two-extra assumption, |A_H|^2<97/32<4<R^2, so this is an ordinary Jordan loop without a roof pinch on the outer circle. The right tip introduces no crossing in it. The only inner-circle crossings are the H roof and the left norm-increasing tip chain. The upper inner-circle point on x=x_0 lies at or below A_H, outside the open pocket. Hence any left extra arc is routed into the actual interval between those two exits, whose length is at most

    max(0, pi/4+w-eta).                             (17)

This uses the whole occupied crosscut and the full tip obstacles, not radial visibility of a center.

It remains to prove eta>=w. This is the one place where the old open-side proof's strict height comparison must be weakened.

The actual exit height is now at least h by (12). If eta>=pi/2, the assertion is immediate since w<pi/2. Otherwise sine is increasing on the relevant interval.

If v<=h, the actual exit height is at least h>=v=r*sin(w). Thus eta>=w. Equality is retained, including the possible rho=0,a=0 geometry. Equation (17) is then at most pi/4, still insufficient for any extra arc of length strictly greater than pi/4.

Suppose v>h. The auxiliary point (-S,v) has

    N_*=b*S+a*v>N=b*X+a*h,
    K_*=b*v-a*S.

Indeed S>X follows from h>1/2 and X<=sigma, while v>h. If K_*<=0 then w<=phi<eta, proving the desired bound.

If K_*>0, the complete smaller-port scalar theorem applies with the unchanged actual X,h,phi:

    0<X<=sigma, h>1/2, v>h, K_*>0
      ==> (1+N)^2+K_*^2<4.                          (18)

Its closed scalar domain includes the present angle and all its boundaries; it contains no tip parameter rho. Compare (18) with the actual full circle equation (11):

    (1+N)^2+Z^2=R^2>4.

Both K_* and Z are positive, so K_*<Z. Put u=w-phi>0. Then

    r*cos(u)=N_*>N, r*sin(u)=K_*<Z.

Both upper limiters in (14) therefore exceed u, including the branch Z>=r. Hence eta>w in this alternative.

We have proved eta>=w throughout the full closed-tip-side domain. Equation (17) excludes every extra from the left cap, and the right cap holds at most one. This contradicts two extras and completes the high-roof case.

## 7. Whole-domain conclusion and its precise use

Adjacent and opposite distinct hub vertices exhaust the physical endpoint cover. The adjacent proof holds for the entire closed side interval. For opposite vertices, |A_H|<=5/4 and |A_H|>=5/4 cover all heights with their common threshold retained. All physical endpoint masks and original means survive every branch.

The theorem therefore proves closing-pocket capacity one for both endpoint tip-side parameters in [0,1], provided their original normals still strictly expose their H vertices.

The two genuinely new endpoint effects have been handled directly:

- rho=1 no longer supplies a strict factor by itself; strict hub exposure supplies a<1/sqrt(2), preserving the strict whole-tip separation used in clipping.
- rho=0,a=0 can give an exit at height h; the resulting weak angular comparison still leaves at most a 45-degree free interval, whereas each actual extra needs strictly more than 45 degrees.

No perturbation, approximation, continuity passage from a realizable family, or choice of a different application is used.

For an original D02 caller with these actual unchanged supports, the same literal graph U=2,V=1,T=3 and boundary path 1,0,5,4,3 has central capacity one, empty direct boundary-pair pockets, and three extras. The theorem supplies the closing capacity one, giving the usual total-capacity contradiction. The original strict certificate already excludes a point-only vertex/vertex contact whose chosen normal is an axis of that tip. The new endpoint geometry therefore does not itself add an original gate closure or eliminate a remaining strict free-normal feature.

Any future extremal-normal use must independently prove that its actual complete equilibrium and physical hypotheses survive. This manuscript supplies no such selection theorem and never silently reselects the original normal.

## 8. Exact operative sources and proof boundary

| Source | SHA256 | Exact use |
|---|---|---|
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Full component equations, actual port/circle order, adjacent/opposite hub coordinate calculations and the printed occupied-pocket winding argument, with the closed endpoint order checked in Section 2 above |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 at its actual all-normal, all-mask, side-endpoint scope |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | No original endpoint application belongs to its other boundary neighbor |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | No physical boundary cycle on at most six units and actual boundary order |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Lemma 1.1 only, degree-free actual boundary-pair moment signs |
| ADJACENT_HUB_VERTEX_TIP_OWNED_ENDPOINT_POCKET_CAPACITY_ONE.md | d68e442989665d423d0f98963901785f93d5d5077e76663223d67d0cf2f69649 | Force-free arc estimates, the explicit adjacent scalar calculation, and the actual routing argument after each open-side use is checked above |
| TIP_OWNED_HUB_BOUNDARY_PATH_ENDPOINTS_POCKET_CAPACITY_ONE.md | 82692b55bbf1ab90baaa485c0de45a83d68a745d7991a408e27a3a3bf7060732 | Complete pure low-roof limiter implication at the parameter scope printed in (15) |
| OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md | 121c24eea215f1d7de199467ba839aaeaa348007d4c4c57e54e21bca38c0b205 | Exact roof-height calculation and support-cap/clipping construction, with both closed endpoint changes re-proved above |
| OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_BOUND.md | 4d45da08bee1d7c8de15a0eb9f8cb9d2f4dacb811f5e77e070037140882df535 | Complete rho-free scalar bound (18), including all its closed domain endpoints |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Every-orientation connected open inner-circle arc longer than pi/4 beyond a strict quarter-height support |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Only the stated literal D02 central allocation |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Actual circle-corner order and direct boundary-pair pocket allocation |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Only the literal original D02 graph/load/three-extra join |

The original open-side theorems are not invoked outside their statements as unexplained black boxes. The source computations used as scalar or force-free geometric lemmas have their operative hypotheses printed above; every place where the old physical proof used a strict side parameter is checked at the new endpoints.

No original force, mean, physical body, circle corner, coefficient or normal is changed. No pose sample, angle mesh, computational exclusion certificate, Lean compilation, CI, remote write or shared-ledger mutation is used.

