# A parallel two-circle tip at perpendicular hub axes has closing-pocket capacity at most one

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed hand theorem for the entire parallel-tip physical-two-circle feature, submitted for independent review.** Every return owner, the complete original UV shared mean, all physical W and T circle masks, and every completing unit remain. The proof complements the nonparallel theorem without treating a variable mean as a fixed vertex application.

Put Q=1105/256 and work in 2<R<=sqrt(Q).

## 1. Entire original component and theorem

Retain the actual complete positive component consisting of an unloaded true-degree-three U and the positively loaded boundary path

    V,W,B_3,...,B_(k-1),T, 3<=k<=6,

with exactly the three original spokes UV,UW,UT. Its actual outer-face order is U,V,W,...,T,U. The true degrees are V2,W3,T2 and degree two at the other path bodies. All original force and torque equations, physical contacts, original normals, positive magnitudes, shared means, physical circle corners and individual zero coefficients remain, as do every other actual unit.

Assume the actual U-to-V and U-to-W normals are perpendicular own side axes of U. Assume V is parallel to U and has two physical circle corners. Impose no owner or fixed-application assumption on VW.

**Theorem.** The actual closing exterior pocket through U between V and T contains at most one additional whole unit square.

For the literal original D02.L01345 row, this excludes the entire stated feature: the complete central union has capacity one, the direct boundary-pair exterior pockets are empty, and three original extras cannot fit in total capacity two. The graph join is printed in Section 10.

## 2. Complete physical V mask cover

Rotate and, if necessary, reflect the entire original data about O so the U-to-V and U-to-W normals are North and East. Write

    U=[L-1,L] x [H-1,H].                              (1)

Because V is parallel to U and touches its top support, V's bottom side is y=H. The actual UV intersection may initially be a singleton or a segment; its original mean is not changed.

The complete geometric normal-cone argument in BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md, Section 2 only, puts the actual V-to-W normal m in the closed Southeast quadrant. That geometric statement uses no degree-two equation at W. With original magnitudes mu,nu>0, the full actual V force equation is

    F_V=mu*North-nu*m,
    (F_V)_x<=0, (F_V)_y>0.                            (2)

A parallel unit with two physical circle corners has one zero own center coordinate and one nonzero one. Its outward resultant, with both physical corners and every nonnegative weight split retained, can satisfy (2) only in the radial North or radial West orientation. A radial South mask has both corner y coordinates negative; a radial East mask has both x coordinates positive.

Put

    d=sqrt(R^2-1/4)-1,
    187/200<d<61/60.                                  (3)

If V is radial West, then

    V=[-d-1,-d] x [-1/2,1/2], H=-1/2.

The whole W lies in x>=L and physically meets V, so L<=-d. The actual U lower-left corner is (L-1,-3/2), whose squared norm is at least

    (d+1)^2+9/4=R^2+2.

This contradicts the containment of U. Thus the entire radial West alternative is impossible, regardless of the VW owner or physical W mask.

The only remaining full physical mask is

    V=[-1/2,1/2] x [d,d+1], H=d.                      (4)

No individual outer-corner weight is assumed positive. The two physical corners are still present even when one has zero coefficient.

## 3. Two axis returns and every aligned W are excluded locally

First, m=South is impossible by the complete radial half-strip theorem: every physical boundary neighbor of the actual V in (4) has minimum y strictly greater than d-1, whereas a neighbor beyond V's inner radial side normal has maximum y=d and width at least one.

If m=East, then the minimum x support of W is simultaneously the VW line x=1/2 and the UW line x=L. Hence L=1/2.

The full U force equation, using both original positive North and East magnitudes, makes U-to-T strictly Southwest. Its original U support is therefore the singleton

    P_T=(L-1,d-1).

Whenever L=1/2, this actual point has norm strictly less than R-sqrt(2). Indeed

    |P_T|^2-(R-sqrt(2))^2=-4d-2+2sqrt(2)R<0,         (5)

because

    (2d+1)^2-2R^2=2d^2-3/2>0

by d>9/10. Both sides being compared are positive. Any actual boundary unit containing P_T has a circle point at distance at most sqrt(2), so must satisfy |P_T|>=R-sqrt(2). This contradicts (5).

It remains to take m strictly Southeast. Since V is aligned, its actual VW support is now the singleton

    M=(1/2,d).                                       (6)

If W is parallel to U, a strictly Southeast minimum-support normal exposes W's upper-left corner. Thus M_x=L, again L=1/2, and (5) excludes the entire aligned-W alternative. Its original UW mean has not been substituted for a corner in an equation.

## 4. One physical support classification covers every remaining VW owner

Let W be nonparallel to U. Its minimum-x support is the unique actual vertex Q_W=(L,q), with d-1<=q<=d because Q_W is the original UW contact. Name its actual inward orthonormal axes

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1,
    W=Q_W+[0,1]f+[0,1]g.

For every strictly Southeast m, one has m.g>0. The actual minimum-m support of W therefore has g-coordinate zero. Consequently the actual point (6) has the exhaustive representation

    M=Q_W+beta*f, 0<=beta<=1,
    L=1/2-beta*C, q=d-beta*S.                        (7)

If beta=0, then L=1/2 and the original T diameter contradiction applies. If beta=1, then

    min_W y=d-S-C<=d-1,

because S+C>=1. W contains the actual point M of radial V, so the radial half-strip theorem again contradicts its physical boundary status. This includes both a free normal at that W vertex and an endpoint-valued W-owned side mean.

Thus 0<beta<1. Because M lies in the relative interior of the actual side, its unchanged minimum-support normal is necessarily

    m=g.

Every originally possible VW owner has been covered: either its physical endpoint was excluded above, or its actual normal is proved to be W-owned. No normal has been reselected and no free contact has been silently relabeled.

The complete force-free radial inner-corner neighbor theorem applies literally to (7), with gamma=C, eta=S and the same actual M,d,R. It gives the uniform strict bound

    0<beta*C<1/4.                                    (8)

It derives W's physical corner from containment, and retains the entire beta interval. It uses no equation at V or W. In particular no nonparallel-V resultant inequality is imported into this parallel chart.

Equations (7),(8) now prove that the actual UV intersection is the nontrivial segment

    [-1/2,L] x {d}, L>1/4.

Its original UV mean is arbitrary on that whole segment, including either endpoint, throughout the remaining proof.

## 5. The actual T port and every physical T circle corner

The complete original U3 force still points U-to-T strictly Southwest. Its unchanged actual application is

    P_T=(-a,b),
    a=1/2+beta*C in (1/2,3/4),
    b=d-1 in (-1/10,1/60).                           (9)

The original U-to-T normal n has both coordinates strictly negative. No formula involving a replacement UV mean is needed.

Let Z be any physical circle corner of T, including a corner with zero individual coefficient. If Z_x>=-1/2, then w=Z-P_T has w_x>0. Since P_T is an actual minimum-n support point of T, n.w>=0; the two strict signs of n force w_y<0. The actual diameter gives |w|<=sqrt(2)<3/2. Therefore

    -1/2<=Z_x<1, -8/5<Z_y<1/4,
    |Z|^2<1+64/25=89/25<4<R^2.

This is impossible. Hence every actual physical T circle corner obeys

    Z_x<-1/2.                                       (10)

Let c_T be the actual center, r_T=|c_T| and sigma=1/sqrt(2). The actual port and boundary status give

    |c_T-P_T|<=sigma, r_T>=R-sigma>31/24.

Its first coordinate is negative. Otherwise (9) and sigma<17/24 give

    0<=(c_T)_x<5/24,
    |(c_T)_y|<1/10+17/24=97/120<5/6,

contradicting r_T>31/24, since

    (31/24)^2-(5/24)^2-(5/6)^2=67/72>0.

Thus its angular lift theta_T lies in (90,270) degrees.

## 6. A full radius cover for the actual T angle

All angles here are exact rational multiples of pi. The exact elementary comparisons used below and in Section 7 are proved in Section 8 of PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md. Their use is algebraic and has no nonparallel-V premise.

First prove

    theta_T<216 degrees.                             (11)

If the center height is nonnegative this is immediate. Otherwise use

    d>18729/20000, sigma<99/140, r_T>181/140,
    a<3/4<91/100, b>-1271/20000, |P_T|<1.

The first comparison follows from the exact squared reserve 64559/400000000 at R=2. Also arg(P_T)<210 degrees: when b<0, |b|/a<1/5<tan(30 degrees), and when b>=0 its argument is at most 180 degrees.

For theta in [216,270] degrees, the squared distance of a point to P_T increases with theta, because the angular difference from P_T lies in (0,pi). It increases with its radius above 181/140 because |P_T|<1. The lower comparison point is therefore the radius-181/140 point at angle 216 degrees. The exact inequalities cos(36 degrees)>29/36 and sin(36 degrees)>47/80 put both its coordinates below the lower coordinate bounds for P_T. Consequently

    |c_T-P_T|^2
      >[(181/140)(29/36)-91/100]^2
        +[(181/140)(47/80)-1271/20000]^2
       =1/2+10826627041/6350400000000>1/2.

This contradicts the actual center-to-port bound and proves (11).

If d>=24/25, then b>=-1/25. The exact radius comparison gives R>101/50 and r_T>919/700. For negative center height,

    |(c_T)_y|/r_T<523/919<4/7<sin(35 degrees),

where the rational reserve is 15/6433. Hence the stronger bound is

    theta_T<215 degrees when d>=24/25.               (12)

Again nonnegative center height satisfies the conclusion directly. These two complete d intervals include their shared threshold.

## 7. Actual interior V points over the same complete radius cover

Put rho=9/8. For d<=24/25 take the radius-rho point at angle phi=116 degrees. For d>=24/25 take phi=115 degrees. Both points lie strictly inside the unchanged actual V.

At 116 degrees the coordinates are (-rho*sin(26 degrees),rho*cos(26 degrees)). The exact bounds sin(26 degrees)<4/9 and cos(26 degrees)>64/75 put its first coordinate above -1/2 and its second above 24/25>=d. The other two V bounds are immediate.

At 115 degrees use sin(25 degrees)^2<43/240 and cos(25 degrees)^2>197/240. The exact strict reserves are

    1/4-rho^2*(43/240)=119/5120,
    rho^2*(197/240)-(61/60)^2=1211/230400.

Thus the point lies between V's two vertical sides and above its inner side for every d<61/60. Its height is below rho<d+1. The two respective angle bounds (11),(12) give exactly

    theta_T<phi+100 degrees.                         (13)

These are actual points of int V, not new applications or chosen circle weights.

## 8. The actual closing crosscut lies in one half-plane and pointed cone

The retained boundary-pair moment is

    det(M,m)=det((1/2,d),(S,-C))=-C/2-d*S<0.

The degree-free physical boundary-pair moment rule and actual angular-neighbor order make the entire loaded path V,W,...,T clockwise. Its closing exterior gap through U is counterclockwise from V to T.

Use the actual gap-facing V circle corner Z_V=(-1/2,d+1), follow V's left side to P_V=(-1/2,d), then the genuine U top side left to its northwest corner, then U's left side down to P_T, and a path inside T to its gap-facing physical circle corner Z_T. Every point of this occupied crosscut lies in x<=-1/2 by (9),(10). The interior of the T path can be chosen strictly left of that line.

The complete unloaded-three-force touching-return theorem gives T closed-disjoint from V and W. The actual U-to-T support is its strict southwest vertex, so U intersects T only at P_T. The V and U portions just chosen meet only at P_V even though the original UV intersection has positive length: the V part is its left side, and the U part leaves P_V to the left. The crosscut is therefore simple.

The actual closing circle arc from Z_V to Z_T is the corresponding left cap arc. Equation (10) puts every T circle corner in its open cap, while the actual boundary path takes the complementary clockwise order. U is circle-clear: its whole box has |x|<3/4 and |y|<61/60, giving squared norm below 9/16+(61/60)^2<4. Thus no extra physical circle spoke from U changes the closing gap.

The bounded Jordan region is in x<=-1/2. It is the original closing pocket: the center/contact crosscut deforms inside the same actual closed U,V,T union to the displayed path. The geometric endpoint on the shared UV segment moves to its gap-facing extreme P_V only in this occupied barrier; the original UV mean stays unchanged in every equation. Each point of an extra's open interior avoids that closed union, so its winding is preserved. Compact interior subsets handle weak contacts and zero-weight junctions, and closure recovers the whole-unit assertion.

Consequently every whole extra E in this pocket has

    (c_E)_x<=-1.                                    (14)

The true T2 torque and counterclockwise final boundary-neighbor moment give det(P_T,n)>0. Proper concurrence with that actual boundary neighbor gives

    q_T=P_T+ell*n=lambda_T*F_T,
    ell>=0, lambda_T>0.

Both P_T and n are in the open left half-plane. Their determinant sign orders n counterclockwise from P_T, so arg(P_T)<=arg(F_T)<theta_T+15 degrees. Every physical T circle corner has the same strict upper bound by the complete physical corner/resultant cone theorem.

The V and U portions of the occupied crosscut have increasing argument: their successive determinant signs are 1/2, d, and a, all strictly positive. The T portion may be kept in the convex angular cone between its endpoints. Its lower angular bound is arg(Z_V), since both P_T and all T circle corners lie in the left cap and after Z_V. Therefore the actual closing boundary and its bounded region lie in the pointed cone

    arg(Z_V)<=theta<=theta_T+15 degrees.              (15)

Its aperture is below pi because arg(Z_V)>90 degrees and theta_T+15<231 degrees. Both defining half-planes therefore contain the bounded region. In particular (15) holds for every actual extra center. No inside-T concurrence assertion is used.

## 9. Two actual extras contradict the complete 100-degree bound

The universal contained-unit center bound gives |c_E|<91/60. Together with (14), the exact angular comparisons give

    130 degrees<theta_E<230 degrees.

For completeness, cos(theta_E)<-60/91<-13/20 and sin(40 degrees)<13/20. The latter follows from cos(40 degrees)>19/25 by the triple-angle cubic (reserve 753/31250), followed by the squared reserve 1/10000. These same exact comparisons appear in the reviewed nonparallel pocket source.

Every E has center norm at least one. The complete centered-forty-degree arc theorem puts its whole closed radius-rho arc of halfwidth 20 degrees in its actual open interior. It also applies to T, since r_T>31/24. Hence any two such units have minor center separation strictly greater than 40 degrees.

Equation (15) gives theta_E<=theta_T+15 degrees. If theta_E>=theta_T, its minor separation from T would be at most 15 degrees, impossible. Thus theta_E<theta_T.

The actual V point in Section 7 has angle phi<=116 degrees, while theta_E>130 degrees. Its presence in int V and the closed centered arc in int E force theta_E-phi>20 degrees.

If two extras E_1,E_2 occupy the pocket, order their angles increasingly. All following differences are genuine minor gaps by the just-proved bounds:

    theta_E1-phi>20 degrees,
    theta_E2-theta_E1>40 degrees,
    theta_T-theta_E2>40 degrees.

Summing gives theta_T-phi>100 degrees, contradicting (13). This proves the whole pocket theorem.

## 10. Complete literal original D02 feature and scope

For M6.B6.HEXAGON.D02.L01345 retain the entire rim 01,12,23,34,45,50, chord 02 and positive circle-load set {0,1,3,4,5}. Use U=2,V=1,W=0,B_3=5,B_4=4,T=3. The true degrees are U3,V2,W3,5_2,4_2,T2 and all three original completing squares remain. The same-nine analytic lower-radius theorem supplies R>2.

If the two original hub normals on 21 and 20 are perpendicular U axes, and V=1 is parallel to U with two physical circle corners, the theorem applies to every original VW normal, every original UV mean, and every physical W/T mask. The radial West, South/East return, aligned-W and side-endpoint cases have all been excluded on their whole domains, leaving exactly the pocket just bounded.

The central triangle and pentagon have combined capacity one. The direct exterior boundary-pair pockets on 10,05,54,43 are empty. The closing pocket through U has capacity one. The actual occupied planar graph and boundary spokes allocate all three original extras to those regions, with the compact-interior convention at weak junctions. Capacity two contradicts their number three.

This is the complete parallel-V physical-two-circle feature. The complementary nonparallel physical-two-circle features have their separate exact owner proofs. A whole perpendicular-interface or full D02 conclusion still requires all unique-circle V cases; no such closure or original checkbox credit is asserted here.

## 11. Exact operative inputs

| Source | SHA256 | Exact use |
| --- | --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2 only, geometric complete Southeast normal cone with arbitrary actual degrees |
| RADIAL_HALFSTRIP_FULL_RADIUS_BOUNDARY_SUPPORT_COROLLARIES.md | e8cb01fa67033056433ce210ae0c286700606533cae5db18fc641e8d568804f8 | Entire physical radial-S boundary-neighbor support barrier and inner-normal exclusion |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Actual intermediate W side feature forces beta*C<1/4 without a V force restriction |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Only its complete exact elementary angle comparisons and the explicit centered-angle comparison in Section 13; its nonparallel physical entry is not used |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Actual U3 and physical VW make T closed-disjoint from V,W |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Lemma 1.1 only, full actual boundary-pair moment signs |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | True T2 proper concurrence, all physical masks, actual boundary predecessor |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only, complete corner/resultant cone and actual center bound |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Actual closed centered arcs in every E and T |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Actual loaded boundary-path direction and order |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Actual circle-corner order and empty direct exterior pockets |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole original central capacity one |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual embedding and weak-junction face allocation |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, loads, degrees and three extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Unchanged same-nine lower-radius exit |

The proof keeps every original square and equation. No sampled pose, numerical optimization, finite orientation mesh, new computational exclusion packet, normal reselection, changed original side mean, force deletion, artificial degree-two neighbor, Lean compilation, CI, workflow or merge was used.
