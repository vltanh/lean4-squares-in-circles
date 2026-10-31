# Independent review of the complete parallel unique-circle perpendicular-hub feature

Date: October 28, 2026 UTC. Reviewer: cycles.

**Verdict: PASS for the entire stated feature and its literal original D02 join. No repair is required.** The result covers a parallel V with one physical circle corner, perpendicular original U-to-V and U-to-W axis normals, every W frame and original VW normal owner, every original shared UV mean, and all physical masks at the other boundary units. It does not by itself close the whole original D02 row.

## 1. Exact reviewed source, complete inputs, and independence

The complete target read and checked is:

    PERPENDICULAR_HUB_PARALLEL_UNIQUE_CIRCLE_TIP_COMPLETE_POCKET_EXCLUSION.md
    f7ac7950b4a4e12877fa4e330d18240f4e857b676b607b5c83db9cbe675a7cc7

Every direct source in its input table was read in full. All sixteen current source hashes were checked.

| Complete direct source | SHA-256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| RECOVERED_ADJACENT_SHARED_HUB_BOUNDARY_TRIANGLE_D02_FULL_FEATURE_EXCLUSION.md | 44b78ba21f68b23387aeb30a5b5fb3c0ea2bea352c538a4782ebdf382f30ce88 |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 |
| ADJACENT_CIRCLE_TIP_WIDE_LEFT_CAP_INNER_ARC_MATCHING.md | 14ca7fbac82fb74b698ab17df01eb1783ce558e75fa8b5a528bbb8fb7bba76c1 |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

The new proof is root's. I did not supply its new parallel-V mean torque identity, its two side-endpoint exits, its complete interior W-mask argument, its direct weak support-endpoint extension, or its new actual geometric join.

Some older inputs have my authorship. In particular, the conditional adjacent-shared pocket source c3f95f4c965513179f7e001113ffd2e3da67c267f0334ea3af394d422e7fad01 underlies 44b78ba2, and the older coincident-port and strict-common-vertex sources 18ad8dbd and 5edbfff4 underlie 5a95c325. This review does not relabel an author's check of those sources as an independent review. Their separate current review chains were checked:

| Complete accepted review/adoption read | SHA-256 |
| --- | --- |
| REVIEW_RECOVERED_ADJACENT_SHARED_TRIANGLE_ACTUAL_CHART_PENTAGON_2026_10_28.md | 30ab3d6d62d9921bf41d7e1dfbc2a76aa6a878a5d19aeaa45fa425ab5e48581d |
| REVIEW_RESTORED_ADJACENT_SHARED_TRIANGLE_POCKET_PENTAGON_2026_10_28.md | fba85b3321b275eaeb9e83f6a563d583d3801eb43e5b5a3d7b83284acd9112bb |
| ADOPTION_FULL_RADIUS_RADIAL_BARRIER_AND_ADJACENT_SHARED_ROOT_2026_10_28.md | 4a8d68e06234f078a7871638fcac9bd6efb40c28203473670abb7dd802c416c6 |
| REVIEW_LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_PENTAGON_2026_10_28.md | 14053d3894f36653357e0210a2ae9ee8c83c578dddfb2a59a180bdccdf008e42 |
| REVIEW_RADIAL_INNER_CORNER_QUARTER_SIDE_BOUND_HOUSE_2026_10_28.md | c59537d7ee575437f4460b4eb525fa0a194ec1753c58c96bf5885a1c1013412d |
| REVIEW_ADJACENT_CIRCLE_WIDE_LEFT_CAP_MATCHING_HOUSE_2026_10_28.md | 67a4e69fb5e60cc2c4862b246510aef135b7986dbb6beac29a537a91bd10a02a |

The common-point review records the fresh independent reviews fff8eed21f20dca2d7c600303c1ca71002af23a2c668313fa6df84ecfe99714c and d4e6a48ab776043418ba5aefc3ba340503e318300c7ee6bc254cb7079c87ba63 of those two older inputs. The adjacent-shared chart operative in 44b78ba2 is the current reconstructed a78f0c4cc5ae037e1dae6358090981f6e21a136193e941fe9368da847493cf72, not the unavailable historical chart.

The independence claim here is a complete separate audit of the new f7ac theorem and all its literal joins, with the above independent chains supplying the older coauthored inputs.

## 2. Exact original setting and the parallel-W exit

The theorem retains the complete positive component with unloaded U3, boundary path V,W,...,T, exactly the three spokes UV,UW,UT, true V2 and T2, true W3, and all remaining actual forces and units. Its radius is the original same-nine interval 2<R<=sqrt(1105/256). The geometry assumes the original UV and UW normals are perpendicular own U axes and V is parallel to U. V has one physical circle corner; physical uniqueness is distinct from assigning one nonzero coefficient to a two-corner mask.

After the global rotation, UV is North and UW is East. If W is also parallel to U, an isolated parallel vertex-to-vertex contact cannot carry an axis-valued selected normal under the original strict point-contact convention. Consequently both physical UV and UW contacts have positive length on adjacent U sides. This is exactly the feature of the complete current 44b78ba2 assembly. Its original mean intervals, including endpoints, are unchanged. The proof does not reselect an isolated normal, infer positive contact length merely from an arbitrary axis-valued vector, or invoke a conditional chart without its full placement cover.

Thus the entire parallel-W branch exits before the nonparallel chart. The strict-normal convention is a stated original certificate convention, not a newly imposed geometric restriction.

## 3. The nonparallel chart and the original V equations

For nonparallel W, the geometric normal-cone calculation in BOWTIE Section 2 gives the original V-to-W normal

    m=(u,-v), u>=0, v>=0.

Only that geometric calculation is used; W is not treated as a loaded degree-two tip. The full true V2 equation gives a circle resultant strictly Northwest, so u>0 and the unique physical V corner and full unit are

    Z=(-x,y),  x>1/2, y>1/2,
    V=[-x,1-x] x [y-1,y],
    x^2+y^2=R^2.

Put H=y-1. Since the actual UW normal is East, W's minimum-x support is its unique vertex Q=(L,q), and H-1<=q<=H. If v>0 the V support for m is its lower-right vertex M=(1-x,H). If v=0, the common contact is W's unique minimum-x vertex on V's right side; q<=H from U and q>=H from V force q=H. Thus VW is the same actual singleton M in the closed v=0 case too. No unknown shared VW mean has been replaced by a convenient endpoint.

Write the unchanged UV mean as P=(p,H), and D=1-x-p. Its actual side interval gives 0<=D<=1. If D=0, P=M belongs to W; the all-owner common-point theorem 5a95c325 excludes this. Its radius and genuine V2/boundary-W premises hold, so D>0.

Taking V torque about the actual M, with its unique positive circle coefficient Lambda, gives exactly

    mu*D=Lambda*(y-x).

The circle-vector determinant is det(M,Z)=y-x, and the UV force sign is South on V. Consequently y>x and y>sqrt(2). The force components give

    nu*u=Lambda*x,
    mu=Lambda*(y-x*v/u)>0,
    D=(y-x)/(y-x*v/u).

Since D<=1 and the denominator is positive, 0<=v/u<=1. This keeps the actual D=1 mean endpoint and the v=0 normal endpoint. It is a consequence of the full retained mean and torque, not a chosen point-force model.

## 4. Every actual W support feature, including beta=1

The complete inward frame at W's minimum-x vertex is

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1,
    W=Q+[0,1]f+[0,1]g.

Because m.g=u*S+v*C>0, the actual common point M lies on the g-minimum side:

    M=Q+beta*f, 0<=beta<=1,
    L=1-x-beta*C, q=H-beta*S.

This is an exhaustive physical support statement. The endpoints beta=0 and beta=1 retain normal cones and every possible original side owner. Only when 0<beta<1 is the original m necessarily g.

I independently checked the whole beta=1 exit. M and Q are already actual shared core points. For each of the other two actual corners, write its displacement from Z as (A,-B), with A,B>0. Its radius deficit is

    2*A*x+2*B*y-A^2-B^2.

For fixed actual R, A*x+B*sqrt(R^2-x^2) is concave on [1/2,R/sqrt(2)]. Its minimum is at one of those two endpoints; the actual x is in that interval because y>x. The radius dependence at each endpoint has the correct positive sign.

For M+g, A=1+S and B=1+C. At x=1/2, the half-deficit lower bound is

    a0-1-S/2+(a0-1)*C > a0-3/2 > 0,
    a0=sqrt(15)/2.

At the diagonal endpoint, it is

    (2+S+C)*sqrt(2)-3/2-S-C
    =1/2+(sqrt(2)-1)*(2+S+C)>0.

For Q+g, A=1+S-C>0 and B=1+S+C. The corresponding endpoint bounds are

    (a0-3/2)*(1+S)+(a0-1/2)*C>0,
    2*(1+S)*(sqrt(2)-1)>0.

All four actual W corners are strictly inside the circle, contradicting W's physical boundary status. This excludes the entire far side endpoint, without a W force equation or a provisional choice of its physical circle corner.

## 5. The beta=0 endpoint is handled directly

At beta=0, Q=M. The source does not apply the interior relation m=g. Assume x>=1. Since y>x, the identity

    (xy)^2-(R^2-1)=(x^2-1)*(y^2-1)>=0

gives x+y>=1+sqrt(R^2-1). Hence

    |M|^2<= (sqrt(R^2-1)-1)^2 < 1,

using R^2<=1105/256<5. M, M+f and M+g are then strictly inside the disk: their distances are at most |M|+1<2<R.

For the last corner M+f+g, set A=1+C+S and B=1+C-S. Both are positive and A^2+B^2=2(A+B). Its radius deficit is exactly

    2*A*(x-1)+2*B*(y-1)>0.

This contradicts W being boundary. Therefore x<1 in the entire beta=0 branch, including every original normal in its support cone. The later parameter beta*C is exactly zero there.

This argument is independent of the selected VW owner, any fictitious radial V, and any upper bound on an auxiliary comparison height.

## 6. Interior beta: complete W mask and the pure scalar comparison

For 0<beta<1, m=g and the mean torque bound gives C<=S. Put gamma=C, eta=S, tau=1-beta, h=eta-gamma and j=eta+gamma. The source retains eta=gamma.

The quantity

    m_f=gamma*(1-x)+eta*(y-1)

is strictly positive. This is direct for x<=1. For x>1 it equals eta*(y-x)+(eta-gamma)*(x-1), which is also positive. The V circle has f-coordinate m_f+h>0 and g-coordinate -v0, where v0=eta*x+gamma*y; M's g-coordinate is z=j-v0.

Both possible nonpositive W-center-coordinate regimes, including their zero ties, are excluded before claiming uniqueness:

* If the g-center coordinate is nonpositive, v0>=j+1/2. Since eta>=gamma and y>x, v0<=j*(x+y)/2. Thus x+y>=2+1/j>R+1/2 and |M|<R-1. The possible minimum-g farthest corners are Q, which is an actual U contact, and M+tau*f, whose distance is below R. Q cannot be a circle point: that would make the actual touching triangle U,V,W consist of three physical boundary units, excluded by the full boundary-triangle input. A tied g-center does not escape this contradiction.
* If the f-center coordinate is nonpositive after the first exclusion, m_f<1/2 and Z.f<3/2. Therefore v0>sqrt(7)/2>5/4. The remaining possible farthest minimum-f, maximum-g corner has coordinates satisfying
  -1<m_f-beta<=-1/2 and 1/2<z+1<5/4.
  Its norm squared is below 41/16<4<R^2. The f-center equality is included.

Thus W has the unique physical circle corner M+tau*f+g. All its possible original physical masks have genuinely been covered. No W3 equilibrium was omitted or reduced.

The actual equal-radius equation is

    2*A1*x+2*B1*y=A1^2+B1^2,
    A1=1+eta+tau*gamma,
    B1=1+gamma-tau*eta.

Here A1>B1>0, even when eta=gamma, since tau>0. At x=1 the line has height 1-(1-tau^2)/(2*B1)<1, contradicting y>x if x>=1. Consequently x<1.

The squared norm along this line decreases for x<=y, because its derivative has the sign of B1*x-A1*y<0. At x=1/2 the auxiliary line height is therefore at least as large in radius as the actual Z. The resulting auxiliary quantity d_* satisfies

    d_*=F(gamma,tau)>sqrt(R^2-1/4)-1>187/200>11/12.

This is a lower bound only. The proof never transfers the original upper radius bound to d_*.

The Sections 4--5 argument of 37f0f207 is invoked only in its printed pure algebraic scope:

    beta*gamma>=1/4  implies  F(gamma,tau)<11/12.

Its full continuous parameter cover and endpoint bounds were checked. The contradiction gives beta*C<1/4. There is no application of a theorem about a physical radial tip to a counterfactual V, and no use of a counterfactual two-force equation.

Combining Sections 5 and 6 yields x<1 and 0<=beta*C<1/4 for every surviving W feature.

## 7. The weak a=x support endpoint is proved, not assumed

The original wide matching source 14ca7fba states a>x. The new proof needs equality when beta=0. Section 7 explicitly rechecks its entire operative argument under a>=x; it does not cite a strict theorem at equality.

For a hypothetical T circle corner with Z_x>=-x, the actual Southwest support implies w_x>=0 and w_y<=0. The genuine diameter and support bounds therefore yield the closed box

    -x<=Z_x<=sqrt(2)-x,
    y-2-sqrt(2)<=Z_y<=b<y-1.

If x>=1/sqrt(2), then |Z_x|<=x while |Z_y|<y, using y>sqrt(3)>1+1/sqrt(2). Thus the radius contradiction stays strict. If x<1/sqrt(2), the same norm expansion as in 14ca7fba has a strict negative reserve, using x>=1/2 and y>9/5; the upper bound is below -1/25. Both alternatives allow a=x.

All later center and angular estimates use only a>=x>=1/2. Their strictness comes from the independent strict bounds 1/sqrt(2)<17/24, the radius lower bound, the retained b bounds, and the strict comparison margins. In the short interval the actual support-point norm remains below r0 and the distance-box contradiction remains strict. Neither the four bottom-side height intervals nor the left-side derivative cover needs a>x.

I checked the original full wide source alongside this extension. Its conclusion is conditional on actual cap and angular routing. The new source correctly supplies that routing later; it does not silently import it from scalar hypotheses.

## 8. The actual original third port satisfies the full matching interface

The original full unloaded U equation has positive North and East terms, so UT is strictly Southwest. Its actual original application is uniquely forced to

    P_T=(L-1,H-1)=(-a,b),
    a=x+beta*C>=x, b=y-2.

There is no shared UT mean to choose at this strict vertex. The bounds just proved give

    1/2<x<1,
    sqrt(3)<y<121/60,
    0<=beta*C<1/4,
    y-2<=b<y-1,
    b<1/60<37/150.

In the short x interval a=x+beta*C<x+1/4<x+41/100, as required by the wide matching proof. All its remaining radius, actual containment, physical-boundary T and strict Southwest support premises are original premises.

Therefore the proved weak extension gives every actual physical T circle corner strictly left of x=-x; c_T,x<0; the correct center-angle lift in (90,270) degrees; theta_T<230 degrees; and an actual open-interior radius-9/8 point of V at angle phi with

    theta_T<phi+100 degrees.

All physical T corner coefficients, including zero coefficients at other circle corners, remain. The argument is about every actual circle corner, not only the full resultant direction.

## 9. Occupied crosscut, original means, and whole-extra routing

The actual VW moment is

    det(M,m)=-(1-x)*v-(y-1)*u<0,

because x<1, y>1 and u>0. The full physical boundary-pair moment theorem and angular-neighbor order make the entire boundary path clockwise. The closing gap through U is its counterclockwise complement.

The source uses the actual left extreme P_V=(-x,H) of the UV common segment for a geometric barrier. This point is genuinely in both squares: U's top interval is

    [-x-beta*C,1-x-beta*C],

and 0<=beta*C<1/4<1. It is not necessary for P_V to be the retained force mean P, and the source never replaces P in the equations from Section 3.

The occupied path goes from the actual V circle corner down its left side to P_V, across the actual U top to its northwest corner, down the actual U left side to P_T, then through T to its gap-facing physical circle corner. For beta=0 the top step has zero length and is omitted; the vertical pieces join without self-intersection.

The complete U3 touching-return separation theorem gives T closed-disjoint from V and W. U meets T only at P_T because the original UT normal is strict Southwest. The V-U barrier and the T segment therefore have no unaccounted crossing. Every T circle corner is strictly left of the V wall.

The actual U is strictly inside the outer circle. Indeed a=x+beta*C lies in (1/2,5/4), the maximum absolute U horizontal coordinate is a, and y>sqrt(3)>3/2 makes the maximum absolute vertical coordinate y-1<61/60. Thus

    max_U |z|^2 < 25/16+(61/60)^2 < 4 < R^2.

The last reserve is exactly 2527/1800. Together with the physical boundary-corner order, this makes the relevant circle arc and occupied crosscut an actual left-cap barrier.

The original center/contact crosscut can be deformed to this barrier within the actual closed union U,V,T, sliding its geometric UV junction along the real shared side. This is allowed precisely because it changes no original force mean. Every extra open interior avoids the closed core union. The deformation consequently preserves its winding and its side of the original closing gap. For weak junctions, compact inner subsets have positive separation from the core, so compatible small routings preserve their side and closure retains the whole extra. Additional physical contacts cannot transfer a portion of an extra across the occupied barrier.

Thus every whole extra in the actual closing pocket lies in x<=-x. Its center satisfies c_E,x<=-x-1/2<-1. The cap is proved for the entire original extra, not assumed from the position of its center or from radial visibility.

## 10. True T2 angular routing and the capacity contradiction

Let the final boundary-path predecessor be B. Its actual T-to-B moment is positive in the boundary order. The full true T2 torque gives det(P_T,n)>0 for the unchanged U-to-T normal n. The proof applies the proper-concurrence lemma at T only; it never shortens W3 or another vertex.

P_T and n lie in the left half-plane. Their determinant fixes the same lifted angular order. The complete proper concurrence is

    q=P_T+ell*n=lambda*F_T, ell>=0, lambda>0.

The argument allows concurrence outside T, both physical masks, all zero individual circle coefficients, and every original other application. It uses the positive resultant direction, not an unsupported assertion q in T. The full corner/resultant cone gives

    arg(P_T)<=arg(F_T)<theta_T+15 degrees,

and the same upper bound for every actual T circle corner.

Along the V and U portions, the determinant signs are x>0, y-1>0 and a>0. Hence the occupied barrier's argument increases. The chosen T segment stays in the convex cone between its endpoint directions. The full cone aperture is below 155 degrees, so its two defining half-planes also contain the bounded pocket. This establishes the complete angular routing required by the wide matching source for the same actual extras already routed to the cap.

That source's centered-arc proof now applies literally. Each such extra has center radius greater than one and contributes its whole closed 40-degree arc at radius 9/8 inside its open interior. T has the corresponding arc. The center-angle upper cone excludes an extra at or above theta_T, since it would be within 15 degrees of T. The cap places each extra strictly beyond the chosen actual V interior point phi, with a gap exceeding 20 degrees. Two extras would force the consecutive strict gaps

    extra_1-phi>20 degrees,
    extra_2-extra_1>40 degrees,
    theta_T-extra_2>40 degrees.

Their sum contradicts theta_T-phi<100 degrees. These are actual minor gaps in the proved common lift. Closed arcs inside open interiors supply strict separation at equality endpoints. Thus the real closing exterior pocket has capacity at most one.

## 11. Literal original graph, exhaustive feature cover, and accounting boundary

For M6.B6.HEXAGON.D02.L01345 the unchanged graph is the rim 01,12,23,34,45,50 with the single positive chord 02. The original load set is {0,1,3,4,5}. The literal substitution is

    U=2, V=1, W=0, T=3,
    boundary path 1,0,5,4,3.

The actual degrees are U3,V2,W3,5_2,4_2,T2. The original U is unloaded; every path body is positively loaded and physically boundary. All three completion squares remain.

The original outer embedding supplies exactly the central triangle and pentagon, the direct boundary-pair exterior pockets on 10,05,54,43, and the closing exterior pocket through U=2. The whole central capacity theorem permits at most one extra in total in the central faces; every direct pair exterior pocket is empty; the theorem just proved permits at most one in the real closing pocket. The full occupied embedding and weak-junction routing allocate every extra. Thus at most two completion units are possible, contradicting the actual three.

The frame and contact cover is complete:

1. Parallel W uses the whole adjacent positive-shared feature.
2. Nonparallel W has the full beta interval [0,1].
3. Beta=1 is excluded by actual-corner concavity.
4. Beta=0 has its direct all-owner geometric exit and the proved a=x endpoint extension.
5. Interior beta has its forced original side normal, full W-mask cover, pure scalar comparison, and unchanged mean-dependent V equations.

No owner, circle-center tie, mean endpoint, weak geometric junction, or physical zero-coefficient corner is lost. This closes the entire parallel-V, unique-physical-circle feature of the original perpendicular-U-axis interface.

It gives no whole original D02 checkbox by itself. The physical-two V branch and the nonparallel-V features need their separate complete sources. An eventual union must preserve the same original certificate and graph rather than move a mean or reselect a normal between branches.

## 12. Method and final decision

I independently derived the new force and torque identities, the two continuous endpoint exits, both full W-mask exclusions, the line-radius scalar comparison, the weak support-endpoint extension, the actual cap and angular routing, and the literal three-extra allocation. Exact rational arithmetic was used only to verify displayed reserves and source hashes; for example 5-1105/256=175/256, 4-41/16=23/16, (121/60)^2-(1105/256-1/4)=31/57600, and 187/200-11/12=11/600.

No numerical pose sampling, mesh certificate, Lean compilation, CI, workflow, changed physical mean, normal reselection, force deletion, shared ledger edit, commit or remote write was used.

**Complete new theorem and original feature join: PASS, with no repair requested.**

