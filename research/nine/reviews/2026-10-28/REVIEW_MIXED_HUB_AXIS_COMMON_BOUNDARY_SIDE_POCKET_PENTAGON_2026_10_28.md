# Independent review: mixed hub axis and common boundary side, both adjacent and radial tip masks

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## 1. Verdict, exact target and review boundary

**PASS, without a requested repair**, for the complete proposed pocket theorem and its literal original D02 feature consequence in:

MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_ADJACENT_OR_RADIAL_TIP_POCKET_CAPACITY_ONE.md

Target SHA256:

    94f9d4850e408c3b076605f8738126d32dd3856899ba3fe330d132b8d029ccb0

I read the entire frozen target and every complete direct source in Section 12 below, checked their exact current hashes, and independently audited the actual support chart, original force and torque equations, both physical V masks, all W mask regimes, continuous scalar comparisons, terminal support, occupied crosscut, all-extra routing and literal original graph join. The verdict concerns these exact bytes.

The theorem retains the stated feature premise that the original U-to-W and V-to-W normals are equal. It covers a nonparallel V with either its unique adjacent physical circle corner or its complete physical-two-circle mask. It proves genuine closing-pocket capacity at most one and excludes that entire feature of M6.B6.HEXAGON.D02.L01345. It does not close the unique-opposite V mask, parallel V, unequal UW/VW normals, or the entire original row.

The reviewer authored the earlier wide-left-cap matching argument and the repaired perpendicular two-circle source supplying elementary angle comparisons. The target explicitly discloses its adaptation of that method. I do not present that shared predecessor as an independently discovered argument. I did not author the target's new common-side chart, full-U3 tilt constraint, positive-height proof, or replacement terminal-center estimate; I checked those independently after the target was frozen. I also checked the full current matching and routing arguments at their actual premises, rather than transferring the predecessor's acceptance.

No Lean compilation, CI, pose sampling, numerical exclusion certificate, normal reselection, force deletion, shared-ledger edit or remote action formed part of this review. Exact rational arithmetic below checks displayed algebraic identities and reserves only.

## 2. Original supports determine the complete common-side chart

The unchanged original normal UV=North and nonparallel V make UV a singleton at V's unique bottom vertex P. The original strict Northeast UW normal m=(b,a) makes Q=(L,H) its actual U application, independently of any force magnitude or W frame. With P=(L-D,H), the support inequality at the actual V point P+e_1 is

    b*c+a*s <= b*D <= b.

This correctly forces gamma=b*s-c*a>0. If gamma were nonpositive, w=a/b would be at least s/c and the displayed inequality would give D>=1/c>1. Consequently m has V-own components (eta,-gamma), with eta=b*c+a*s>0, so the actual VW maximum is the unique vertex M=P+e_1. Equality of the two original W minimum-support values gives D=eta/b=c+w*s.

The two distinct physical points Q and M lie on one minimum-m face of W. Their vertical difference s is positive, so this face has positive length and m is an actual W axis. The complete side chart is therefore

    f=(-a,b), alpha=s/b,
    M-Q=alpha*f,
    W=M+[-beta,1-beta]f+[0,1]m,
    alpha<=beta<=1, tau=1-beta.

This retains both original application points and every allowable side endpoint. In particular, **the lower W corner M-beta*f need not equal Q**. I checked all later uses of this chart: the target never substitutes that corner for the actual UW application Q.

The full original unloaded U3 force equation makes UT strictly Southwest, hence its unchanged U application is P_T=(L-1,H-1). The full torque about P_T is

    mu*(1-D)+omega*(a-b)=0.

The endpoint D=1 is actually impossible: it would force a=b and then D=c+s>1. Thus delta=1-D>0, b>a, and

    0<w<1, delta<1-c, w<s/(1+c),
    n is a positive multiple of -(1,q),
    q=w+(1-w)/delta>1.

All three original positive pair forces have been used. There is no manufactured degree-two hub or altered application. The identities alpha=gamma+w*eta, kappa=eta-w*gamma and gamma*alpha+eta*kappa=1 follow exactly from the two orthonormal frames.

## 3. Entire V mask cover and actual concurrence

P and M are actual shared points. Two interior-disjoint contained squares cannot share a containing-circle point, by their common short inward radial segment. Therefore neither shared point is a physical V circle corner.

For physical-two V, this excludes every mask except the two corners on its upper e_2 face. Equal physical corner norms force the actual own-coordinate chart

    V=[-1/2,1/2] x [d,d+1],
    P=(-1/2,d), M=(1/2,d),
    d=sqrt(R^2-1/4)-1.

Every individual original circle coefficient, including either possible zero coefficient, remains. The exact lower bound d>18729/20000 is valid because

    15/4-(38729/20000)^2=64559/400000000>0.

For the unique adjacent corner, the target correctly writes

    V=[-x,1-x] x [y-1,y],
    Z_V=(-x,y), x>1/2, y>1/2,
    P=(-x,y-1), M=(1-x,y-1).

The original full V2 resultant is mu*North-nu*m. Its dot product with f is mu*b>0. The actual pair-line intersection is

    q_V=P+(gamma/b)*North.

The proper-concurrence input applies to true loaded V2 because its actual neighbor W is physically boundary. In this unique mask q_V=lambda*Z_V with lambda>0. Its first coordinate gives lambda<1, so K=1/(1-lambda)>1 and

    x=K*gamma*alpha,
    y=K*(1-gamma*kappa),
    Z_V.f=K*(eta-gamma).

The positive f-component of the full resultant therefore implies eta>gamma. The identity y-x=K*(eta-gamma)*kappa>0 is exact. These signs are obtained from the original equations, not from a picture or an assumed center order.

The radial endpoint x=1/2 has y=d+1>x directly. No inside-concurrence claim for a two-circle body is introduced anywhere in this mask cover.

## 4. All W masks and the uniform tilt bound

For the unique adjacent mask, the target checks both W center-coordinate signs before choosing a circle corner.

If its m-center coordinate is nonpositive, then v=eta*x+gamma*y>=eta+gamma+1/2. The inequalities eta>gamma and y>x give

    v<(eta+gamma)*(x+y)/2,
    x+y>2+1/(eta+gamma)>R+1/2.

Hence |M|<R-1. Both actual minimum-m side corners, M-beta*f and M+tau*f, lie within distance one of M and are strictly inside the disk. At least one is farthest in the alleged regime, including the center tie, so physical boundary status is contradicted. This argument correctly works when the lower side corner is different from Q.

If the f-center coordinate is nonpositive, the positive m-center coordinate already obtained gives the farthest candidate M-beta*f+m. The estimates K*(eta-gamma)<3/2 and v>sqrt(7)/2>5/4 place its two own coordinates in the printed intervals, and its norm squared is below 41/16<4. This also covers the tie.

Thus both center coordinates are positive and W's unique physical circle corner is

    Z_W=Z_V+(A_1,-B_1),
    A_1=1+eta+tau*gamma>B_1=1+gamma-tau*eta>0.

The exact same-radius equation is

    2*A_1*x+2*B_1*y=A_1^2+B_1^2.

No W force is discarded; its true degree remains three. Its physical mask was forced by actual containment and geometry alone.

For the radial V mask, the full force-free quarter-side theorem applies directly to the actual W chart, with d>11/12, gamma,eta>0 and beta>=alpha>0. It supplies this same corner equation and beta*gamma<1/4.

For the unique mask, the target uses a separate algebraic comparison: along the circle line, decreasing x to 1/2 increases squared norm while y>x. The comparison height d_* therefore exceeds sqrt(R^2-1/4)-1 and hence 11/12. It is not assigned a physical upper radius bound. I checked the signs of all derivative comparisons for

    F(gamma,tau)=(tau^2+tau*gamma+eta)/
                  (2*(1+gamma-tau*eta)).

F increases in tau, decreases in gamma along eta=sqrt(1-gamma^2), and increases under independent enlargement of eta while its denominator is positive. The three closed gamma intervals exhaust beta*gamma>=1/4 and give strict upper bounds 11/12, 101/122 and 87/106 respectively. The final reserves are 65/732 and 61/636. The strict first bound comes from eta<1, including its interval endpoints.

The actual side relation beta>=alpha and the strict full-U3 inequality D<1 then give

    beta*gamma>=alpha*gamma
       =s^2-w*c*s>1-c.

Thus c>3/4, s<2/3 and w<8/21<2/5 on both entire physical masks. The radial mask also acquires eta>gamma from c>s. These are genuinely uniform constraints on the actual tilt, not necessary conditions obtained after changing the configuration.

Finally the circle line has height

    y_1=1-(1-tau^2)/(2*B_1)<1

at x=1. Together with y>x, this proves x<1. Hence the shared coordinate range is exactly sufficient:

    1/2<=x<1, sqrt(3)<y<121/60,
    0<y-1<9/8<y.

## 5. Actual terminal support and the new positive-height proof

The target transforms the original Southwest U vertex and normal, without choosing a new T support:

    P_T=(-a_T,b_T),
    a_T=x+s+c*delta>x,
    b_T=y-1-c+s*delta.

Because q>1 and c>s, the original normal has both own-V components strictly negative. The physical point P_T is a genuine minimum support of the actual T for this normal, with every T owner and mean retained.

The printed bounds

    y-2<b_T<y-1, b_T<13/30

follow from the actual c,s,delta range. This upper bound is weaker than 37/150 in the reviewer's wide-cap predecessor. The target does not silently import that predecessor's center-left conclusion.

The additional positive global height H is needed for the occupied U-top path to turn in the required angular direction. It is proved here. In the radial case H=dc-s/2>41/120. In the unique case, with t=gamma/b=s-wc,

    Z_V=(-K*s,K*(c-t)),
    H=K*(c-t)-c,
    R^2=K^2*((c-t)^2+s^2),
    0<t<=s, s*t<1/4.

If H<=0, the whole s<=1/2 interval gives R^2<13/4. On s>=1/2, q_0=c^2 lies in (9/16,3/4]; the concave quadratic 28*q_0-20*q_0^2-9 has positive endpoint values 27/64 and 3/4. This proves 4cs>1+2s^2 and consequently c-t>s/2, giving R^2<15/4. Both contradict R>2. Every denominator and squared comparison is positive on its stated interval. This is a complete continuous proof of H>0, including the common s endpoint.

## 6. Every physical T corner and the new center-left estimate

The proof of every physical T circle corner lying strictly left of x=-x uses only actual membership, actual Southwest minimum support and unit diameter. It includes circle corners whose individual coefficient is zero.

For a hypothetical corner to the right, the displacement from P_T has positive horizontal and negative vertical components. The target's two x intervals then give a norm contradiction: for x>=1/sqrt(2), both coordinate magnitudes are bounded by x,y with a strict vertical bound; for x<1/sqrt(2), the resulting deficit is strictly below -1/25. No direction or force at T is changed to obtain these inequalities.

The center estimates

    |c_T-P_T|<=1/sqrt(2),
    r_T>31/24 and r_T>181/140

are valid for any physical T mask and frame.

The new center-left proof explicitly handles the actual b_T<13/30 scope. If s>=5/24, a_T>x+s>=17/24>1/sqrt(2). If s<=5/24, the actual tilt gives c>39/40, delta<1/40 and b_T<3/64, while b_T>-7/25. Thus |(c_T)_y|<1. A nonnegative first coordinate would also be below 5/24, contradicting

    (31/24)^2-(5/24)^2-1=5/8.

Both common endpoints are covered. The lifted angle is therefore in (90,270) degrees. The lower port-height bound and the exact 691/905<49/64<sin(50 degrees) comparison prove theta_T<230 degrees. The rational reserve 121/57920 and the triple-cosine value -111/65536 are correct.

This is the decisive scope check: the source proves its own center lift before using the matching method, rather than applying the narrower wide-cap statement outside its domain.

## 7. Complete continuous inner-arc matching

At radius rho=9/8 the two limits

    phi_L=acos(-x/rho),
    phi_B=180 degrees-asin((y-1)/rho)

are in (90,180) degrees. Every angle strictly between 90 degrees and their minimum is an actual open-V point. The positive-y and right-face inequalities follow directly from the full coordinate range, including x=1/2.

I checked both entire comparisons theta_T-phi_L<100 degrees and theta_T-phi_B<100 degrees.

The four closed y intervals for the bottom face have upper T angles 230,225,220,215 degrees and lower V endpoint angles 130,125,120,115 degrees. The strict rational and trigonometric reserves survive every common interval endpoint. The high-y interval correctly strengthens the actual radius lower bound before improving the center estimate.

For the left face, the derivative estimate

    d/dx asin(v_m(x))<875/1161<8/9<=phi_L'(x)

holds on the entire x interval, with m=0 or m_0=207/16000. Its reserve 157/1161 is correct. The three branches are exhaustive:

- s>=17/100 supplies the improved port height with reserve 121/80000 and the initial 216-degree comparison.
- x>=9/16 uses m=0 and the exact phi_L=120-degree endpoint.
- The remaining closed rectangle has c>197/200, delta<3/200, a_T<x+37/200<x+41/100 and |b_T|<1/10.

The last rectangle therefore has the actual port inside radius r_0 and an argument below 210 degrees. The comparison radius-r_0 point is strictly left of and below the entire enlarged port box. All signs of D_x,D_y and their derivatives are valid uniformly, including the endpoint conventions. The squared-distance comparison increases with x, with half-derivative above 19/300. Its initial reserve above 1/2 is

    10826627041/6350400000000.

Squared distance from the actual port increases with radius above r_0 and with angle on the required interval. Thus theta_T cannot reach theta_0. This argument covers the actual larger port-height domain; it does not require a hidden 37/150 hypothesis.

Only the elementary exact angle inequalities are imported from the repaired two-circle predecessor. No physical-two force inequality is transferred to the unique mask.

## 8. Actual pocket assignment and full terminal angular cone

The actual VW moment is negative in both masks: it is -(K-1)*(eta-gamma) in the unique mask and -gamma/2-d*eta in the radial mask. The degree-free moment-sign and angular-neighbor results therefore orient the unchanged boundary path clockwise and its closing gap counterclockwise from V to T.

The actual U port order is established from P in its top-side interior, Q its Northeast vertex and P_T its Southwest vertex. The closing U arc passes through the Northwest vertex. This is the original embedding order, not an inference from a replaced W corner.

The full unloaded-three-force touching-return theorem applies at the actual U3 and the real VW contact, and makes T closed-disjoint from V and W. Together with the singleton UV and strict-support UT intersections, this validates the simple occupied crosscut through V's left side, the actual U top/left boundary and T. Its entire path and genuine closing circle arc lie in x<=-x. T's final portion can be chosen strictly left, since both endpoints are there and T is convex.

U being physically circle-clear is correctly deduced from the impossibility of three mutually touching physical boundary units U,V,W. It is not deduced from U's zero load. Actual circle-corner order puts the other core boundary intervals on the complementary path side.

The deformation from the original center/contact crosscut stays inside the actual closed V,U,T union, fixes P and P_T, and preserves winding at every extra interior point. The compact-interior convention handles weak junctions without moving any original force mean. Thus the whole of every actual closing-pocket extra, not merely a selected point, lies in the left cap. In particular

    (c_E)_x<=-x-1/2, |c_E|>=x+1/2>=1.

The angular upper bound uses the full true T2 equation with its actual boundary predecessor. The sign of the original terminal pair moment gives det(P_T,n)>0. Proper concurrence gives q_T=P_T+ell*n=lambda_T*F_T with ell>=0 and lambda_T>0, including both physical T masks, zero individual coefficients and an outside concurrence.

The actual point and normal are in the open left half-plane, so this determinant orders their lifted directions. The full physical-corner/resultant cone bounds both arg(P_T) and every physical T corner by theta_T+15 degrees. Along the earlier crosscut, the V determinant is positive, the U-top determinant is the now-proved H>0, and the U-left determinant is cx+s(y-1)+delta>0. The T segment stays in the convex angular interval of its endpoint directions.

The genuine closing Jordan boundary and its region therefore lie in the pointed cone from arg(Z_V) to theta_T+15 degrees. Its aperture is below pi. This proves the required upper bound for every actual extra center without assuming radial visibility of a nonconvex pocket.

## 9. All extras, centered arcs and the literal original feature

The actual farthest-corner inequality gives every unit center norm below 91/60, with reserve 31/57600. The left-cap center estimate then implies theta_E>phi_L>phi in the established lift. The cosine comparison is valid for all x<1.

The full centered-forty-degree theorem applies to T and every pocket extra. These are closed radius-9/8 arcs inside the respective open squares, so distinct units have strict minor center separation greater than 40 degrees. The terminal cone prevents an extra center from lying at or beyond theta_T. The actual open-V point at phi prevents an extra center from lying within 20 degrees after phi.

Two extras would consequently require successive strict gaps exceeding 20,40,40 degrees. Their whole interval is below 100 degrees by the complete matching proof, so all gaps are minor and their sum is impossible. This proves capacity one for all whole actual extras and all their frames.

The original D02 join is literal:

    rim 01,12,23,34,45,50; chord 02; loads {0,1,3,4,5};
    U=2, V=1, W=0, B_3=5, B_4=4, T=3.

Its degrees remain U3,V2,W3,5_2,4_2,T2. The same-nine lower-radius theorem is applied only to the full retained nine-unit packing. The actual central triangle and pentagon have combined capacity one; the four direct pair pockets are empty; the actual closing pocket has capacity one. The original occupied plane graph and circle spokes assign all three connected extra interiors to these regions, including weak junctions. At most two can be allocated, a contradiction.

This is complete feature exclusion. It does not by itself justify any whole-row, whole-gate or whole-proof closure.

## 10. Exact arithmetic independently checked

In addition to checking the symbolic derivatives and signs, I recomputed the displayed rational identities with exact fractions. Representative values are:

| Check | Exact value |
|---|---|
| First alleged gamma-interval upper comparison | 11/12 |
| Second alleged gamma-interval upper comparison | 101/122 |
| Third alleged gamma-interval upper comparison | 87/106 |
| Radial d lower squared reserve | 64559/400000000 |
| y upper squared reserve | 31/57600 |
| Actual mixed b_T upper comparison | 13/30 |
| Radial H lower comparison | 41/120 |
| Positive-H quadratic endpoint values | 27/64 and 3/4 |
| Small-s c squared reserve | 43/7200 |
| Small-s b_T upper comparison | 3/64 |
| Center-left squared reserve | 5/8 |
| Angle-lift ratio reserve | 121/57920 |
| Triple-cosine polynomial at 49/64 | -111/65536 |
| Large-s improved-height reserve | 121/80000 |
| Small-rectangle c squared reserve | 7/8000 |
| Small-rectangle b_T upper margin below 1/10 | 3947/60000 |
| Left matching derivative reserve | 157/1161 |
| D_x upper and lower reserves | 141/14000 and 107/11200 |
| D_y initial and derivative reserves | 24643/840000 and 12/175 |
| Initial squared-distance reserve above 1/2 | 10826627041/6350400000000 |
| Universal center upper-radius reserve | 31/57600 |

These checks corroborate the printed continuous proofs; they are not a replacement for any continuous domain argument.

## 11. Required preservation and remaining scope

No source repair is requested. The literal endpoint x=1/2, beta=1, beta=alpha, common scalar-interval endpoints, every T owner, both T physical masks, and every original allowed circle-weight split have been retained or excluded by a printed strict inequality. W remains true loaded degree three and all original means remain fixed. A containing-circle corner with zero individual coefficient is still treated as physical.

Adoption should retain the target's exact restricted feature label: UV is a U axis, UW is strict in the adjacent U vertex cone, the original UW and VW normals agree, V is nonparallel, and its physical mask is adjacent unique or radial two-circle. Its whole conclusion is a useful simultaneous exclusion of those two mask domains, not closure of the remaining D02 domains.

## 12. Complete direct sources read and exact pins verified

| Complete source | SHA256 | Audited operative scope |
|---|---|---|
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Actual full radial W theorem; only printed scalar inequalities at comparison d_* |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 at true V2/T2 with actual boundary neighbors |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full actual U3 and touching V,W |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Degree-free original moment sign only |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Actual full corner/resultant cone and center radius |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Full closed centered arcs at actual T and every extra |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Original physical boundary order and boundary-triangle exclusion |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Physical corner order and empty direct boundary-pair pockets |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Combined original central capacity and full region assignment |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original selected physical embedding and weak-junction convention |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Actual graph, loads, degrees and three extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Lower-radius entry on all nine original units only |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Exact elementary angle comparisons in Sections 8 and 13 only |

The method predecessor ADJACENT_CIRCLE_TIP_WIDE_LEFT_CAP_INNER_ARC_MATCHING.md has SHA256 14ca7fbac82fb74b698ab17df01eb1783ce558e75fa8b5a528bbb8fb7bba76c1. Its stronger port-height premise is not an operative hypothesis or a transferred conclusion here. The target prints and proves the replacement estimates in full.

