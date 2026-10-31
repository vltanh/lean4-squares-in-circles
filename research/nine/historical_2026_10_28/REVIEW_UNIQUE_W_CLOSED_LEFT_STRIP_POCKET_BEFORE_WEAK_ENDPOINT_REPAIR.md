# Independent full review of the unique-W closed left-strip pocket exclusion

Date: October 28, 2026 UTC. Reviewer: two_circle_v_review continuation.

**Verdict: PASS for the entire stated local capacity-one theorem, its
closed strip endpoints, and the literal original D02 feature exit. No
repair is required. This source alone does not close the complementary
unique-W strip, the unique V-owned interface, or the original D02 row.**

Reviewed complete source:

    UNIQUE_W_RETURN_LOW_ROOF_AND_CLOSED_LEFT_STRIP_POCKET_EXCLUSION.md
    SHA256 eff3bead6a2a1f4672b6818c7bde7b1f050b395f8e6c1926f218b563f13cf053

This independent review is pinned to those exact bytes. I read the whole
source and the operative proofs of all thirteen direct inputs. In
particular I checked the complete new polynomial bound, actual physical
paths and masks, both angular cases, and full completing-unit routing.
I did not author this manuscript, its X_0 bound, its roof proof or its
closed-strip pocket argument. Root contributed to the low-port route
and A_T>1 extension, as the manuscript discloses; root adoption is an
author/integration check. This is the separate independent review.

Subsequent discussions about a possible broader correlated-angle theorem
are not part of this source or the verdict below. They cannot silently
enlarge the scope of this pinned closed-strip theorem.

## 1. Entire component and original interfaces

The local component retains U unloaded of true positive degree three,
the full loaded path V=B_1,W=B_2,...,B_k=T with 3<=k<=6, and exactly
the three original spokes UV,UW,UT. V and T retain their true positive
degree two; all actual internal degrees and their other path forces
remain. The exterior order is U,V,W,...,T,U.

The unique-W entry is the already proved nonparallel interface in which
the original VW normal is a W axis different from the UW normal, V has
one physical circle corner, UV and UW are genuine singleton contacts
in externally owned side interiors, and UT is the sole U-owned spoke.
The new local theorem additionally requires the actual UT intersection
to be a singleton. It does not infer that property merely from an
application mean. All circle weights, including individual zero weights,
and every original shared mean on the remaining path are retained.

The circle-centered U chart is

    U=[N_j-1,N_j] times [N_e-1,N_e],
    P=(N_j,N_e), Q_U=(N_j,N_e-1),
    P_T=(N_j-1,N_e-t), 0<t<1.

The only extra local range condition is the closed strip
|N_j-1|<=29/128. In particular no origin containment, central disk
containment or additional positive contact is assumed.

## 2. Full unique-W chart and the new X_0<2/3 bound

I independently reviewed the full unique-W chart source at its current
pin before this review. Its all-mask derivation of the physical W corner
is valid; none of its conclusions rests on a false W2 or T2 equation.
The operative inherited facts used here are

    1/2<x<1, sqrt(3)-1<d<61/60, y=d+1,
    x^2+y^2=R^2, A=1-x>0,
    X_0=x*(kappa*d+A)/(kappa*y-x), 0<X_0<x,
    kappa>1, kappa>(d^2-A^2)/(2*A*d),
    P=(-X_0,d), e=(C,-S_0), j=(-S_0,-C),
    0<S_0<alpha<1/sqrt(2), C>epsilon>1/sqrt(2).

For x<2/3, the new bound follows immediately from X_0<x. On the
entire remaining closed interval 2/3<=x<1, the manuscript proves
d<1 using Q-4/9<4. The exact reserve is 295/2304. Also

    D=2+(2-3*x)*d>1.

The factor kappa*y-x is positive. The inequality X_0<2/3 is therefore
exactly kappa*D>x*(5-3*x); this multiplication does not reverse a sign.
Using the inherited strict lower bound on kappa reduces it to E>0 for

    E=(d^2-A^2)*D-2*A*d*x*(5-3*x).

Both displayed two-variable polynomial identities in the source check
exactly. With q=R^2-4=x^2+d^2+2*d-3>=0, they yield

    E>=2*x*(-1+2*x-(3/4)*x^3)
       +q*((3/2)*x^2-(3*x-2)*d).

The tangent-line bound d<=1+(q-x^2)/4 is valid because the proposed
upper bound on y is positive and its squared excess is (q-x^2)^2/16.
The coefficient Q_0=3*x^2-12*x+4 is strictly negative throughout the
interval, so substituting that upper bound gives the stated lower bound
on E. The cubic factor is concave and has endpoint values 1/9 and
1/4. The second factor exceeds (3/2)*(x-1)^2+1/2. Hence E>0
throughout, including x=2/3. This proves X_0<2/3 without a parameter
mesh or an unexamined orientation range.

## 3. Every point of the actual roof is inside the inner circle

The unchanged incoming application satisfies

    |P|^2<4/9+(61/60)^2=5321/3600<(5/4)^2,

with strict reserve 19/225. The upper-left U vertex L=P+j satisfies

    |L|^2=|P|^2+1-2*N_j<|P|^2,

because the closed strip gives N_j>=99/128>1/2.

The actual occupied U arc is the clockwise arc through Q_U and the
bottom side. The original internal UW spoke and the full exterior order
fix this choice. Its complementary actual arc is P--L--P_T.
The genuine terminal T2 torque, with T's actual boundary-path neighbor
and its full original application mean, gives

    det(P_T,n_UT)>0, P_T.e=t-N_e<0.

Thus 0<t<N_e. The squared norm on L+s*e has derivative 2*(s-N_e)<0
throughout 0<=s<=t. P_T is inside the inner circle, and convexity puts
the whole two-segment roof strictly inside. No force at W has been
deleted to obtain this sign.

Writing P_T=(s,A_T) in U coordinates gives |s|<=29/128 and A_T>0.
Since P_T belongs to the actual physical boundary unit T,
|P_T|>=R-sqrt(2)>2-sqrt(2). The exact strip comparison proves
A_T>1/2, including both closed strip endpoints. It follows that every
point of the roof has positive height at least A_T.

## 4. Actual V gap chain and its one inner crossing

In V's frame the actual gap-facing chain is

    P=(-X_0,d) -> M=(-x,d) -> Z_V=(-x,d+1).

Since 0<X_0<x and d>0, the norm increases strictly on each segment.
Its initial point is inside radius 5/4 and its final point is on radius
R>5/4. Hence there is exactly one inner crossing, including the possible
crossing at the shared vertex M. The proof does not assume M is inside
the inner disk.

In the U display the unique physical V corner has coordinates

    Z_V=(C*y-S_0*x, C*x+S_0*y).

The first coordinate is greater than (y-x)/sqrt(2), and hence greater
than (sqrt(3)-1)/sqrt(2)>1/2. Its second coordinate is positive.
The entire gap chain has height at least N_e>A_T: the P--M increment
is a positive multiple of (-S_0,C), and M--Z_V increments n=(C,S_0).
These are bounds on the actual occupied path, not substitute radial
segments introduced without a physical containment argument.

## 5. Every physical T circle corner is above the horizontal axis

The actual UT singleton and its strict ownership make P_T T's uniquely
exposed east vertex. Its two inward unit directions have negative
horizontal components, with opposite vertical signs. Thus every actual
T point satisfies

    s-sqrt(2)<=X<=s, A_T-1<=Y<=A_T+1.

The center height is greater than A_T-1/2>0. If any actual T circle
corner had Y<=0, it would have -1/2<Y<=0 and

    |X|<=29/128+sqrt(2)<29/128+10/7<5/3.

Its squared norm would be less than 109/36<4<R^2, a contradiction.
This treats every physical circle corner, including a zero-weight
corner of a two-corner mask. It does not assert that all of T lies
above the axis.

The selected actual gap-facing T circle corner has X<=s<=29/128<1/2.
Together with Z_V's first coordinate greater than 1/2 and the proved
positive heights, this places V before T on the upper semicircle.
The real loaded boundary path has the opposite clockwise orientation.
Thus the upper circle arc between the gap-facing corners is the actual
closing outer arc, with no intervening body of that path. The physical
corner order, rather than a resultant-only order, supplies this join.

## 6. Whole incircle arc and one actual T crossing

The actual T center radius r_T lies in

    R-1/sqrt(2)<=r_T<91/60, r_T>129/100>5/4.

For beta=atan(5/16), the centered closed halfwidth-beta arc on radius
5/4 lies in T's open incircle. The manuscript checks the whole arc,
using cos(beta)=16/sqrt(281)>477/500 and the exact upper-end reserve
161/36000 below squared distance 1/4. The squared distance increases
with r_T on the permitted interval, so this is a complete continuous
radius bound, including both angular endpoints of that closed arc.

Let E_T=(5/4)*C_T/r_T. The path P_T--E_T--Z_T lies in the actual
T and in the open upper half-plane. P_T is strictly inside the inner
circle, so the first open segment stays strictly inside. Every actual
physical circle corner Z of T has

    Z.C_T/r_T>=r_T+1/2>5/4.

Therefore every point after E_T on the second segment lies strictly
outside the inner circle. There is exactly one T crossing, E_T.
The argument covers every physical T mask and does not require a
special orientation of its own axes.

## 7. Both terminal-height angular cases and all endpoints

The rigid pi/2 rotation used by the proof sends the actual upper
half-plane to the left half-plane and P_T to (-A_T,s). The height
bound on the V chain supplies

    theta_V>=theta_A=acos(-A_T/(5/4)).

The roof containment already gives 0<A_T<5/4, so this comparison
is defined on the stated lifted semicircle.

For 0<A_T<=1, the complete force-free low-port lemma applies literally:
its point (-A,-h) is (-A_T,s), so h=-s and
|h|<=29/128<27/100. The lemma permits every actual point of an
arbitrary-degree boundary unit; the current T2 is therefore within
its full scope. I read its complete squared-distance argument, including
the correct half-plane proof, the positive quantities before squaring,
the monotone quadratic bound and its 113/50000 reserve. It gives the
required strict inequality even at A_T=1 and the closed h endpoints.

For 1<A_T<5/4, the manuscript's separate extension is valid. The
rotated center has negative first coordinate and second coordinate of
absolute value less than 29/128+71/100<1. Its radius exceeds129/100.
Consequently any angle below the negative horizontal ray has offset
less than pi/3; in all cases theta_T<4*pi/3. Also
theta_A>acos(-4/5)>3*pi/4 and beta>pi/12. These bounds give

    theta_T-beta-theta_A<pi/2.

The two height ranges exhaust the actual permitted A_T and include
their common endpoint. Therefore the whole closed strip satisfies
theta_T-beta-theta_V<pi/2, not merely a sampled set of heights.

## 8. Whole occupied routing and the capacity conclusion

Full unloaded-U3 strict touching-return separation makes V and T
closed-disjoint. UV and UT are their distinct actual physical singleton
contacts with U. The three actual V/U/T paths therefore form a simple
occupied crosscut, meeting only at the prescribed endpoints. Together
with the actual upper closing circle arc they give a Jordan boundary
in the open upper half-plane.

Each boundary path has exactly one inner-circle crossing; the entire U
roof lies strictly inside. Their disjoint annular strands preserve the
proved outer order, so theta_V<theta_T in the rotated left-semicircle
lift. The semicircle endpoints are outside the bounded pocket. Hence
the pocket's actual inner-circle part is bounded by these two crossings.
The occupied homotopy lies in the original closed V,U,T and avoids each
extra's open interior, preserving its actual bounded-side assignment.
Every whole extra's complete open inner-circle arc is therefore routed
inside (theta_V,theta_T).

The full one-hub path theorem applies with the component's true degrees
and unchanged spokes. It makes every whole closing-pocket extra strictly
quarter-clear. The force-free inner-arc theorem consequently gives each
one connected open arc longer than pi/4. The complete closed beta arc
inside T removes the interval adjacent to theta_T, leaving all extra
arcs in (theta_V,theta_T-beta). Its length is less than pi/2, so two
such disjoint arcs cannot fit. This is a whole-pocket capacity bound,
not a comparison of square centers. Extra zero-weight contacts may only
subdivide the permitted region.

## 9. Exact original application and residual

The literal D02 identification remains U=2,V=1,W=0,T=3 with loaded
path 1,0,5,4,3 and true U3,V2,W3,5_2,4_2,T2. All three original
extras are retained. The original triangle/pentagon central union has
capacity one, the four direct boundary-pair exterior pockets are empty,
and the closed-strip theorem gives closing capacity one. Their complete
physical allocation cannot accommodate all three extras.

This excludes the entire closed strip |N_j-1|<=29/128 in the unique-W
interface. The already reviewed near-hub theorem gives N_j<1+delta
with delta<29/128. Therefore every remaining unique-W certificate must
have N_j<99/128, and its near side must instead satisfy |N_e-1|<delta.
No complementary domain or whole original row is credited here.

## 10. Exact checks and direct pins

The new two-variable identities were independently checked by exact
rational polynomial expansion. The following displayed reserves also
check exactly:

    295/2304, 19/225, 15839/409600, 31/2688,
    35/36, 161/36000, 39/256, 41/10000, 9923/66564.

These checks verify printed algebra and strict comparisons. They are
not pose enumeration, numerical angle search or a new computational
exclusion certificate.

All thirteen direct source hashes match:

| Source | SHA256 |
| --- | --- |
| UNIQUE_TIP_DISTINCT_W_RETURN_FULL_MASK_AND_ORIGIN_MARGIN.md | 83b0b942ad474befbf9fca3315337df2116809b32e3f9015820a9c8783660785 |
| BOUNDARY_TERMINAL_CENTER_LOW_PORT_ARC_ANGLE_BOUND.md | d94502aed4091098a1fa23801284a734f9f42989f130a5f0d9b0f464bb7497e6 |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| D02_ENTIRE_TWO_CIRCLE_TIP_EXCLUSION_AND_EXACT_UNIQUE_TIP_RESIDUAL.md | 8aba649f47a66527beff0a0a12db6fdcb7f8782b54f734baf190d8b8523732b8 |
| CRITICAL_NEAR_HUB_CENTRAL_OCCUPANCY_AND_D02_TWO_SUPPORT_STRIPS.md | 46810a719f06c5153f1340f5fbc846427a1c1d5d2e50fb69dac9f1e067806e41 |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

No source repair or alteration was needed. No Lean/Lake invocation,
build, CI/workflow dispatch, original-ledger edit, commit, remote write
or pull-request merge was performed for this review.
