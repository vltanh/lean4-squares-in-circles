# Independent review of the complete opposite-tip high-roof pocket theorem

Date: October 28, 2026 UTC.
Reviewer: house.
Decision: **PASS at the exact source bytes and whole stated scope below.**
No source repair was required.

## 1. Exact object, scope and independence

The reviewed manuscript is:

- OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md
- SHA256: 121c24eea215f1d7de199467ba839aaeaa348007d4c4c57e54e21bca38c0b205.

I read the complete physical manuscript and all eight complete direct inputs listed in Section 9, checked their actual bytes against its pins, and independently checked the physical endpoint chart, whole-square routing, all mask endpoints, scalar application, capacity comparison, and literal D02 join. This review is separate from cycles' authorship and root's scalar authorship. I did not author the physical theorem or its scalar argument.

The scalar input already has my separate complete review:

- REVIEW_OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_HOUSE_2026_10_28.md
- SHA256: 2fc64678f3d583302a5582e0ae7c6857239f5cc14b3fa255625b2e11e7579839.

That review applies to the repaired scalar bytes 4d45da08... printed in the source, not the earlier 031c6459... draft. It explicitly records the two author-applied literal repairs. No such correction was needed in the present physical manuscript.

The conclusion is the capacity-one theorem for the actual closing exterior pocket of the complete stated single-hub/boundary-path component, under opposite tip-owned singleton endpoint contacts and the closed condition |A_H|>=5/4. The original six-body consequence excludes that entire endpoint/vertex feature of D02.L01345. It does not by itself exclude the complementary |A_H|<5/4 domain, other endpoint owners, the whole D02 row, or a coarse parent.

## 2. Complete actual-component and endpoint entry

The general single-hub source applies literally: the endpoint bodies have true positive degree two; H is unloaded; every actual internal spoke is retained; every path body remains physically circle-touching with its true degree. Its opposite-vertex chart uses the full H force and torque equations, including coincident internal applications. No internal loaded vertex is treated as a transmitter.

A singleton contact at a relative-interior point of a tip side and an H vertex has the original tip-owned normal. Its normal lies in the H vertex cone. The accepted complete port-order and endpoint-moment argument therefore gives exactly

    P_L=(-X,h), P_R=(Y,h),
    X,Y>0, X+Y=sqrt(2), h>0,
    n=(-b,a), 0<=a<=b, a^2+b^2=1,
    K=b*h-a*X>0.

The closed angle range used in the estimates is harmless. In fact a=b at the left endpoint would align the tip side with the adjacent H roof side; since P_L is in the relative interior of that tip side, it would produce a nontrivial shared segment. That endpoint is already inconsistent with the stipulated singleton contact. The proof does not need to use this additional strictness in its scalar bounds.

The actual B_2 is the boundary neighbor needed by the true-degree-two concurrence lemma. Thus q=P_L+ell*n with ell>=0 is a positive multiple of the full original circle resultant. This statement is valid for both physical circle masks and does not assert that a physical-two-circle concurrence belongs to V.

Writing the actual tip as

    V=P_L+[0,1]n+[-rho,1-rho]k, 0<rho<1,

is consequently exact. Its center has positive n-coordinate. Since q.k=-K<0, its physical farthest mask has nonpositive center k-coordinate and Z=K+rho>=1/2. The actual negative-k outer corner is physical and positively weighted, even when Z=1/2 and the other outer corner is also physical. Therefore

    R^2=(N+1)^2+Z^2, N=b*X+a*h>0

is valid throughout the original mask and individual-weight domain. In particular it is not a unique-corner formula incorrectly applied to a physical-two-circle tip.

The endpoint radius and whole-tip horizontal bounds follow directly. I checked the strict radical reserve 31/57600, the lower bound X,Y>3/8, and the inequalities putting the entire left and right tip strictly on opposite sides of x=x_0. These inequalities concern their actual whole squares, not their centers or the concurrence points.

## 3. Whole actual exterior-pocket routing above h

The polygonal chain in source (10) uses actual endpoint-side pieces and the actual two upper H sides. Its endpoint pieces meet H only at their stipulated singleton contacts. The two endpoint tips are closed-disjoint in the general path setting and, more directly here, lie strictly on opposite sides of x=x_0.

The accepted physical circle-corner order identifies its upper outer-circle arc as the original closing arc. The displayed gap-facing endpoint corners both have height strictly greater than h; the entire chosen occupied chain and that arc lie above h. Deforming the original physical crosscut inside H,V,T preserves winding about every compact subset of an extra's open interior. It does not change any force application.

Thus every whole extra assigned to this actual pocket lies in y>=h. Weak additional contacts may subdivide that region but cannot move an extra to its other side. If A_H lies on the outer circle, the same compact-interior argument works on the piecewise bounded regions separated by that occupied point. This is a geometric routing convention, not an altered packing.

The high-roof condition then forces h>1/2. I checked the exact displayed bound using |x_0|<41/40-sigma and sigma>70/99; its positive reserve is 227/52800. The full-Q cap theorem now supplies each whole extra a connected open inner-circle arc longer than pi/4, contained in its open interior. Hence two extras imply h<r/sqrt(2).

A useful direct endpoint check strengthens the topology at precisely this stage. After reflecting to X<=Y, one has 0<=x_0<=sigma. Under the two-extra reduction,

    |A_H|^2=x_0^2+(h+sigma)^2
       <1/2+(r/sqrt(2)+sigma)^2
        =97/32<4<=R^2.

Consequently A_H is strictly inside the outer circle throughout the nontrivial Section 5 argument. The outer-circle pinch mentioned in the standalone statement has already been excluded by the two-extra reduction. The clipped loop used below is therefore an ordinary simple loop; only the closed inner-circle threshold |A_H|=r remains as an endpoint to retain.

## 4. The support-cap split is a split of actual extra arcs

On y>h, the upper half of the actual H diamond is exactly the intersection of the two stated roof half-planes. Thus every inner-circle point of an extra's open interior satisfies at least one of the two strict opposite support inequalities.

The identity

    S_L^2+S_R^2=|A_H|^2>=r^2

makes those open inner-circle support caps disjoint, including equality where their closures meet only at the occupied H vertex. A connected extra arc cannot change cap through that point. If a support is at least r, its cap is empty, as stated.

The reflection X<=Y gives x_0>=0. The right support obeys

    Y+h=x_0+h+sigma>=|A_H|>=r,

so its complete cap has angular length at most pi/2. Thus at most one of the disjoint arcs longer than pi/4 can use the right cap.

I also checked explicitly that an actual left-cap point really belongs to the left clipped loop considered in Section 5. If an upper inner-circle point had x>=x_0>=0, then

    y-x=sqrt(r^2-x^2)-x
       <=sqrt(r^2-x_0^2)-x_0
       <=h+sigma-x_0=h+X.

The first inequality uses the decreasing function on x>=0, and the second is |A_H|>=r. Such a point cannot satisfy the strict left-cap inequality y-x>h+X. Every left-cap extra-arc point therefore has x<x_0. There is no unproved assignment from an abstract support label to the opposite geometric half of the pocket.

## 5. Full two-crossing audit of the smaller-port interval

The smaller port has |P_L|^2<41/32<r^2. Its straight roof segment reaches A_H on or beyond the inner circle and has exactly one inner-circle exit. In the support basis its fixed first coordinate is S, while the second increases to S_R>=sqrt(r^2-S^2). This proves the sign and branch of the exit angle

    theta_H=3*pi/4-arccos(S/r).

The endpoint chain P_L--A_L--Z_L is also exact. Along its first piece the positive n-coordinate stays N and the negative k-coordinate decreases from -K to -Z; along its second piece the negative k-coordinate stays -Z and the positive n-coordinate increases from N to N+1. Its norm strictly increases on both nondegenerate pieces. Starting inside r and ending on radius R>r, it has exactly one inner-circle crossing, including a crossing at A_L.

For that crossing I independently derived the full formula

    theta_V=pi-eta,
    eta=phi+min(arccos(N/r), arcsin(min(Z/r,1))).

When A_L is outside or on r, the normal-face limiter is the smaller one; when A_L is inside, the tangent-face limiter is the smaller one and Z<r. The two agree at the join. The truncation at Z=r and the physical mask Z=1/2 are both valid.

The left clipped loop consists of the actual H roof, this actual V chain, the outer-circle arc, and the vertical segment from A_H to the outer circle at x=x_0. The last two pieces do not enter the inner circle. The right tip contributes no piece or intersection in this loop. Section 3's strict outer-radius observation makes this a simple loop with precisely the two stated inner-circle exits.

The side of each exit is also correct, rather than a count of crossings without orientation. Starting at P_L, the increments in y-x along the V chain are

    rho*(b-a)>=0, followed by a+b>0,

whereas the H roof has y-x=h+X. With the stipulated singleton contact the initial nontrivial V piece is on the free side of that roof. Thus its crossing is on the left-support-cap side of the roof crossing. The upper inner-circle point at x=x_0 is at or below A_H and is outside the open pocket. Following increasing angle from that side gives exactly the interval between the roof exit and the gap-facing V exit. No other occupied boundary piece can introduce a further inner-circle interval.

It follows that every point of a left-assigned extra arc is in

    theta_H<theta<theta_V.

At |A_H|=r, the roof exit and vertical-segment endpoint coincide at that one occupied point. The open extra arc avoids it, and the same open interval follows directly or by the accepted compact-interior convention. No radial-visibility assumption about the entire pocket is made. No center-only sector estimate is being substituted for whole-square routing.

## 6. Complete scalar-to-physical join

Every point of the endpoint chain after P_L has height strictly greater than h. This includes the case a=0 because the first piece rises strictly and the second is then horizontal. The actual inner-circle crossing therefore has height r*sin(eta)>h.

If eta>=pi/2, the desired eta>w is immediate. In the remaining range, v<=h gives eta>w by ordinary sine monotonicity.

If v>h, all scalar premises are literal:

    0<X<=sigma, h>1/2, 0<=phi<=pi/4,
    S=sigma*(X+h), v=sqrt(r^2-S^2)>h.

The comparison point (-S,v) is used only to compare the actual two limiting-face coordinates. Since h>(sqrt(2)-1)*X, one has S>X and

    N_*=b*S+a*v>N=b*X+a*h.

If K_*=b*v-a*S<=0, the angle relation w<=phi and the positive actual limiter give eta>w. Otherwise K_*>0 is exactly the scalar theorem's remaining premise, so its full continuous conclusion yields

    (1+N)^2+K_*^2<4<=R^2=(1+N)^2+Z^2.

Hence K_*<Z. Setting u=w-phi gives u in (0,pi/2), r*cos(u)=N_*>N and r*sin(u)=K_*<Z. Both actual limiter angles are consequently strictly larger than u. This includes Z>=r, where the tangent limiter is pi/2. Therefore eta>w throughout.

The resulting routed interval length is

    theta_V-theta_H=pi/4+w-eta<pi/4.

It cannot hold even one of the actual extra arcs. The use of the auxiliary point does not assert that it belongs to V and does not change a physical mean, a circle weight, or a support owner.

## 7. Capacity, original D02 allocation, and limits

Every putative extra's connected open arc is assigned to one support cap. The left cap contains no such arc in the actual pocket, and the right cap contains at most one. This proves the whole closing-pocket capacity claim, including the closed exterior-vertex threshold and both endpoint physical circle masks.

For D02.L01345 the literal path is (1,0,5,4,3), H=2, with the original rim and chord 02. I checked the exact graph/load table: H has unloaded degree three; endpoints 1 and 3 have loaded degree two; 0 is loaded degree three; 5 and 4 are loaded degree two. All original degrees, forces and nine units remain.

The unchanged positive chord permits the complete central-capacity-one theorem. Each direct boundary-pair exterior pocket along the path is empty by the cited physical boundary-pair theorem. Every remaining exterior extra belongs to the one closing pocket just bounded. Thus at most two extras fit, contradicting the three actual extras of the original six-body row.

This is whole coverage of the stated high-roof opposite-tip-owned feature. It is not a whole-row or original-fine-ID closure by itself.

## 8. Verified complete direct-input pins

| Complete direct input | SHA256 |
| --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb |
| OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_BOUND.md | 4d45da08bee1d7c8de15a0eb9f8cb9d2f4dacb811f5e77e070037140882df535 |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

All direct sources were read completely. The review relies on their accepted mathematical conclusions at the exact scopes printed above, and independently checks the new physical joins. No sampled pose, finite parameter grid, computational pose certificate, normal reselection, changed original mean, deleted positive force, fake leaf, Lean compilation, CI, remote write, or ledger mutation was used.

