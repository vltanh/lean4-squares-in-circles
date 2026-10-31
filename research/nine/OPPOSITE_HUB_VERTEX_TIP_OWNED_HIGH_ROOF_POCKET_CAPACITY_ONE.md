# Opposite tip-owned hub vertices have pocket capacity one when the exterior vertex reaches the inner circle

Date: October 28, 2026 UTC. Physical proof author: cycles. The continuous scalar input is root's separately authored proof, with the fixed-sum reduction contributed by cycles.

**Status: complete proposed hand theorem, submitted for full independent review.** The conclusion covers the entire stated exterior-vertex domain, every endpoint physical circle mask, every internal spoke and original side mean, and every additional physical unit. It is one part of the opposite-vertex endpoint problem; it does not claim the complementary lower-vertex domain or the whole D02 load row.

Put

    Q=1105/256, r=5/4, sigma=1/sqrt(2).

## 1. Exact unchanged physical scope

Work in 2<=R<=sqrt(Q), with an original selected positive component of the following form:

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

The actual H is unloaded. Every B_i has positive total circle load. The actual exterior-face order is H,B_1,...,B_k,H. In particular the two endpoints V=B_1 and T=B_k have their true positive degree two. Every internal B_i retains its actual degree and all its original equations.

Assume the two actual intersections H cap V and H cap T are singleton points, each in the relative interior of a side of its respective endpoint tip. Their actual applications are opposite vertices of H. Thus both endpoint contact normals are owned by the endpoint tips. No ownership premise is imposed on any other edge.

Let A_H be the actual vertex of H between these ports on the exterior H arc, namely the arc with no internal positive spoke. Assume

    |A_H|>=r.                                           (1)

**Theorem.** The whole actual closing exterior pocket through H has capacity at most one additional unit square.

The theorem retains the entire original packing, all selected positive magnitudes, all physical circle corners and individual zero corner coefficients, every internal shared-side mean including its endpoint values, and all zero-weight contacts. It neither deletes an internal hub force nor uses a two-force equation at an internal loaded body.

## 2. The complete actual chart and its all-mask endpoint data

Apply the opposite-vertex case, Section 6 of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, to the unchanged component. Rotate and reflect the whole configuration once so that the occupied H arc is the lower arc. The original ports, center and exterior vertex are

    P_L=(-X,h), P_R=(Y,h),
    X>0, Y>0, X+Y=sqrt(2), h>0,
    c_H=(x_0,h), x_0=sigma-X=Y-sigma,
    A_H=(x_0,h+sigma).                                 (2)

The left endpoint's unchanged normal directed H to V has the form

    n=(-b,a), k=Jn=(-a,-b),
    a=sin(phi), b=cos(phi), 0<=phi<=pi/4.                (3)

The right endpoint has the reflected form. These angle signs come from the complete original H force and torque equations and physical port order, including all coincident internal applications. They are not a transmitter assumption. The same accepted source gives the strict left endpoint moment

    K:=b*h-a*X>0.                                       (4)

The all-mask true-degree-two proper-concurrence lemma gives

    q=P_L+ell*n, ell>=0,

where q is a positive multiple of V's complete circle resultant. Its physical boundary neighbor is the actual B_2. No assertion that q belongs to V is needed.

Because this contact is a singleton owned by the tip's side, the entire actual V is

    V=P_L+[0,1]n+[-rho,1-rho]k, 0<rho<1.                (5)

Write

    N=P_L.n=b*X+a*h>0,
    Z=K+rho.

The center's n-coordinate is N+1/2>0, so all physical farthest corners lie on the outer n-face. The full circle resultant has negative k-component because q.k=-K<0. Therefore the center's k-coordinate is nonpositive, and

    Z>=1/2,
    R^2=(N+1)^2+Z^2.                                  (6)

If Z>1/2, the negative-k outer corner is unique. If Z=1/2, both outer corners are physical circle corners; the negative-k one has positive weight, while the other original weight may be zero or positive. Formula (6) covers both complete masks. Its gap-facing physical circle corner is

    Z_L=(N+1)n-Zk=P_L+n-rho*k,
    (Z_L)_y=h+a+rho*b>h,
    (Z_L)_x=-X-b+rho*a<0.                              (7)

Thus no unique-corner concurrence was used at a physical two-corner endpoint.

Also X=N*b-K*a<=N. Equation (6) consequently gives

    X<=N<=sqrt(R^2-1/4)-1<61/60<41/40.                 (8)

The same holds with Y at the right endpoint. The strict radical comparison is

    (121/60)^2-1041/256=31/57600>0.

In particular both X and Y exceed 3/8, since their sum is sqrt(2)>7/5 and the other is below 41/40.

The actual left tip lies entirely to the left of x=x_0. Indeed its maximum horizontal coordinate in (5) is

    -X+rho*a<-X+sigma=x_0.                             (9)

The right tip lies entirely to the right of this line by reflection, because its minimum coordinate is Y-rho_R*a_R>Y-sigma=x_0. These are statements about the whole actual squares, not only their centers or concurrence points.

## 3. The actual pocket lies above h, and two extras force h<r/sqrt(2)

The occupied boundary chain from the left circle corner to the right circle corner can be drawn as

    Z_L -- (P_L-rho*k) -- P_L -- A_H -- P_R
         -- (right inner top corner) -- Z_R.           (10)

Its endpoint pieces lie in the actual endpoint tips. Its middle pieces are the actual exterior H sides. The two endpoint contacts are singletons, so these pieces have no unintended intersection with H. Equation (9) separates the two endpoint pieces.

The actual circle-corner and boundary-path order identifies the upper outer-circle arc from Z_R to Z_L as the closing arc. This is also the occupied-pocket argument in Sections 1, 2 and 6 of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md: the endpoint resultants have positive y-coordinate, their actual closing resultant gap is less than pi by full component balance, and the gap-facing physical circle corners retain the same interval order.

Deforming the original center/contact exterior crosscut to (10) takes place only in the actual H,V,T union. It therefore preserves winding about every point of the open interior of an additional square. The remaining original bodies and their contacts can subdivide the bounded region or remove free space; they cannot move an extra through this occupied barrier.

Every point of (10), and of its upper closing circle arc, has y>=h. Hence the actual exterior pocket and every whole unit assigned to it are in

    {y>=h}.                                            (11)

At a weak junction, or if A_H itself is on the outer circle, use a compact inner part of each additional unit first. The accepted compact-interior routing convention preserves its side and winding under arbitrarily small routings inside the same occupied units. Closure recovers (11) for the whole unit. No physical mean is changed in any equation.

Condition (1) implies

    h>1/2.                                             (12)

For if h<=1/2, (2), (8) would give

    |A_H|^2
      <(41/40-sigma)^2+(1/2+sigma)^2
       =1681/1600+5/4-(21/20)*sigma
       <25/16.

For the last strict comparison use sigma>70/99; its exact reserve is 227/52800.

By (11), (12), the force-free whole-orientation cap theorem, Section 1 of GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, supplies every additional square in this pocket one connected open arc on |p|=r, contained in its open interior and of angular length strictly greater than pi/4. Distinct squares have disjoint such arcs.

Suppose for contradiction there are at least two such squares. Their arcs are above y=h. The full available upper-circle cap there has length 2 arccos(h/r). Thus they already give a contradiction if h>=r/sqrt(2). Hence the only remaining possibility has

    1/2<h<r/sqrt(2).                                   (13)

All subsequent arguments assume (13) only after this complete two-extra reduction.

## 4. The hub separates the inner-circle arcs into two roof-side intervals

Reflect the entire chart if necessary so that X<=Y. Thus

    0<X<=sigma<=Y, x_0>=0.

On the upper half-plane y>h, the whole actual H is exactly the region below both of its roof support lines,

    y-x<=h+X,  y+x<=h+Y.

Define their positive unit-normal supports

    S_L=(X+h)/sqrt(2), S_R=(Y+h)/sqrt(2).                (14)

Every inner-circle point in an extra's open interior avoids the closed H. It therefore satisfies at least one of

    y-x>h+X,  y+x>h+Y.                                 (15)

The squared supports satisfy the exact identity

    S_L^2+S_R^2=|A_H|^2>=r^2.                          (16)

If S_j>=r, the corresponding strict cap in (15) is empty. Otherwise write w_j=arccos(S_j/r), so 0<w_j<pi/2. The left support cap is centered at angle 3pi/4 and the right support cap at pi/4. Equation (16) implies

    w_L+w_R<=pi/2                                      (17)

whenever both caps are nonempty: cos(w_L)>=sin(w_R), with both angles in (0,pi/2), is equivalent to the squared comparison in (16).

Thus the two open support caps are disjoint; at equality their closures meet only at A_H on the inner circle. An extra's connected open arc, which avoids the whole closed H, lies entirely in one of the two caps. A weak contact at A_H cannot join those two open arcs through the occupied point.

The right cap has total angular length at most pi/2. Indeed

    Y+h=x_0+(h+sigma)>=sqrt(x_0^2+(h+sigma)^2)
                         =|A_H|>=r,

because both summands are nonnegative. Consequently S_R>=r/sqrt(2), giving w_R<=pi/4 when that cap is nonempty. At most one arc longer than pi/4 can lie in the right cap.

It remains to show that the actual left part of the exterior pocket offers less than pi/4 of inner-circle arc.

## 5. Full routing of the smaller-port part of the pocket

The smaller port is strictly inside the inner circle. From X<=sigma and (13),

    |P_L|^2=X^2+h^2<1/2+r^2/2=41/32<25/16=r^2.       (18)

Its left support S=S_L satisfies

    0<S<(1+r)/2=9/8<r.

Put

    w=arccos(S/r), v=sqrt(r^2-S^2)>0.

The actual left roof segment P_L--A_H exits the inner circle exactly once, possibly at its endpoint A_H. Its exit angle is

    theta_H=3pi/4-w.                                  (19)

To verify which intersection is the exit, use the orthonormal directions (-sigma,sigma) and (sigma,sigma). The support coordinate is S; the second coordinate increases along the roof segment. At A_H it is S_R, and (16) says S_R>=sqrt(r^2-S^2). Thus the first exit is the intersection with positive second coordinate, giving (19).

The gap-facing endpoint chain of V is

    P_L -- A_L:=P_L-rho*k -- Z_L=A_L+n.                (20)

In its own coordinates the first segment has n-coordinate N>0 and k-coordinate decreasing from -K to -Z; the second has k-coordinate -Z and n-coordinate increasing from N to N+1. Its norm increases strictly along both nondegenerate segments. By (18), it crosses the inner circle exactly once.

Write the angle of this crossing as theta_V=pi-eta. Directly from (20),

    eta=phi+min{ arccos(N/r),
                 arcsin(min(Z/r,1)) }.                 (21)

Here N<r by (18). If A_L is outside or on the inner circle, the first segment supplies the normal-face limiter arccos(N/r). If A_L is inside, the second segment supplies the tangent-face limiter arcsin(Z/r), with Z<r. The two expressions coincide at the face join. This is an actual full-mask corner calculation, including Z=1/2.

For precision, the pocket's left inner-circle interval lies between the two exits (19), (21), rather than on the other side of either obstacle. Clip the occupied upper loop (10) by x=x_0. Its clipping segment runs from A_H to the upper outer-circle point with first coordinate x_0; it has norm at least r by (1). The outer-circle piece also has norm R>r. The right endpoint unit is wholly in x>x_0 by (9), so it introduces no extra intersection in this left clipped loop.

In the left clipped loop, the only inner-circle crossings of the occupied boundary are the two just identified: the straight H roof segment and the norm-increasing chain (20). The inner-circle point on x=x_0 is at or below A_H, hence outside the open pocket. Following the upper inner circle toward increasing angle first crosses the H roof at theta_H; it can leave the bounded side again only at the endpoint chain. Avoiding the entire closed V removes its connected occupied interval on that side. Equivalently, the gap-facing boundary (20) itself is the last boundary of V reached from the free pocket.

Consequently every inner-circle point in the open interior of any actual pocket extra assigned to the left support cap belongs to

    theta_H<theta<theta_V.                            (22)

If theta_V<=theta_H, the interval is empty. This is a winding argument with the actual occupied crosscut; it assumes neither radial visibility of the whole pocket nor a sector condition on an extra's center. At |A_H|=r the clipping and roof crossing meet at that single occupied point. An extra's open interior avoids it, and the same open-interval conclusion holds by the compact-interior convention.

## 6. The smaller-port comparison shortens (22) to less than pi/4

We prove

    eta>w.                                             (23)

The actual crossing point in (20) has height strictly greater than h: the first segment rises by rho*b>0 overall, and the second rises weakly; any crossing of the inner circle comes after P_L by (18). If eta>=pi/2, (23) is immediate because w<pi/2. We can therefore use the increasing sine on 0<eta<pi/2 whenever comparing crossing heights.

First suppose v<=h. The crossing height exceeds h>=v=r*sin(w), so eta>w.

Now suppose v>h. Set the auxiliary comparison point

    z_*=(-S,v),

which lies on the inner circle. It has angle pi-w. Since h>1/2 and X<=sigma,

    h>(sqrt(2)-1)*X,

so S>X. Hence its n-projection is strictly greater than that of the actual port:

    N_*:=b*S+a*v>b*X+a*h=N.                            (24)

Put K_*=b*v-a*S. If K_*<=0, then w<=phi and (21) gives eta>phi>=w.

If K_*>0, all hypotheses of OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_BOUND.md hold for the actual X,h,phi,S,v. Its complete continuous inequality gives

    (1+N)^2+K_*^2<4<=R^2=(1+N)^2+Z^2.

Thus K_*<Z. Also w>phi, and the relative angle u=w-phi lies in (0,pi/2). Equation (24) and the definition of K_* read

    r*cos(u)=N_*>N,  r*sin(u)=K_*<Z.

Therefore u is strictly smaller than arccos(N/r) and strictly smaller than arcsin(min(Z/r,1)). The latter statement is immediate if Z>=r and is ordinary sine monotonicity if Z<r. Formula (21) now yields eta>phi+u=w, proving (23).

This reasoning compares the two upper limiting faces of the actual endpoint. It does not need, or assert, that z_* lies inside every other face of the square. In particular it makes no hidden substitution of an auxiliary point for an actual contact mean.

Combining (19), (21), (23),

    theta_V-theta_H
      =pi/4+w-eta<pi/4.                                (25)

The complete routed interval (22) is therefore too short for even one additional square's arc longer than pi/4.

## 7. Capacity and the closed exterior-vertex endpoint

Every putative additional square supplies one connected arc longer than pi/4. Section 4 assigns it to the left or right support cap. Sections 5 and 6 exclude the left assignment. The right cap has length at most pi/2, so it contains at most one such arc.

This contradicts the assumption of two additional squares and proves pocket capacity at most one. All comparisons remain strict where needed at the closed threshold |A_H|=r. Both original physical endpoint circle masks and every individual zero circle coefficient were retained in (6), and all other original equations remain untouched.

## 8. Literal D02.L01345 consequence and exact remaining scope

In the original row M6.B6.HEXAGON.D02.L01345, keep the rim

    01,12,23,34,45,50

and its original positive chord 02. Put

    H=2, V=1, T=3,
    (B_1,...,B_5)=(1,0,5,4,3).

The actual H is unloaded true degree three, with neighbors 1,0,3. The endpoint V=1 is loaded true degree two, T=3 is loaded true degree two, B_2=0 is loaded true degree three, and 5,4 are loaded true degree two. No extra spoke or force is introduced.

If the original 12 and 23 contacts are tip-owned singleton side-interior contacts at opposite vertices of 2, and the exterior intermediate vertex of 2 has norm at least 5/4, every hypothesis above is literal. The whole central free union has capacity at most one by CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md. Every direct boundary-pair exterior pocket along 1--0--5--4--3 is empty by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md. Thus all other extras are in the single closing pocket treated here, whose capacity is at most one.

At most two additional units can then be placed, whereas the original six-body row retains three additional physical units. This excludes this entire physical endpoint/vertex domain of the original row.

The opposite-tip case with |A_H|<5/4 remains a separate obligation. Hub-owned endpoint axes, genuinely free endpoint normals, and other endpoint-type combinations are not silently included. The theorem gives no new fine ID and no whole D02-row or coarse-family credit by itself.

## 9. Exact operative sources and proof limits

| Source | SHA256 | Exact use |
| --- | --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Whole original path/hub setting, complete opposite-vertex force/torque order, endpoint moments, physical closing-pocket routing |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Local Lemma 2.1 only: true endpoint degree-two proper concurrence with an actual physical boundary neighbor, including both physical circle masks |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Force-free Section 1 for every whole additional square in the actual cap y>=h>1/2 |
| OPPOSITE_HUB_SMALLER_PORT_ROOF_SCALAR_BOUND.md | 4d45da08bee1d7c8de15a0eb9f8cb9d2f4dacb811f5e77e070037140882df535 | Complete continuous smaller-port inequality, only at the literal scalar scope used in Section 6 |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole central capacity for the literal D02 original join |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Empty actual direct boundary-pair exterior pockets |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original graph, load mask and unchanged degree table |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Supplies R>2 for the literal full nine-square caller |

Every geometric assertion needed beyond these exact inputs is printed above. The scalar source requires its own independent review; cycles' checks of that source include an explicit contribution disclosure for the fixed-sum reduction. No numerical pose, finite parameter mesh, coordinate-search certificate, normal reselection, altered force, changed original mean, Lean compilation, CI, remote write or ledger mutation is used.

