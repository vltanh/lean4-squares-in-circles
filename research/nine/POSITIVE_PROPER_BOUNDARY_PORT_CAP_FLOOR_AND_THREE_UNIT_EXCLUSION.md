# Positive proper boundary ports lift an actual closing pocket into a cap

Date: October 28, 2026 UTC. Author: house.

**Status: complete proposed hand lemma, frozen for full independent review.** The local statement retains the physical two-circle mask and its entire coefficient interval, including zero coefficients. Its radial proof does not put an exterior concurrence inside the unit. The geometric corollary concerns an actual occupied closing pocket with its protected lift, not a center-only region.

Put

    Q=1105/256,       2<=R<=sqrt(Q),
    d=sqrt(R^2-1/4)-1>0.

Every square below is one of the actual contained unit squares, with disjoint open interiors from every other square retained in the caller.

## 1. One actual contact supplies a physical circle corner beyond the same floor

Let V be physically boundary and let K be an actual contained unit touching it. Retain an original separating unit normal n directed from K into V and its actual application P. Thus P minimizes n on V and maximizes n on K. It may be a vertex, side-interior point, or an endpoint-valued original shared-side mean.

Fix a unit vector w and H>0 such that

    P.w>=H,       n.w>=0.                                  (1)

If V has a unique physical circle corner Z, assume the caller has proved its genuine proper ray and interior concurrence:

    q=P+ell n=lambda Z,       ell>=0,       0<lambda<=1.    (2)

If V has two physical circle corners, no assertion that its concurrence is inside V is required.

**Theorem A.** Under these hypotheses, some actual physical circle corner Z of V satisfies

    Z.w>=P.w>=H.                                           (3)

This selected geometric corner need not have positive individual coefficient. All actual coefficients remain unchanged.

### 1.1. The entire unique physical mask

Equation (2) gives

    Z.w=(P.w+ell n.w)/lambda>=P.w,

because P.w>0, ell>=0, n.w>=0 and lambda<=1. Equality in either proper distance is retained. If two original pair applications coincide, their genuine concurrence is that same point and (2) has exactly the same implication.

For a true loaded degree-two body, the complete nonparallel rectangle proof in TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md proves q in V in this unique mask. Its proof uses only the original two distinct applications, the unshareable circle point and the actual unit-neighbor width; its other-neighbor boundary premise is used to remove parallelism before that calculation. The root-neighbor export in7ecc supplies nonparallelism by its own unchanged physical geometry. Thus (2) is a precise available premise in both actual high-aligned endpoint callers; no broader properness is asserted here.

### 1.2. The entire physical two-circle mask, without a force simplification

Write the actual radial side frame as

    V=[d,d+1] e+[-1/2,1/2] f,       |e|=|f|=1, e.f=0.    (4)

Its two physical circle corners are exactly

    Z_+=(d+1)e+f/2,       Z_-=(d+1)e-f/2.

This is purely the geometry of two adjacent unit-square corners on the containing circle. Their midpoint has radial norm sqrt(R^2-1/4)=d+1, and the other square face lies one unit inward. Three or four physical circle corners are impossible at R>=2; opposite equal-radius corners would put the center at O and all four at radius1/sqrt(2).

Write

    n=alpha e+beta f,       P=s e+t f,
    d<=s<=d+1,       -1/2<=t<=1/2.                       (5)

We first prove alpha>=0. If alpha<0 and beta!=0, the minimum-n support of V is one of its physical outer circle corners, which cannot be shared by two contained interior-disjoint units. Indeed each contained square's right-angle inward tangent sector at a circle point is strictly within the circle's inward tangent half-plane; two such right-angle sectors cannot have disjoint interiors in that strict half-plane. If alpha<0 and beta=0, n=-e and the actual neighboring K lies wholly in e.x>=d+1. Its e-width is at least one, forcing a point with e-coordinate at least d+2>R. Both alternatives are impossible.

Suppose e.w<0. Since s>=d>0 and P.w>0, (5) forces

    t(f.w)>0.                                            (6)

If beta!=0, the minimum-support condition gives t=-sign(beta)/2, including alpha=0 and every original point on that same tangential side. Therefore beta(f.w)<0. With alpha>=0 and e.w<0 this gives

    n.w=alpha(e.w)+beta(f.w)<0,

contrary to (1).

If beta=0, then alpha>0 because n is a unit vector, and n.w=alpha(e.w)<0 directly. These cases exhaust (5), including the inner-side mean, both inner vertices, every radial/tangential axis endpoint, and every side-interior application. Consequently

    e.w>=0.

The larger w projection of the two physical circle corners is now

    max(Z_+.w,Z_-.w)=(d+1)(e.w)+|f.w|/2
                     >=s(e.w)+t(f.w)=P.w.

This proves (3). It uses neither a chosen nonzero circle atom nor a bound on an exterior radial concurrence. The full physical mask is retained.

## 2. A complete actual closing-pocket cap lift

Retain one actual physically circle-clear hub K and two distinct physically boundary endpoint units V,W. They are closed-disjoint. Retain their original contact means P_V,P_W and original normals n_V,n_W directed out of K. Suppose the caller has supplied the following actual local data:

1. The original two endpoint ray calculations have positive scalar multiples of their complete circle resultants F_V,F_W. In the unique physical mask they satisfy (2); in the physical two-circle mask their proper lengths are nonnegative but their concurrence may be exterior.
2. The actual outer K boundary arc between the two endpoint applications has w.x>=H for one unit w and H>0, and both original normals satisfy n_j.w>=0.
3. The occupied embedding gives the actual exterior closing lift between these two endpoints, with their protected physical corner intervals in its original circular order. Across this particular closing side, the full resultant-direction gap is strictly less than pi. This is a premise about that actual lift, not an assertion inferred merely from the endpoint centers.
4. For the region being counted, geometric physical spokes are chosen once before any pocket allocation. A caller that counts neighboring regions must use these same corners and spokes for both adjacent regions.

**Theorem B.** There is such a compatible initial choice of the physical endpoint corners for which the whole actual closing pocket is contained in

    {x:w.x>=H}.                                           (7)

Every whole extra assigned to that pocket satisfies (7).

Here is the complete geometric join. Theorem A selects physical circle corners z_V,z_W with w.z_j>=H at the unchanged original means. For geometry only, take the gap-facing extreme a_j of each actual K--endpoint intersection. These points lie on a subarc of the stipulated outer K arc, so w.a_j>=H. Do not substitute them for P_j in any force or torque equation.

The straight segment a_j--z_j in its actual convex endpoint unit lies in (7). If a segment has a boundary degeneracy, fix any eta>0 and take a compatible arbitrarily close interior route in w.x>=H-eta instead. The routes meet K only at their own gap-facing contact extremes. The endpoint units are closed-disjoint and the hub is physically clear, so these two paths and the actual outer K subarc form an occupied simple crosscut with the same two distinct containing-circle endpoints. This perturbation does not move either endpoint along the circle.

The full proper rays give

    w.q_j=w.P_j+ell_j(w.n_j)>=H>0,

so both original full resultants also have positive w projection. Both selected physical corners have positive w projection by (3). The protected physical intervals order all these directions consistently; the selected corners and the resultants lie in the same open w-positive semicircle. Since the particular resultant closing gap is less than pi, its actual closing lift is the corresponding arc in that semicircle, not the complementary one. The selected physical-corner closing arc has the same order and is also in that semicircle. Its endpoints satisfy w.z_j>=H, so the whole minor circular arc satisfies that same inequality: in coordinates w=North, its angles belong to [asin(H/R),pi-asin(H/R)].

The occupied crosscut and this actual circular arc therefore form a Jordan boundary entirely in w.x>=H-eta; in the nondegenerate closed-segment case eta can be zero. Its bounded side is also in that convex half-plane. This is the asserted actual closing side, including its weak physical subdivisions. Additional contacts only subdivide it; an extra's connected open interior cannot pass through the closed occupied crosscut.

At a degenerate endpoint or shared contact, fix a compact subset of an alleged extra's open interior first and use compatible interior paths in the original units, with the already fixed circle endpoints. Its separation from the occupied union keeps the winding and side assignment fixed. The construction is available for every eta>0; let eta decrease to zero and then pass to the extra's closure. This proves the exact weak bound (7) for the whole extra. No force point or circle coefficient changes in this geometric construction.

The spokes in this proof are fixed before the counted regions are defined. No claim is made that moving a previously labeled endpoint along the outer circle preserves every extra's winding number.

## 3. The sharp cap threshold immediately gives capacity at most two

If the actual floor in Theorem B satisfies

    H>7/16,                                               (8)

the pocket contains at most two pairwise interior-disjoint whole unit squares.

Indeed rotate w to North and enlarge the disk to D_(sqrt(Q)). The complete three-square cap theorem UNRESTRICTED_THREE_SQUARE_CAP.md applies to every unit in (7). Three such units would all be axis-parallel in that frame, and the two extreme ones would have centers

    (-1,15/16),       (1,15/16).

Their lower heights would be exactly7/16, contradicting (8). This uses the full equality classification at Q, so the closed upper radius endpoint is retained. A merely weak floor H=7/16 would not justify this conclusion.

For clarity, the imported cap theorem is the all-orientation clipped-section theorem: every unit in y>=7/16 cuts length at least one from [-3/2,3/2] at height5/4; a rotated unit cuts strictly more. Three disjoint open sections therefore force all three frames aligned and all three unit intervals to tile that segment. The extreme farthest-corner inequalities then force their lower height7/16. Its full four-edge, two-tilt proof is the operative source, not a finite regression.

## 4. Every balanced aligned-root boundary corner has positive global x

The following observation makes Theorem B compatible with the fixed-first leaf-pocket allocation.

Use the actual high aligned root and real S leaf,

    sqrt(17)/2<=R<=sqrt(Q),
    epsilon=d-1 in[0,1/60),
    A=[epsilon,d] times [-b,a],       a+b=1,
    353/1000<=a,b<=647/1000.

Let T be an upper true loaded degree-two root neighbor in the complete7ecc scope. Its original root normal is North or strict Northeast; its original root application has height a. The genuine root ray gives

    (F_T)_x>0,       (F_T)_y>0.                           (9)

**Theorem C.** Every physical containing-circle corner of T has positive global x coordinate. The same statement holds for the lower neighbor B by simultaneous reflection.

For the unique physical mask, (9) proves the statement immediately.

For the physical two-circle mask, retain (4). If its two circle corners were not both strictly positive in global x, (9) ensures that one is strictly positive and the other is nonpositive. Consequently

    |(d+1)e_x|<=|f_x|/2<=1/2,
    |e_x|<=1/4,       |e_y|>=sqrt(15)/4.                 (10)

Here d>=1. Their global y coordinates have the sign of e_y: the radial contribution has magnitude at least2 sqrt(15)/4 while the tangent contribution has magnitude at most1/8. Equation (9) therefore gives e_y>0.

Every point of T has global y coordinate at least

    d e_y-|f_y|/2
      >=sqrt(15)/4-1/8
      >3/4>647/1000.                                    (11)

The strict elementary comparison uses sqrt(15)>7/2, with squared reserve15-49/4=11/4. But T contains its original A application at height a<=647/1000. This contradicts (11), proving Theorem C for the entire physical two-circle mask.

Thus any physical T corner selected by the cap-floor proof is also a permitted positive-x corner in BALANCED_ALIGNED_S_ROOT_FIXED_INNER_POINT_AND_EMPTY_LEAF_POCKETS.md. Choose that corner, the cap-selected C corner, and one physical B corner once, before all original regions are defined. The full leaf-pocket allocation then applies with these identical initial spokes. It need not transport any previously labeled region between different corner choices.

## 5. Exact scope and operative complete sources

Theorems A and B are local all-mask implications. A caller still has to prove its entire outer-arc floor, the original normal signs, the genuine unique-mask interior concurrence, the protected closing lift, and the actual region allocation. They do not supply these data from a picture, a center bound, or a false degree-two replacement.

Theorem C is the entire high balanced-root corner sign needed by the stated original house allocation. It does not extend a high-radius slider bound to lower radii.

| Complete source | SHA256 | Exact use |
| --- | --- | --- |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Full unique-mask interior/proper concurrence and the precise exterior radial alternative; the local theorem above keeps the required caller premise explicit. |
| ALIGNED_GENUINE_S_ROOT_BOUNDARY_RAYS_AND_TRIANGLE_PAGE_CLOSING_POCKET.md | 7eccbcc7814e2e6ab0129d1cd24016687edf59cb6b4299385d683c3a77597a4f | Actual high-aligned T root rays, full mask scope, protected leaf-inclusive lift and original endpoint data. |
| GENERAL_BOUNDARY_CHORD_OUTER_CYCLE_ORDER_EXCLUSION.md | 13abf52906294b994c078598985d656b65d4267faa67a6b7b17ee8bc25c11273 | Ordered disjoint physical circle-corner/resultant intervals and compatible protected physical spokes. |
| UNRESTRICTED_THREE_SQUARE_CAP.md | b1359fcb446d93a534dc19dc7582edc5e8067300109810369621e47989ecf77b | Entire all-orientation clipped-section proof and exact three-square cap equality at Q; no numerical regression is a premise. |
| BALANCED_ALIGNED_S_ROOT_FIXED_INNER_POINT_AND_EMPTY_LEAF_POCKETS.md | b1a15d99b0374bdf74c717bdfe781fb1e93c83c0c28b46b53cd485ae9b280e1e | Only the exact fixed-first high-aligned original allocation, whose positive-x endpoint-corner choices are supplied by Section4. |

House authored7ecc and b1a15d. Their complete separate root reviews a649c569dd0e9103b6136b0c36c34050941ca83bea851ef84733a2e548dc0e73 and2e30d8cbd6992c6875ea83a0a5fb23e9c1435f0b2bd204605e0da841a4eab3e9 remain the independent component boundary. They do not constitute an independent review of the new all-mask floor lift or Theorem C.

No original graph/load flag is changed by this local theorem. Every original unit, degree, physical mask, zero coefficient, normal and mean remains. No sampled pose, numerical packing certificate, Lean compilation, CI, merge, repository metadata change or remote action is used.

