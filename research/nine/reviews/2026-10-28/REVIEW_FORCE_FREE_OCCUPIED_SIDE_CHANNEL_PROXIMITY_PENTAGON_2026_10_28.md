# Independent review: an occupied arbitrary-degree side channel has one-eighth proximity

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

**Verdict: full independent PASS, without repair.** The whole actual transmitter has distance strictly less than 1/8 from the original circle origin whenever the stated upper channel pocket is occupied. The proof retains arbitrary endpoint degrees, all physical circle masks and the full original application means.

## 1. Exact target and full input reads

Reviewed target:

    FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_EIGHTH_PROXIMITY.md

SHA256:

    633b6b4a790187ba46d9b89001a3abf816ddb78e91fbed432ea81283c208620e

The current target has 12,636 bytes. I read the entire current source and all three complete direct inputs:

| Complete source | SHA256 |
| --- | --- |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 418229089de594515bbb60da5bdcdb4cd044bd4e9396aacfa47d27de96194055 |
| NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md | 4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366 |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 |

All current pins match. I additionally read the complete operative predecessor used by the 4930 source's inner-face case:

    NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md
    SHA256 4da80eec56859a863f042257d8ae391c17409e2b0e82dbee2e6b7173838fa54b.

The new one-sided concavity estimate, the actual new-radius routing and the whole closed-arc/slab contradiction are cycles-authored. I independently derived them and did not contribute their discovery.

I authored the older d575 centered-arc input. Its independent acceptance is retained rather than supplied by this review. I read the complete separate review

    REVIEW_CENTERED_FORTY_DEGREE_THREE_QUARTERS_FRONTIER_2026_10_28.md
    SHA256 37ed46006f52797428d34ba20c7f8e58d1790f916fbf61a447321de3f1b808d9,

which covers the full d575 theorem, closed endpoints and exact coefficient identity. The new target uses precisely its accepted all-contained-unit centered-arc statement.

The current 418229 capacity source has my separate full review

    REVIEW_FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CAPACITY_PENTAGON_2026_10_28.md
    SHA256 b03120174dad7f893b711c4e127fc9cb38614eff6bb931814ff93d0735101a34.

That review retains the sole caller clarification that the original exterior-spoke corners are fixed. The present target uses those exact clarified bytes.

## 2. The physical entry preserves the actual transmitter and pocket

The target keeps

    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h), P_Y=(b,h), v<=h<=v+1,
    X subset {x<=-a}, Y subset {x>=b},

with X and Y physically boundary and every original support application unchanged.

The force-free entry gives a,b>7/100, hence both are less than one, together with h>3/10 and strictly positive endpoint-center heights. The local pocket is the bounded side of the actual occupied crosscut and its upper outer-circle arc. In a positive-channel caller, its chosen physical circle corners are the unchanged original exterior-spoke corners.

The complete capacity proof gives dist(O,E)>3/10 for every whole actual extra E in that pocket. This remains valid when an endpoint's chosen opposite circle corner lies below h. The target correctly makes no whole-extra y>=h assertion.

## 3. Every circle-intersection and centered-arc premise is satisfied

Each boundary center has radius at least R-1/sqrt(2), hence at least m=2-1/sqrt(2). Every actual point of a physical boundary unit has norm at least R-sqrt(2)>1/8, by the unit diameter.

The 4930 theorem therefore applies to both endpoint units with its required strict clearance. Its complete own-frame formulas give one connected closed radius-9/8 intersection, the corresponding nonempty open arc, and the actual radial-center point in that open arc. The strict threshold is respected: the known disconnected equality example at clearance exactly 1/8 is never used as an endpoint input.

I checked the full predecessor scope used in the inner-face part. Its stronger global clearance assumption is needed only to enter a>rho. The remainder of its own-frame proof uses exactly the inequalities reproduced in 4930. The latter's separate outer-face proof handles the missing a<=rho domain. Thus no connectedness statement is imported outside its proved range.

Both boundary center radii exceed 3/4, so d575 gives their entire closed centered arcs of halfwidth 20 degrees inside their open interiors.

For E, its actual incircle lies in E, and dist(O,E)>3/10 implies

    |c_E|>=dist(O,E)+1/2>4/5>3/4.

Hence E has the same entire closed centered 40-degree arc. This conclusion does not presume that the whole circle intersection of E is connected; only the specified centered arc is needed.

All arcs used in the contradiction are on the same radius rho=9/8.

## 4. The one-sided endpoint comparison is uniform and strict

At the left endpoint write

    -(c_X)_x=a+H_X,
    0<H_X<=sigma=1/sqrt(2),
    theta_X in (pi/2,pi),
    delta=pi-theta_X,
    beta_a=acos(-a/rho)=pi/2+asin(a/rho).

The physical boundary-center lower bound gives

    cos(delta)<=(a+sigma)/m.

The desired estimate theta_X-beta_a<pi/3 is exactly

    delta+asin(a/rho)>pi/6.

For a>=rho/2, the arcsine term is at least pi/6 and delta>0 supplies strictness.

For the enlarged full interval 0<=a<=rho/2, the target's function

    F(a)=(sqrt(3)/2)sqrt(1-a^2/rho^2)
           +a/(2rho)-(a+sigma)/m

is concave. Its only nonaffine term is the concave square root on an interval strictly inside its singular endpoint. Thus a positive lower bound at both endpoints controls the entire closed interval.

At zero, sigma/m<3/5 and sqrt(3)/2>3/4 give F(0)>3/20. At rho/2, the first two terms sum exactly to one. The remaining inequality is

    rho/2+2sigma=9/16+sqrt(2)<2,

with the exact squared reserve 17/256 for sqrt(2)<23/16. Both endpoints are strictly positive.

The first two terms of F are cos(pi/6-asin(a/rho)). The compared angle lies in [0,pi/6], while delta lies in (0,pi/2). Strict cosine monotonicity therefore proves the claimed inequality on the entire domain, including a=rho/2. There is no physical orientation or mean selected in this scalar comparison.

The endpoint of X's closed centered half-arc at theta_X-pi/9 lies in open X. Its gap-facing closed-intersection endpoint alpha_X must therefore satisfy the strict inequality

    alpha_X<theta_X-pi/9.

Combining the two estimates gives

    alpha_X-beta_a<2pi/9.

The interval may be empty, which only strengthens the conclusion. Reflection proves the identical right-side comparison. No endpoint force, concurrence, owner, physical corner weight or transverse mean enters this argument.

## 5. The new-radius routing is an actual winding proof

The source explicitly redoes the routing at rho=9/8; it does not transfer a radius-5/4 interval claim by analogy.

The endpoint closed arcs lie respectively in the left and right open semicircles and contain their strictly upper center directions. A free lower-left circle point can continue toward (0,-rho) without encountering another piece of X's connected arc. Its negative x-coordinate avoids Y, and its nonpositive height avoids the middle crosscut segment. The endpoint strands are contained in the endpoint units. The downward ray then exits through the lower outer-circle point, which is not on the chosen closing arc. Reflection covers the lower-right quadrant.

For an upper free point beyond theta_X, the increasing-angle path toward pi stays strictly left of x=-a: the radial-center point already lies in open X, and cosine decreases along the upper semicircle. This avoids the middle segment. Connectedness of the closed endpoint arc prevents a later X encounter after the starting point has passed outside it. The path then uses the lower escape already established. Reflection treats angles before theta_Y.

Consequently every rho-circle point in open E lies on the upper lift and strictly between the gap-facing endpoints:

    alpha_Y<arg(z)<alpha_X.

These paths test winding relative to the defining loop. They are not proposed motions of physical squares, so no unproved free corridor among the other packing units is required.

## 6. The slab contradiction covers the closed one-eighth threshold

Suppose dist(O,H)>=1/8. Since a,b>0, the horizontal interval of H contains zero. Its vertical interval contains h>0. If v<=0, that interval would also contain zero, so O would belong to H. Thus the alleged positive distance forces

    v=dist(O,H)>=1/8,
    v+1>=9/8=rho.

On each vertical line with -a<=x<=b, the endpoint strands lie on the two exterior sides of the slab. The actual middle crosscut is at height h, and the selected upper circle arc is above it. Therefore a point of the bounded pocket in this slab is above the middle segment; a point in open E is strictly above it because it avoids the closed occupied crosscut.

Any such point on the rho-circle would satisfy

    -a<=x<=b,
    v<=h<y<=rho<=v+1.

It would belong to the closed actual H. An open interior point of a different interior-disjoint unit cannot belong even to H's boundary, since every neighborhood of a boundary point of a square meets that square's open interior.

This handles x=-a, x=b and v+1=rho at the north circle point. No equality case is discarded.

Every point of E's whole closed centered arc must therefore lie in x<-a or x>b. Connectedness of that arc makes it stay on just one of the two sides.

On the left, its entire upper angular interval is contained in (beta_a,alpha_X), whose length is strictly less than 2pi/9. Yet the actual closed centered arc has length exactly 2pi/9. This is impossible. The reflected argument excludes the right side.

Hence dist(O,H)<1/8, including exclusion of the alleged equality v=1/8. The conclusion concerns the original physical transmitter and its complete original slider.

## 7. Exact checks

I independently recomputed the fixed comparisons used in the new proof:

| Expression | Exact value |
| --- | ---: |
| (3/4)^2-1/2 | 1/16 |
| 3/4-(3/4)^2 | 3/16 |
| 3/4-3/5 | 3/20 |
| (23/16)^2-2 | 17/256 |
| 4/5-3/4 | 1/20 |
| 1+1/8 | 9/8 |

The endpoint cosine identity, the conversion between theta_X-beta_a and delta+asin(a/rho), and the full concavity sign were checked symbolically. These are exact scalar checks, not a numerical pose or finite parameter certificate.

## 8. Literal original callers and remaining limitations

For D02.L0134 the unchanged channel is W=0--H=5--B=4. W retains true loaded degree three, H true unloaded degree two, and B true loaded degree two. The original chord 02, all circle-resultant weights and every original mean remain. If this actual side pocket is occupied, the same actual unit 5 has distance less than 1/8 from O.

For D02.L0135 the literal channel is 3--4--5, and the same implication holds for its original transmitter 4. The complete previous capacity source supplies the correct upper-arc join from full component balance. No smaller simple-cycle certificate or endpoint properness equation is substituted.

The local theorem is broader than either caller because its statement requires only the displayed actual geometric pocket and endpoint containment. It does not give dist(O,H)<1/40 or <1/60. The old near-origin three-unit obstruction therefore cannot yet be invoked without an additional argument. Nor does this single occupied-pocket consequence close a whole original load row.

**Final disposition:** accept the exact 633b6b4a source as a complete force-free, all-mask, all-mean one-eighth proximity theorem. No source repair, force or normal change, physical motion, Lean compilation, CI, remote write or shared-ledger mutation was performed in this review.

