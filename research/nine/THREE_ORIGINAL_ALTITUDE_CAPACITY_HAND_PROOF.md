# A three-original capacity row from endpoint altitude

This theorem concerns three unchanged physical unit squares L, M and U with pairwise disjoint open interiors. It is a necessary inequality on the full original predicate; it assumes no common square orientation and introduces no branch. All coordinate intervals used below must have been proved on the entire original parent before this row is constructed.

Let m=c_M−c_L, n=c_U−c_M and d=c_U−c_L=m+n. Put D=||d||. Suppose the full parent proves

    m·d ≥ 0,   n·d ≥ 0,   |det(m,n)| ≤ A,   D ≥ B > 0,
    δ=A/B ≤ 7/10.

Then

    D ≥ f(δ),    f(z)=min(2,208/75−(29/15)z).                 (1)

The accepted `THREE_ORIGINAL_NARROW_STRIP_CAPACITY_HAND_PROOF.md`, sections 2–6, proves that for any physical middle square M, the intersection of M+B_(1/2) with a line at distance h≤7/10 from c_M has length at least f(h), regardless of M's frame.

## Projection and endpoint disks

The first two guards are equivalent to 0≤m·d≤D². Thus the orthogonal projection of c_M onto the line c_Lc_U lies on its closed endpoint segment. The actual distance h from c_M to that line is

    h=|det(m,d)|/D=|det(m,n)|/D ≤ A/B=δ.

Each original endpoint square contains its radius-one-half incircle. Physical nonoverlap implies that each endpoint center lies outside the interior of the Minkowski sum M+B_(1/2). On the endpoint line the projection of c_M lies strictly inside this Minkowski-sum slice: indeed M+B_(1/2) contains the unit disk centered at c_M and h≤7/10<1. Because the projection lies between the two endpoint centers, the lower endpoint must lie below the entire open slice, and the upper endpoint above it. Hence their distance D is at least the length of this slice. The slice bound and monotonicity of f give D≥f(h)≥f(δ), proving (1).

Closed projection guards retain their boundary. If one endpoint coincided with the projection, it would lie strictly inside the unit disk in the slice, immediately contradicting physical nonoverlap. No equality face is lost. Endpoints at slice boundaries and physical contact are allowed.

## Exact guards from already proved boxes

For interval vectors X,Y, let P(X,Y) be the exact interval sum of their coordinatewise products; multiplication is bounded by the minimum and maximum of its four endpoint products. This gives a valid enclosure of X·Y even when the physical vectors are dependent. Let T(X,Y) similarly enclose X_1Y_2−X_2Y_1. All operations have rational endpoints.

For any physical pair, center distance is at least one. An already proved owner-free support bound r≥1 may replace one when available. Consequently

    m·d=||m||²+m·n ≥ r_LM²+lower(P(m,n)),
    n·d=||n||²+m·n ≥ r_MU²+lower(P(m,n)).

The maximum of these lower bounds and the direct box lower bounds P(m,d),P(n,d) gives the recorded projection guards. A nonnegative lower bound proves the corresponding closed guard on the entire parent.

Since det(m,n)=det(m,d)=det(d,n), the minimum of the three absolute interval upper bounds is a valid A. The implementation uses |det(n,d)| for the third equivalent magnitude. An exact rational lower square root of the maximum of r_LU² and the box's squared-distance lower bound supplies B>0. The root is rounded downward and checked by integer-square arithmetic. Thus h≤A/B remains valid.

## Affine endpoint row

Suppose d_x∈[a,b] and d_y∈[c,e] are proved. The exact secants

    d_x² ≤ (a+b)d_x−ab,
    d_y² ≤ (c+e)d_y−ce

combined with D²≥f(δ)² imply

    −(a+b)d_x−(c+e)d_y ≤ −f(δ)²−ab−ce.             (2)

This is the printed rational row. Its coefficients at c_L are (a+b,c+e), at c_U their negatives, and at every other original zero. The middle original remains an essential geometric premise although its variables cancel from the final affine row. A certified interval guard is not inferred from a numerical LP point.

## Stronger slice-floor extension

A separately proved strengthened middle-square slice theorem may replace f by any rational nonincreasing lower slice-length function on [0,7/10]. In particular, if the independent stronger theorem gives slice length at least min(2,2√2−2h), then the rational floor

    f_*(h)=min(2,280/99−2h)

is valid because (140/99)²=19600/9801<2. The same projection proof and exact row (2) apply with f_* in place of f. This stronger extension is accepted only with its separate all-orientation slice proof; a numerical check is not its premise.

## Scope

All implications use three of the same nine original squares. All other originals, pair constraints, corner constraints, marked cones and strict mask bits remain in the caller. A row closes no cell by itself. A cell closure requires exact induction from its original path to a complete contradiction. No new case split or mandatory gate is introduced.
