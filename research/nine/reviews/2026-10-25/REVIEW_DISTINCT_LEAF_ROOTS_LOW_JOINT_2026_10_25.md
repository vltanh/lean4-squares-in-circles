# Independent review: all distinct-leaf-root layouts share one upper remainder

Date: October 25, 2026. Reviewer: root, independently of `global_pressure`.

**Verdict: PASS** for
`DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md`, including its
complete five-layout/six-load join. The theorem excludes the entire
strict lower interval `R^2<17/4` and retains the full upper interval
and equality endpoint. It closes no full-window gate and introduces
no new subgate or scalar certificate.

## 1. Exact root normal form, not an assumed common orientation

I read the complete leaf and bridge sources and
`FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md`. A genuine D leaf has
its inner vertex in the relative interior of the root's support side,
and its positive radial distance is less than one. Hence its root
contains O in its open interior. Any genuine S root contains O when
`d=sqrt(R^2-1/4)-1<1`, by the real inward support segment.
Thus no D leaf can occur at either of two distinct roots in this
strict interval: the other root's interior approaches O and would
meet the D root's open neighborhood of O.

For a tilted S root, its two inward side components are positive.
O has coordinates `da,db` strictly between zero and one in the
original corner chart, so it too would be an interior point. Both
remaining S roots must therefore align with their own leaf directions.
Their radial intervals contain O strictly; O must be on a transverse
side of each. Disjoint open tangent half-planes at O force a common
boundary line and opposite half-planes. Parallel leaf directions would
give the same original radial leaf square; therefore the directions
are antipodal. This proves the displayed pair of aligned roots and
actual opposite leaf-force directions, without changing any root degree.

## 2. A whole physical boundary common neighbor is impossible

I independently checked the two contact-vector cases in Section 2.
For `a=1-d in (0,1/10)`, a circle-touching common neighbor would
supply contacts p,q with opposite vertical signs and
`p_x>=-a`, `q_x<=a`. Every point of that neighbor has norm at
least `R-sqrt(2)>1/2`. Whether `p_x` is positive or negative,
the dot product is strictly below `|p||q|/5`. Their angular
separation exceeds `arccos(1/5)>pi/3`.

I read the full `CIRCLE_CONTACT_ANGULAR_ORDER.md`. Its Lemma 4.1
bounds the entire shadow of every physical boundary square below
`pi/3`, independently of circle-load positivity, degrees or contacts.
Thus no such common neighbor exists, even for zero-stress contacts.
The proof keeps both complete arbitrary physical corner masks.

The unloaded-neighbor exclusion in Section 3 is also exact. A genuine
leaf root contains O, so its normal support value alpha is nonnegative.
The actual unloaded degree-two channel has reserve `w>=1`, while the
far endpoint's sharp center and halfwidth bounds give `alpha+w<=d<1`.
This contradiction uses no changed degree at either endpoint.

## 3. The touching-pair resultant and the antipodal leaf sum

The same circle-order source gives center separation greater than
`pi/5`, an empty minor center arc for a touching boundary pair, and
contact gap less than `2pi/5`. The all-mask original circle-force
direction estimate is less than `pi/12` from the center direction;
its precise scope is stated in
`BOUNDARY_THREE_PATH_RESULTANT_CONE.md` and its local cited proof.
Both individual zero-weight endpoints are retained.

The actual pair-force directions consequently have ordered difference
in `(pi/30,17pi/30)`. Their positive sum is nonzero and points strictly
between them. If this direction equaled any third physical boundary
center direction, that center would have to lie between the pair's
center directions: otherwise it would be within `pi/12` of an endpoint
center, contradicting the proved `pi/5` separation. But the actual
contact pair's minor arc is empty. This proves the pair-resultant lemma.
No radial shape is needed for this third-body geometric conclusion.

For the actual two antipodal genuine leaves, their resultants are
opposite multiples of the center axis. The whole component force sum
would make the touching pair's sum either zero or a positive multiple
of one of those two original center directions. Both alternatives are
excluded. No fictitious combined square or omitted force is used.

## 4. Exact join and retained upper domains

I checked every row against the complete original four-body/two-bridge
load table. The adjacent C4 one-load row has a real unloaded neighbor
of a leaf root. Its two-load row has exactly the touching loaded pair
and two antipodal loaded leaves. In each opposite C4 and diamond row,
the designated loaded body really is a physical common neighbor of
both roots. Thus all five distinct-root layouts and their six original
load orbits are excluded throughout the strict lower interval.

The two-tip diamond already has its separate full-window accepted
boundary-hub exclusion; it is included in this geometric reduction but
not counted as a new exit. Mixed S/D roots already require strict
`R^2>17/4`, and D/D is excluded throughout. Every remaining SS or SD
upper domain retains its original label, both radius limits where
applicable, true forces, masks, means and all three arbitrary extras.

No conclusion for two merely near-origin roots in the upper interval
is inferred. The source explicitly retains the actual second common
neighbor, extra connected tip, or unloaded bypass required by each
remaining layout. All original nine squares remain, and no complete
coarse cell is declared closed. No Lean compilation, CI or workflow
dispatch was used.
