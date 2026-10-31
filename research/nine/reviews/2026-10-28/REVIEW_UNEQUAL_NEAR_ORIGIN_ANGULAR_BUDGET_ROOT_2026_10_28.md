# Independent review: the unequal-distance near-origin angular budget

Date: October 28, 2026 UTC. Reviewer: root continuation.

**Verdict: complete independent PASS without repair.** The general continuous angular budget, both exact three-unit specializations, and the conditional coordinate criterion are valid on their entire stated domains. No original family is closed by this lemma alone.

## 1. Exact manuscript and review independence

The complete reviewed source is UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md, SHA256 741ff2415b91fa8d490c601185994b7d947e000003c1ca702e423677eea3684e, 9,973 bytes.

Pentagon authored the unequal-distance formulation and the useful mixed constants. I did not supply or repair the new general theorem, either trigonometric threshold or the coordinate criterion. The manuscript reproduces the entire required one-square argument, so its general theorem is self-contained. I read all of its current bytes, independently reconstructed each origin-location case, and checked every exact constant and endpoint.

The complete old equal-distance source was read again at its current 0fa62 hash. The optional physical source comparisons are separately checked below; they are not hidden premises in the new theorem. All four source/provenance hashes match the exact current bytes.

## 2. Precise general statement

There are finitely many actual closed unit squares S_i with pairwise disjoint open interiors. A common radius d satisfies 0<d<1/2. Each square has a possibly different bound 0<=delta_i<d, satisfies dist(O,S_i)<=delta_i, and has every actual vertex at norm strictly greater than d.

The conclusion is the necessary inequality

    sum_i acos(delta_i/d)<=pi.

Distances concern whole actual squares. Neither center distances nor common orientations occur. The weak distance endpoints are allowed, and the strict vertex margin is retained. The source correctly does not strengthen the final non-strict inequality without an additional strict premise.

## 3. Outside-origin case, including attained distance bounds

If O is outside a square, its nearest point exists and cannot be an actual vertex: that would put a vertex at distance at most delta<d. In its actual own orthonormal frame the nearest point is therefore in a side's relative interior. After signs are fixed, the square has the exact form

    [a,a+1] times [b,b+1],
    0<a<=delta, b<0<b+1.

This is only a change of coordinate axes about the original origin. The actual square is not translated or altered.

The two nearest-face vertices have squared norms a^2+b^2 and a^2+(b+1)^2 greater than d^2. Thus both transverse endpoints lie strictly beyond the relevant test-circle heights. Every test-circle point with x>a has transverse magnitude less than sqrt(d^2-a^2), while x<=d<a+1 because d<1/2. It is strictly inside all four original faces.

The resulting open arc has length exactly 2acos(a/d), at least 2acos(delta/d). Equality a=delta is legitimate. Strict vertex margins ensure open membership of that whole arc but do not by themselves require a strict improvement of its angular length; the source correctly preserves this distinction.

## 4. Boundary and interior origin cases are complete

If O is on a square boundary, it cannot be a vertex because every vertex is farther than d. It is in a side's relative interior. The preceding argument with a=0 gives an entire open semicircle in the open square. Its measure pi is at least 2acos(delta/d), including delta=0.

If O is in the open square, opposite faces cannot both cut the test circle: their separation is one, whereas its diameter is strictly below one. At most two faces cut it, and two must be adjacent.

With no cutting face, the whole circle is inside except for possible tangencies of zero angular measure. With one cutting face at positive distance from O, the removed outward arc has measure strictly below pi, leaving more than pi.

With two adjacent cutting faces at positive distances a,b<d, their common actual vertex has norm sqrt(a^2+b^2)>d. Consequently

    acos(a/d)+acos(b/d)<pi/2.

This follows by comparing a/d with sqrt(1-(b/d)^2) on the positive acute branches. The total removed angular measure is at most twice this sum, hence strictly below pi. More than pi remains in the open square. Tangencies have zero measure, and all other faces are inactive on this circle.

No connectedness assertion about the complete interior-origin intersection is needed. The proof uses its complete measure, so it covers any multiple-arc pattern. These cases exhaust all positions of the origin and establish the one-square lower measure bound throughout the declared domain.

## 5. The global angular sum uses the same actual circle

The intersections of different open squares with the fixed radius-d circle are disjoint measurable sets. Their total angular measure is at most 2pi. Summing their individual lower bounds gives

    2 sum_i acos(delta_i/d)<=2pi.

No pairwise arc-order assumption or common frame is needed. The argument covers any finite number of units and does not use forces, a containing radius, a selected graph, or a load allocation. It is therefore a reusable necessary condition independently of the later physical applications.

## 6. Exact first three-unit specialization

For d=19/300, the prescribed distances 1/40,1/40,13/300 normalize to 15/38,15/38,13/19, all strictly below one. Put alpha=acos(15/38), beta=acos(13/19).

Both 2alpha and pi-beta belong to (pi/2,pi): 15/38<1/sqrt(2), all arguments are positive and less than one, and beta lies in (0,pi/2). The exact cosine values are

    cos(2alpha)=-497/722,
    cos(pi-beta)=-494/722.

Their positive difference 3/722 and strict decrease of cosine on [0,pi] imply 2alpha>pi-beta. Hence 2alpha+beta>pi, violating the proved budget.

Thus the three stated actual distances are impossible when every actual vertex of all three units is farther than 19/300. All three distance bounds may be attained. The strict contradiction comes from the exact cosine reserve, not from treating a weak distance bound as strict.

## 7. Exact older-margin specialization and coordinate test

For d=3/50, distances 1/40,1/40,3/80 normalize to 5/12,5/12,5/8. The corresponding cosines are -47/72 and -45/72. Their difference is 1/36>0, and the same acute-branch argument gives the required strict angular excess. This is a separate valid specialization; it does not weaken the vertex premise of the first one.

For an actual own-frame rectangle

    U=[x-1,x] times [p-1,p],
    0<x<61/60, 0<p<26/25,

the nearest-point distance formula is exactly

    dist(O,U)^2=max(x-1,0)^2+max(p-1,0)^2.

The strict positive-coordinate bounds ensure that the only possible gaps are beyond the lower faces. They give

    dist(O,U)^2<(1/60)^2+(1/25)^2
               =169/90000=(13/300)^2.

Both x>=1 and p>=1 strips remain included; the argument does not assume U contains O. The full criterion still requires the actual four-vertex margin and two other distinct actual units meeting the first specialization. No coordinate condition is inferred from a small center, an occupied pocket, or a diagram.

## 8. Optional actual-source comparisons and exact limits

The accepted occupied force-free side-channel theorem 5e8f69ad gives its actual transmitter distance less than 1/40 and every vertex farther than 7/100. Its original arbitrary endpoint degrees and full physical scope were independently checked in root review 2a099d91. It provides one of the first two units only when its actual occupied-pocket premise is present.

The complete C7 inner side/corner restriction b9329b7a is geometric for a finite physical enclosure with every enclosing center below 91/60. It gives the enclosed unit's two own center coordinates below 1/2+121/7200 in absolute value, hence distance less than sqrt(2)*121/7200<1/40, and every vertex farther than sqrt(5/2)-91/60>19/300. Its actual finite enclosing ring and all original chords must remain. I read this complete source in the current continuation and checked the literal numerical margins.

The radial-tip theorem acd1a2b5 supplies the stronger third-unit distance less than 1/60 and vertex margin greater than 7/100 only on its stated entire radial local interface. I read it in full and checked the new original-Q argument, all four vertices and its local scope. The separate complete cycles review a68f8673 was also read in full; it independently passes the actual local theorem and conditional original D02 join, with cycles' separate channel authorship disclosed.

These are legitimate comparisons of already proved constants. None enters the proof of Sections 1--6 of the target, and none establishes the missing unique-mask hub coordinate p<26/25. The new budget does not itself exclude every U3 hub, every occupied closing pocket, or an original graph/load family.

## 9. Exact manifest and disposition

| Source or review | SHA256 | Role |
| --- | --- | --- |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | Complete earlier radius-free equal-distance proof; all needed arguments are reprinted in the target |
| FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md | 5e8f69ad14c78b6ad99a1ba46855fc3627df5ccc1d5451f295826d2b06709abb | Optional actual occupied-channel constants |
| REVIEW_FORCE_FREE_ONE_FORTIETH_CHANNEL_PROXIMITY_ROOT_2026_10_28.md | 2a099d9115acd5e01acb3fb929b9e80c31257c5b942591c21407d94cb6477ade | Existing complete independent review of that channel input |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Optional actual enclosed-unit constants |
| TERMINAL_HUB_AXIS_RADIAL_TIP_NEAR_ORIGIN_INJECTION.md | acd1a2b515779188a9e029d7e9b4a4c0182cde9c43b58fb52cd2a4237094761a | Optional stronger radial local third-unit bound |
| REVIEW_TERMINAL_HUB_RADIAL_NEAR_ORIGIN_INJECTION_CYCLES_2026_10_28.md | a68f86733559921f19f8344a926944a5f252b88cf26c4be23233c448ef39816c | Separate full independent review of the radial local theorem |

**Accept the general budget and both exact corollaries without source repair, with zero original fine or coarse flag credit.** The entire proof is continuous and radius-free, and all distance and origin-location endpoints are retained. It supplies a weaker sufficient proximity requirement for a third actual unit; the physical caller still has to prove that unit's distance and every vertex margin.

No numerical pose search, sampled angular interval, force deletion, changed application, altered normal, common-orientation assumption, Lean compilation, CI/workflow dispatch, remote write or shared-ledger mutation occurred in this review.
