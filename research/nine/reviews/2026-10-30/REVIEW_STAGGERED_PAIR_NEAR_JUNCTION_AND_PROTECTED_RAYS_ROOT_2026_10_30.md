# Root review: staggered pairs, central junctions and protected outward rays

Date: October 30, 2026 UTC (October 29, America/Chicago).

**Verdict: PASS for the complete three sources at their stated scopes.**
I read each complete source and reconstructed the following proofs. The
author is annular_capacity. The proposed later two-channel assembly is
not part of this review and requires its own full proof and review.

## Exact source identities

| Source | SHA256 |
| --- | --- |
| STAGGERED_CENTRAL_PAIR_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md | `8cce720d62d361f02912c49962d0da51aac4de382ac2294defc2f67e313ed98f` |
| NEAR_CENTRAL_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_2026_10_30.md | `f9f2e43ce31d3275d0f111b1ef8b48592607cc03920c3610ef8fefcff9b7bda0` |
| NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md | `82ff38f0d73045652c517a10f70f86d93bc0d55d540f3b67c99b04896cc049de` |
| NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md (quantitative input to the first source) | `33168fb5ab4605739746348d1425b47da33c6f2a64803357f1f0608515a160b8` |

The complete quantitative input has my separate full review in
REVIEW_PAIR_CAPACITY_AND_LARGE_BLOCK_DIAGNOSTICS_ROOT_2026_10_30.md.

## 1. The pair capacity retains the actual stagger

The two given axis-aligned squares really cover the rectangle C0 formed by
their common vertical interval. Its upper endpoint is y_lo+1/2 and its
lower endpoint is y_hi-1/2. Both inequalities relative to +/-delta have
the stated directions. The covered rectangle contains the centered disk
of radius delta, even when the two centers have different heights.

An extra square cannot overlap the interior of C0: an open overlap has
points off the central seam and would overlap an original unit. Applying
the separating-axis theorem to this actual occupied rectangle is valid;
it does not enlarge a nonconvex occupied union to its convex hull.

For every unit normal the rectangle's support is at least
(1-|s|)|n_x|+delta|n_y|, at least delta. Equality requires a vertical
normal because 1-|s|>delta. An extra-owned separating axis has minimum
support at most delta by the extra's own-coordinate hypothesis, so that
case also supplies a vertical separator. A horizontal rectangle-owned
separator would force |c_x|>=17/12, whereas the extra has norm at most
sqrt(2); the squared contradiction has exact reserve 1/144.

Thus each qualifying original extra lies wholly in one of the actual
upper/lower half-planes, each of clearance at least delta. The complete
single-square arc proof depends only on its own-coordinate bound,
clearance and containing radius. It therefore applies without changing
either central-square height. The strict three-arc comparison allows at
most two qualifying extras in each cap, hence at most four in all.

The result neither extracts a near-central pair from an arbitrary channel
nor limits the other extras failing the own-coordinate condition.

## 2. A near-central four-square junction has total capacity eight

At a common point four disjoint square interiors contribute four local
angles, each at least pi/2. Their disjointness forces exactly four vertex
quadrants filling the full angle. The actual four units therefore form
one aligned two-by-two block. No stress or generic-contact premise is
needed for this geometric conclusion.

The center bound |c|<91/60 follows from the actual farthest corner and
the positive rational reserve 31/57600. Every extra's open half-unit
incircle avoids the occupied block interior, so its center has distance
at least 1/2 from the closed block. Boundary nearest points do not evade
this implication, by continuity toward interior points.

If an extra center is outside both coordinate intervals of the block,
the two excesses s,t have s^2+t^2>=1/4. The hypothesis
|p_x|,|p_y|<=1/60 implies norm squared at least
2(59/60)^2+59/60+1/4=5701/1800. Its excess above (91/60)^2 is
3121/3600>0. This excludes every corner sector, including the limiting
cases by the same inequality.

Every remaining extra center lies in one of four disjoint caps with a
signed coordinate at least 89/60. Each cap has squared diameter at most
(1/30)^2+4/10=361/900<1. Distinct square centers have separation at least
one from their open incircles, so each cap contains at most one extra.
Four block units plus at most four extras prove the stated bound eight.

I checked the eight-unit sharpness example at squared radius 17/4. This
is also a useful scope check: two physical channels are not excluded as
an eight-square configuration. An arbitrary translated two-by-two block
does not meet this theorem's near-origin hypothesis.

## 3. Protected rays require neither load nor circle contact

For an endpoint with c_A.n>=89/60, the ray points with parameter
0<=t<1/2 lie in its open incircle. Another closed square cannot meet
that open interior, because interior points of the other square are
arbitrarily close to every boundary point.

For t>=1/2, membership of c_A+t*n in another square E would give,
in the n frame, -1/4<xi<1/30 and |eta|<=1/sqrt(2). Hence the two
centers would have squared separation strictly below 1/16+1/2=9/16,
contradicting their incircle separation. This includes the equality
parameter t=1/2 and all closed physical contacts.

A long support gap gives each endpoint the requisite signed projection
strictly beyond 89/60, so both outward rays are protected against every
other actual square, irrespective of positive-component membership.
The transverse bound is |Y|^2<1/10, so |Y|/X<20/89<1/4<tan(pi/12).
The angle along an outward ray stays between its center angle and its
axis direction. Consequently pairwise endpoint angular separations
greater than pi/6 give disjoint spoke angular intervals and preserve
their cyclic order at the containing circle.

This lemma supplies actual exterior access. It does not by itself prove
alternation of two long endpoint pairs, their physical crossing, or the
location of a four-square junction. Those are separate caller claims.

## 4. Adoption scope

All three proofs retain arbitrary independent orientations of the extras,
the unchanged disk center and every weak physical boundary. They use no
common angular/planar stress selection. None changes an original fine or
coarse checklist flag, proves the full nine-square lower bound or proves
equality classification. The rational reserves were checked exactly;
no pose search, numerical mesh, Lean build or CI was used.
