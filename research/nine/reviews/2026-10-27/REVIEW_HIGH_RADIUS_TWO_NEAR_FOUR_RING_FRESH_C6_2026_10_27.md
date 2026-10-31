# Independent full audit: high-radius two-near four-ring recovery

Date: October 27, 2026.

Reviewer: c6_side, independently of the source author.

**Decision: ACCEPT the complete fresh geometric theorem and both complete
original caller families, with no correction.**

## 1. Exact source and recovery boundary

Source: ROOTED_HIGH_RADIUS_TWO_NEAR_BOUNDARY_FOUR_RING_EXCLUSION.md.

Frozen mathematical SHA256:

`f31c67f46c3d4318d67c887afbb4ee93997ac8e587c6d7f3d5a7bdc9fcb28b10`.

I read all 334 lines, reconstructed the complete half-lens maximization
and weak center-order proof, and checked the original load/degree joins.
I separately read the complete original planar uncrossing construction
through aggregation, the full unloaded-diamond-hub theorem, the full
origin-free genuine-leaf reduction used here, the current C4 origin
theorem's exact statement and extraction, and its separate full review.
The current decorated-diamond origin theorem and its separate rooted
review were also checked at the exact one-private-leaf scope.

This review accepts the fresh source at the displayed pin. It does not
claim byte recovery of the missing historical 5f73169d source, inherit
that source's pin, or extend to any missing historical forest statement.

## 2. Complete closed half-lens estimate

The center normalization is legitimate: exchanging the two near centers
makes the midpoint's longitudinal coordinate nonnegative, and transverse
reflection makes its distance b from the origin nonnegative. Both actual
center bounds then reduce to (m+a)^2+b^2<=q^2, with a>=1/2 from the
disjoint open incircles. No contact between the near units is assumed.

The common-contact center has distance at most sqrt(2) to each endpoint.
Their conjunction is exactly (a+|t|)^2+s^2<=2 on the origin side s>=0.
Replacing t by |t| can only increase its squared norm because m>=0.
For each fixed z=a+|t|, convexity in s gives the two stated endpoints.

On the curved endpoint, the complete squared norm is

    2+(m-a)^2+b^2+2(m-a)z-2b sqrt(2-z^2).

Its last term is convex over the entire closed interval. The b=0
alternative is affine, and the continuous endpoint at sqrt(2) is valid.
Thus the maximum is at precisely F1 or F2, without an interior maximum
or omitted limiting point.

For F1, the allowed upper bound on m is nonnegative, so squaring it
preserves the inequality. The resulting function of b is convex.
At b=0 it is at most 2+q^2-q; at b=sqrt(q^2-a^2) it is the square
of the displayed difference of square roots. Rationalization gives its
upper bound 2-q^2, including a=q. Since q>1/2, this endpoint is strictly
below the first uniform bound. This is a whole-domain argument, not a
sampled endpoint assumption on a.

For F2, the coefficient of m changes sign exactly at a=1/sqrt(2).
The source treats both ranges. In the lower range, m<=q-a gives the
correct positive-coefficient bound, and q+sqrt(2)-2a remains positive,
so its subsequent monotonic comparison is valid. In the upper range,
discarding the nonpositive m term gives F2<=q^2. The common threshold
is retained by both inequalities.

I independently recovered the final upper bound 2881/1600, strictly
below the physical boundary-center lower bound (27/20)^2. This includes
b=0, s=0, z=a, z=sqrt(2), a=q, and a=1/sqrt(2). When b=0, reflecting
the transverse direction indeed covers the other closed half-lens, so
no boundary common neighbor survives on either side of the line.

The physical boundary-center bound uses only a real circle corner and
the center-to-vertex radius 1/sqrt(2). The strict radius window supplies
R>103/50 and 1/sqrt(2)<71/100. No positive corner multiplier is required.

## 3. Selected straight-center order and all weak cases

The no-crossing argument is complete. If two nonincident positive
center segments cross internally, their four endpoints are in convex
order. The cosine law at each vertex uses two distances at least one
and the opposite contacting diagonal at most sqrt(2), so each angle
is at most 90 degrees. Their sum forces a rectangle, and the same
distance bounds force all four sides to have length one.

At center distance one, the two incircles touch. A separating support
line must be their common tangent, so both actual square half-widths
along the center direction equal 1/2. This makes the direction an own
axis of both squares. The four units are therefore exactly the aligned
2-by-2 junction. Its two crossing center edges are the two opposite
point-contact pairs that the original compatible selection forbids
simultaneously. This is the precise selected-graph premise; an arbitrary
physical touching graph is not silently substituted.

A nonincident center on a contact segment would split it into two
lengths each at least one, contradicting the whole length at most
sqrt(2). The same argument excludes overlapping nonincident collinear
segments. The actual selected four-ring therefore has a straight plane
center drawing.

The weak-convexity argument is also valid. If C lay in the interior of
triangle ABD, the two cosine-law inequalities at C would put A,B,D
in a closed half-plane through C, with A strictly on its positive side.
Their triangle cannot then contain C in its interior.

A collinear middle center cannot lie between a contacting pair.
Consequently the only possible collinear triple has C between its two
cycle neighbors B,D. Their opposite directions and the two nonnegative
cosine projections force both right angles, then all three incident
distances in (13) are exactly one. This is the complete T endpoint;
it is not discarded by assuming a strictly convex quadrilateral.

For opposite near centers E,F, their distance is less than 2q<2.
They cannot be the length-two opposite pair in the T endpoint. If
they are its other opposite pair, the remaining centers are strictly
on opposite sides of their line. This proves the exact strict side
conclusion needed for the half-lens contradiction in every weak case.

## 4. Force-free four-ring theorem

A unit meeting the closed epsilon disk has center norm at most
epsilon+1/sqrt(2)<29/40. The proof applies this only as a geometric
estimate; no square is translated or altered.

The selected ring E-B-F-C-E puts the two physical boundary centers
strictly on opposite sides of the near-center line. The half-lens
theorem puts every physical boundary common neighbor strictly on its
side away from O, or excludes all such neighbors if the line contains O.
These statements contradict each other directly.

The resulting theorem permits arbitrary true degrees, circle weights,
frames and additional forces at all four units. It needs no E-F contact.
The only graph restriction is the original compatible positive four-ring,
and the only load requirement is physical boundary status of B,C.

## 5. Complete original graph and load callers

For the same-role decorated-diamond callers, the current c11df54a origin
theorem supplies a unique common open-origin H and excludes the initially
disjoint layouts. The genuine private leaf root X avoids O, so the full
genuine-leaf alternatives give a real S leaf, d>1, and X meeting closed
D_epsilon. The original H equation is not reduced to two forces.

When H,X are both hubs, the two untouched private tips have exactly
their two original block forces. An unloaded channel would strictly
separate its two neighbors, contradicting the real central HX contact.
Both tips are therefore physically boundary, and the actual outer
four-ring has H,X opposite as required.

When H,X are both tips, the untouched hubs retain their true degree-three
stars. The complete selected unloaded-hub theorem applies to each with
all three original forces and makes each loaded. They are the two
boundary common neighbors in the actual selected outer four-ring.
No HX contact is assumed in this role.

For the opposite-private-leaf C4, the current 95e44547 C4 origin theorem
supplies the shared open-origin H and excludes the disjoint layout.
The exact graph has untouched degree-two U,V and genuine leaf root
X of degree three. If either U or V were unloaded, its actual positive
width W>=1 separates the whole endpoint units H,X. Their center
projections differ by at least W plus both half-widths, hence at least
two. This contradicts their near-center distance <2q<2. Thus both are
physically boundary and the four-ring theorem applies. This explicitly
covers all four original U/V load masks, not just the both-loaded mask.

All further H forces, all actual means, physical circle masks and nine
units remain. The two mixed diamond roles and unrelated bridge layouts
are not claimed by this source.

## 6. Independent exact checks

Thirteen exact rational identities or comparisons were reconstructed:

| Quantity | Exact value |
| --- | ---: |
| 2+q^2-q-2881/1600 | 0 |
| 2q^2-q | 261/800 |
| q+17/12-1-137/120 | 0 |
| 2881/1600-(137/120)^2 | 179/360 |
| 2881/1600-q^2 | 51/40 |
| (27/20)^2-2881/1600 | 7/320 |
| 17/4-(103/50)^2 | 4/625 |
| (71/100)^2-1/2 | 41/10000 |
| 103/50-71/100-27/20 | 0 |
| 1/60+17/24-q | 0 |
| (17/24)^2-1/2 | 1/576 |
| 2-2q | 11/20 |
| q^2-1/2 | 41/1600 |

All strict inequalities are supplied by the stated actual radius or
epsilon bounds where an intermediate rational identity is zero.

**Final decision: full ACCEPT at f31c67f4, with no correction.**
No shared ledger, original gate, remote, Lean file or workflow is changed.

