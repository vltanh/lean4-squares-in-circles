# Independent full review: protected outward rays and central junction capacity

**Date:** October 30, 2026 UTC. **Reviewer:** axial-chain agent, separate
from the author of both sources below. Both complete sources were read and
their mathematical assertions reconstructed. No dependency on a selected
planar or torque-balanced stress was introduced.

| Complete current source | SHA256 |
| --- | --- |
| NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md | 82ff38f0d73045652c517a10f70f86d93bc0d55d540f3b67c99b04896cc049de |
| NEAR_CENTRAL_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_2026_10_30.md | f9f2e43ce31d3275d0f111b1ef8b48592607cc03920c3610ef8fefcff9b7bda0 |

## Conclusion

**PASS for both sources at their full stated scopes, with no repair
required.** The first protects the full closed outward ray from every
other closed actual square, including noncontacting and unstressed units.
The second excludes a ninth arbitrary unit around the actual near-central
four-square junction, retaining all orientation and contact endpoints.

Neither source by itself proves that two long paths cross or that their
crossing is the required central four-square junction. Those complete
caller obligations remain separate and are not certified by this review.

## 1. Protected outward rays: complete reconstruction

The farthest-corner formula gives the strict actual center bound
`|c|<M=91/60`, with exact excess `31/57600` at M. For an endpoint
with `c_A.n>=89/60`, the ray for `0<=t<1/2` lies in its open incircle.
An interior point of one square cannot belong to another closed square
under disjoint-open-interior packing, because the latter has nearby
interior points. This handles the first part of the ray, including its
starting center.

For `t>=1/2`, a hypothetical other-square center differs from c_A by
`xi*n+eta*n_perp`, with

`-1/4 < 1/2-1/sqrt(2) <= xi < 1/30`,
`|eta|<=1/sqrt(2)`.

Therefore `xi²+eta²<1/16+1/2=9/16<1`, contrary to the physical
center separation at least one. This covers the closed `t=1/2`
threshold, arbitrary farther points, and physical boundary-only contacts.
No outward circle-contact hypothesis is used.

The long-support-gap caller has projected center gap at least three.
Combining it with the strict M center bound gives the stated endpoint
projections beyond `89/60`, so both outward rays satisfy the theorem.

For angular control, the transverse squared coordinate is below
`M²-(89/60)²=1/10`, hence its absolute value is below 1/3. The
direction deviation has tangent below `20/89<1/4<2-sqrt(3)`.
Along the ray the deviation is `atan(Y/(X+t))`, with constant sign
and decreasing absolute value. Thus its circle exit differs from the
endpoint's center direction by less than pi/12. If four center
directions are pairwise separated by more than pi/6, their corresponding
open angular neighborhoods of halfwidth pi/12 are disjoint, preserving
cyclic order. The source properly requires the caller to prove that
separation; it does not assert it from one long pair alone.

The center-to-actual-application route in the final section is also
sound: each open segment is within the corresponding original square's
interior. Using these routes avoids incorrectly treating a force line
lying on a square boundary as an interior crosscut. No global crossing
statement was smuggled into this local fact.

## 2. Near-central four-square junction: complete reconstruction

Four disjoint square interiors meeting at p contribute at least four
right angles. They must all be right angles, use the four consecutive
quadrants, and have the same two side axes. Their unit lengths force
exactly the aligned two-by-two block centered at p. This covers
potential side-interior alternatives by excluding them through the
angle sum; a side-interior contribution would have angle pi.

Every further square's open radius-half incircle misses the open block.
An open overlap cannot be confined to the internal seams. Consequently
its center has distance at least 1/2 from the closed block, including
nearest-boundary limits.

If a further center lies outside just one coordinate interval of the
block, its excess in that coordinate is at least 1/2. The bound
`|p_x|,|p_y|<=1/60` then puts it in the corresponding cap beyond
`89/60`. A coordinate equal to an interval endpoint belongs to the
closed interval and is handled by this same one-coordinate case; it
is not lost at the two-coordinate split.

If it is outside both intervals, its positive excesses s,t obey
`s²+t²>=1/4`, hence `s+t>=1/2`. Both absolute coordinates are at
least `59/60+s` and `59/60+t`. This forces squared norm at least

`2*(59/60)²+59/60+1/4=5701/1800`,

exceeding `M²=8281/3600` by `3121/3600`. Thus this entire diagonal
escape region is impossible, without any orientation restriction on the
additional unit.

All remaining centers lie in four caps. Adjacent caps are disjoint
because `2*(89/60)²>M²`; opposite caps are disjoint by their signs.
In one cap, horizontal coordinate width is at most 1/30 and transverse
width at most `2/sqrt(10)`. Its squared diameter is at most

`1/900+4/10=361/900<1`.

Physical center separation therefore permits at most one additional
unit in each cap. Four original junction units plus at most four
completions gives eight total. All inequalities include the printed
closed junction thresholds and cap endpoints.

The eight-unit witness is valid: four aligned centers `(+-1/2,+-1/2)`
and four at `(+-3/2,0),(0,+-3/2)` are pairwise separated in at least
one coordinate by one. Their maximal squared corner radius is 17/4.
This confirms why the ninth physical unit is essential to the intended
two-channel contradiction.

## 3. Verification record and boundaries

The rational center, diagonal-escape, adjacent-cap and cap-diameter
identities above were recomputed exactly using rational arithmetic.
The radical comparisons use only positive squaring. The proof is
continuous and force-free; there is no sampled pose or orientation grid.

No original fine/coarse flag, selected normal, actual mean, physical
circle mask, stress coefficient or repository metadata was changed by
this review. No Lean compilation, CI or full unrestricted n=9 claim is
part of the result.
