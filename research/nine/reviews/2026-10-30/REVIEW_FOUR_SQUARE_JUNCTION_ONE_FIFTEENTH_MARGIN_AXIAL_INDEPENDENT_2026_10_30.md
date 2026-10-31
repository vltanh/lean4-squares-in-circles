# Independent full review: four-square junction with a one-fifteenth margin

**Date:** October 30, 2026 UTC. **Reviewer:** axial-chain agent, separate
from the author. The complete source, including its standalone one-cap
corollary and retained eight-unit witness, was read and reconstructed.

Reviewed frozen source:

`FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_WITH_ONE_FIFTEENTH_MARGIN_2026_10_30.md`

* Bytes: 4756.
* SHA256: `df237a44886f100d3fa901981c6c747b0dfa827d61ef4c1f046b476df1c1ada4`.
* Git blob: `7a050d16121e2a01ef00ddf1dc4f98ff67f8373f`.

## Conclusion

**PASS at the full stated scope, with no repair required.** Four actual
interior-disjoint unit squares meeting at a point whose two coordinates
in their common square frame have absolute value at most 1/15 admit at
most four additional arbitrary units in the disk of squared radius
1105/256. The closed coordinate thresholds and every boundary case are
retained. The one-cap assertion at the stronger threshold 22/15 is
independent of the existence of a four-square junction.

## Complete geometric reconstruction

At a common point of four squares, each local interior sector has angle
at least pi/2. Pairwise disjoint interiors make their total at most
2*pi, so each sector has angle exactly pi/2. The four squares therefore
have that point as a vertex and their sectors are the four consecutive
quadrants in one orthonormal frame. Unit side lengths identify their
union exactly as the translated closed two-by-two block. A square
meeting the point in a side interior or its own interior would consume
more than pi/2 and is excluded by the same sector argument.

For each actual square the corner formula yields
`R^2 >= |c|^2+|c|+1/2`. At `M=91/60`, the right-hand side exceeds
`Q=1105/256` by `31/57600`. Thus all actual centers have strict norm
less than M. The disjoint open half-unit incircles of distinct squares
also imply center separation at least one.

The incircle of an additional unit cannot meet the open block. An
alleged open overlap has a point off the internal seams and therefore
meets one of the four actual square interiors. The same reasoning,
using an arbitrarily small move into the block at a nearest boundary
point, gives distance at least 1/2 from the closed block. This handles
boundary-only contacts and centers aligned with a block edge.

Split a completion center by membership in the two closed block
coordinate intervals. Membership in both contradicts clearance.
If it lies outside exactly one interval, its excess in that coordinate
is at least 1/2, so that absolute coordinate is at least
`3/2-1/15=43/30`. Equality in the other coordinate at an interval
endpoint remains in this case and is not omitted.

If it lies outside both intervals, let its two positive excesses be
s and t. Clearance gives `s^2+t^2>=1/4`, hence `s+t>=1/2`.
The respective absolute coordinates are at least `14/15+s` and
`14/15+t`. Its squared norm is consequently at least

`2*(14/15)^2+14/15+1/4=2633/900`,

which exceeds `M^2` by `2251/3600`. No diagonal completion center
is possible. This reasoning uses only the incircle and permits every
orientation of the completion square.

All completion centers therefore lie in four axial caps beyond
`b=43/30`. Each such cap is contained in a rectangle of side lengths
`M-b` and `2*sqrt(M^2-b^2)`. Its squared diameter is at most

`(M-b)^2+4*(M^2-b^2)=713/720<1`.

At most one actual center occupies each cap. Opposite caps are disjoint
by sign; adjacent caps are disjoint because
`2*b^2-M^2=6511/3600>0`. Thus at most four additional units occur,
giving eight in total. There is no assumption about contact graphs,
circle masks, physical means, external loads, or force and torque.

## Stronger coordinate corollary and sharp count witness

Repeating the same argument under coordinates at most 1/30 gives
`a=29/30`, `b=22/15`, diagonal norm excess `2827/3600`, and cap
squared diameter `719/1200`. These identities were checked exactly.
The final cap diameter proof itself depends only on the actual center
bound and physical center separation. Rotation therefore gives the
claimed standalone assertion: two actual centers cannot both satisfy
`n.c>=22/15` for any one unit direction n. No junction premise is
silently retained in this assertion.

The eight-unit witness has four centers `(+-1/2,+-1/2)` and the
four centers `(+-3/2,0),(0,+-3/2)`, all with the same square axes.
Every pair is separated in at least one coordinate by at least one;
its largest squared corner radius is `17/4<Q`. It has the required
junction at the origin. Thus eight is attained and the ninth original
unit is indispensable for the intended contradiction.

## Verification record

All displayed rational identities, cap margins, and source hashes were
recomputed independently. This is a continuous argument, without pose
sampling. A caller still has to establish the actual junction and its
location in the actual common square frame; neither is supplied by
this local source. No original case flag, stress, mean, mask, repository
metadata, Lean file, CI state, or publication was changed by this review.
