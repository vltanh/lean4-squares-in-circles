# Independent full review: translated junction capacity by two caps per axis

**Date:** October 30, 2026 UTC. **Reviewer:** axial-chain agent, separate
from the source author. The entire current source, including the exact
translation region, both whole boxes and the optional long-channel
caller, was read and reconstructed.

Reviewed source:

`TRANSLATED_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_BY_TWO_CAPS_PER_AXIS_2026_10_30.md`

* Bytes: 9167.
* SHA256: `17f78403de1ab75d0de0aba42bf1344dd82e9c64822bf8743bd1e9f2d2ea5260`.
* Git blob: `6fec6447b4c37f34a5ce6635669c51ee9715b704`.

## Conclusion

**PASS at the full printed scope, with no repair required.** The
capacity-eight theorem holds throughout the entire closed region
`P,T<=5/16` and

`(1-P)^2+(1-T)^2+1-max(P,T)+1/4>=M^2`.

It includes the full 1/5 square and the asymmetric 1/20 by 5/16
rectangle in the actual common square frame. The optional channel
corollary correctly preserves the record junction at height 9/16 and
requires a genuine full torque-balanced long channel to identify the
actual common frame with the long-normal frame.

## Full geometric reconstruction

Four actual interior-disjoint square interiors at a common point
exhaust the full angle with four right-angle vertex sectors. Their
common frame and side lengths force an exact translated two-by-two
block centered at that point. A side-interior contribution would
have angle pi and is excluded by the same angle count.

The corner formula gives the strict actual center bound `|c|<91/60`.
Every further square's open incircle misses the open block, because
an open overlap cannot remain confined to its internal seams. If a
closed block point were within distance less than 1/2 of the center,
nearby block-interior points would lie in the incircle too. Thus the
closed block clearance is at least 1/2, with all contact endpoints
included.

A center outside both coordinate intervals has positive excesses
s,t with `s^2+t^2>=1/4` and `s+t>=1/2`. Its absolute coordinates
are at least `1-P+s` and `1-T+t`. Positivity of `1-P,1-T` gives
the asserted squared norm bound by

`(1-P)^2+(1-T)^2+min(1-P,1-T)+1/4`.

The regional hypothesis therefore contradicts the strict center
bound, even at equality in the regional inequality. A center inside
both closed intervals has no clearance. Every remaining center is
outside precisely one interval and lies beyond a corresponding
side-cap threshold `3/2` from the block center. Interval endpoint
equalities are included in the other closed interval, so the case
split loses no centers.

A cap at depth 89/60 has squared diameter at most `361/900<1`
and therefore contains at most one actual center. A cap at depth
19/16 splits into two transverse half-caps, each of squared diameter
at most `7189/7200<1`. Thus it contains at most two centers. Assigning
the transverse zero line to one half makes this a complete disjoint
split; strict center separation is not being assumed at that boundary.

For one block-coordinate magnitude d, the opposite cap thresholds
are `3/2+d` and `3/2-d`. If d<=1/60 both are at least 89/60 and
each cap has capacity one. If d>=1/60 the farther cap is empty by
the strict center bound, while d<=5/16 puts the nearer cap at depth
at least 19/16 and gives capacity two. At d=1/60 both descriptions
are valid. Thus the entire horizontal group contains at most two
completion centers, and the identical vertical argument gives two
more. All orientations of the additional units are retained because
only their physical incircles and centers were used.

## Boxes, channel join and retained witness

At P,T<=1/5, the regional expression is at least `233/100`, which
exceeds `M^2` by `107/3600`. In the asymmetric box it exceeds
`M^2` by at least `713/57600`. Both exact comparisons are correct
and both boxes obey the 5/16 coordinate bound. These are whole
closed boxes, not sampled points.

The imported frozen straight-line source proves that a genuine
two-internal unloaded true-degree-two force-and-torque channel has
both internal units side-normal and its actual middle mean at
`(s,t)` with `|s|<1/60`, `|t|<=9/16`. At a four-square junction
through that mean the four actual frames agree; thus the long-normal
coordinates are the required block-frame coordinates. If |t|<=5/16,
the asymmetric box applies, excluding a ninth unit. Consequently
the strict lower endpoint `5/16<|t|` and closed upper endpoint
`|t|<=9/16` are correctly retained. No transverse center alignment
or altered physical mean is used.

The stated nine-unit witness is valid. Four central/upper squares
centered at `(+-1/2,1/16),(+-1/2,17/16)` meet at `(0,9/16)`.
The two outer row units and three lower row units are interior
disjoint from these and one another. The four outer anchors attain
Q, while all other corners are inside. It confirms why capacity
eight cannot hold at every translated junction or every long-channel
middle junction.

## Exact audit

The source record and all printed rational identities were recomputed,
including the narrow half-cap reserve `11/7200`. The optional imported
channel SHA256 matches the already frozen source. The review did not
change any actual square, force, mean, mask, original case flag,
metadata, Lean file, CI state or publication.
