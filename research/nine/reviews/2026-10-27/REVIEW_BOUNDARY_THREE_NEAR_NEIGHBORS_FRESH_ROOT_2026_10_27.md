# Full root review: a boundary unit and three near-origin neighbors

Date: October 27, 2026.
Reviewer: root, independently of author triangle_bridges and reviewer hexagon.

**Root verdict: ACCEPTED in full.** I read the complete new source and
the complete separate independent review, recomputed the fixed-lens
geometry, and checked its literal original-component caller. The source is

    BOUNDARY_UNIT_THREE_NEAR_NEIGHBORS_FRESH_EXCLUSION.md
    ba49bbf678dfecdadbd120328de745253c8e5a45a5f7635d7044fc784179f156.

The separate complete review is

    REVIEW_BOUNDARY_THREE_NEAR_NEIGHBORS_FRESH_HEXAGON_2026_10_27.md
    8ae31e5cc651ab151a65df358fed675379801e1f514eda69a7d010e05771ca85.

This is a full mathematical audit of the current text. No conclusion
is reconstructed from an unavailable historical lens source.

## 1. The exact physical-center reduction

For a unit meeting the closed disk of radius 1/60, the actual center
has norm at most 1/sqrt(2)+1/60<29/40. For the actual circle-touching
unit, its center has norm at least R-1/sqrt(2)>63/50 throughout the
stated radius window. I checked the strict reserves 1/576 and 1/1400,
including the rational bound 1/sqrt(2)<5/7.

After a common rotation, the boundary center is (q,0), q>63/50.
Every near center has x<=29/40<63/50. Therefore its squared distance
to (q,0) increases strictly with q. Replacing q by 63/50 in the
necessary contact inequality enlarges the domain. A real common
contact point gives center distance at most sqrt(2), independently
of the orientations and contact features of both squares.

Thus all three putative near centers really lie in the displayed
fixed lens. Their mutual distances must be at least one, because
the open radius-1/2 incircles of distinct physical units are disjoint.
This reduction uses physical circle contact, not an assumed positive
weight at a chosen corner.

## 2. The entire closed half-lens has the claimed diameter

I derived x0=647/14400 and verified that both upper boundary arcs are
short arcs in the indicated first-quadrant parameter intervals. The
upper half-lens has exactly the two arcs and the axis segment as its
boundary. It is compact and convex.

For a fixed Q on the circle centered at (63/50,0), maximizing its
distance to a point of the origin-centered arc is equivalent to
minimizing Qx*cos(theta)+Qy*sin(theta). When Qx<=0 its derivative is
nonnegative; when Qx>=0 it is concave. In both cases an endpoint
suffices. For the resulting comparison with A, the other arc's
distance increases with its angle since b>a. The comparison with Z
is a chord on that same short arc. Same-arc pairs are likewise
bounded by the two endpoint chords.

Convexity of squared distance handles points on the axis segment and
then all interior points. This proves the maximum-of-three-distances
bound for the full curved half-lens. No inscribed triangle has been
substituted for the curved set.

The exact long chord squared is 1-4003/288000. The other chord is
strictly below one using b-x0>6/5 and sqrt(2)>5/4. The horizontal
chord is strictly below one using b-a>1/2 and sqrt(2)<3/2. The
strictness remains at every closed endpoint and arc intersection.

Reflection gives the same strict diameter bound for the lower half.
Three centers in their union must have two in the same half; an axis
center may be assigned to either half containing it. This contradicts
the actual center separation. The force-free theorem is complete and
needs no upper bound on R.

## 3. The whole original diamond caller has its real degrees

I reread NO_UNLOADED_DIAMOND_HUB.md in full, including its finite
pre-extraction normal selection, compatible junction matching,
arbitrary-neighbor-degree scope and subsequent uncrossing convention.
Its actual degree-three hub theorem applies to K: K has exactly
H,B,D as positive neighbors, and H physically touches B and D.
No fourth K force exists in this attachment. The theorem leaves
every H4, B3 and D3 force untouched and forces K to have positive
total circle load.

Each of H,B,D is the actual root of a genuine radial leaf. The
degree-free radial inward segment places a point of that root at O
when d<=1, or within the closed disk of radius epsilon<1/60 when
d>1. The D alternative contains O. These are facts about the actual
three distinct units, not artificially extracted lower-degree stars.

K is therefore a physical boundary unit touching three distinct units
meeting the small disk, exactly the force-free theorem's hypotheses.
This excludes the entire original hub-and-two-tips leaf attachment,
for all S/D choices, physical masks, zero individual weights, original
means and closed radius endpoints. The other two physical squares
remain in the same nine-square packing.

## 4. Verification and scope

The exact arithmetic in /tmp/pr11_root_b3_first_rationals.py was run
with standard-library Fractions; all 25 checks passed, including
every rational comparison used in this lens proof. Those checks only
verify displayed identities and bounds; the continuous geometric
argument above is the proof.

The source has now passed a full root review and a separate full
independent review. It closes one attachment of C1.4.b3, not its
remaining attachments or the whole coarse cell. This audit introduces
no new lemma or source correction. No force deletion, normal
reselection, numerical pose search, Lean compilation, CI or remote
mutation was used.

