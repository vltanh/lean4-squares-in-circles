# Clean review: the complete parallel-core unloaded triangle

Date: November 1, 2026 UTC. Reviewer: four_chain continuation.

**PASS for the entire stated parallel-core-frame feature.**

Reviewed the complete frozen source
`EVERY_PARALLEL_FRAME_UNLOADED_THREE_FORCE_TRIANGLE_REQUIRES_RADIUS_SQUARED_GREATER_THAN_NINE_HALVES_2026_11_01.md`,
SHA256
`75de6a35fc588897193bfdf473abf7f8a9aeb0946d98894bb0d7422c9a45f09b`.
The reviewer did not construct its contact chart, three-point arc
obstruction, endpoint force calculation or diameter argument. The whole
new proof is printed in the source and has been checked directly. No
mathematical correction or added hypothesis is needed.

## 1. Complete physical chart

For parallel unit frames, each physically touching pair with disjoint
open interiors has center-coordinate differences bounded in absolute
value by one, with equality in at least one coordinate. Thus all three
center pairs have L-infinity distance one and both coordinate ranges
are at most one. Among three pairwise witnesses, two use the same
coordinate and have a common center. Their other centers must have the
same coordinate; opposite signs would give total range two. Their other
coordinates differ by exactly one. This proves the printed closed T
chart after a rigid motion, reflection and relabeling of the actual units.

The remaining unit must touch both members of the adjacent pair, giving
exactly `-1<=s<=0`. The open interval and its two endpoints exhaust every
parallel-core contact feature, including coordinate-witness ties. No
ambient disk-center normalization is introduced: the proof keeps the
arbitrary actual center `(h,k)` throughout.

## 2. Original outside points and complete force stars

The actual unit-step assertion is correct for every support vertex and
every point of an own-axis support side, including the original side mean
and both endpoints. In the outside unit's own frame, adding a unit normal
to its minimum support application changes each nonzero coordinate
inward by at most one and leaves a zero coordinate unchanged. Every
resulting point is therefore in the same actual outside square.

On the entire open interval, all three internal intersections have
positive length and their normals are their unique common own axes.
The original complete translations yield outside force vectors
`(-(a+b),0)`, `(a,c)` and `(b,-c)` at A,B,C, respectively. All magnitudes
are positive; the last two vectors strictly expose `(1,1)` and `(1,-1)`.
The first exposes the whole side of first coordinate minus one, whose
original mean is retained. The three actual outside points therefore
have exactly the forms required by the arc obstruction. Outside normals
and frames are not assigned independently or replaced with parallel
frames.

## 3. Complete arc endpoint cover

Assuming `R<17/8`, the actual point of first coordinate minus two gives
`h<1/8`, whether or not `h+2` is positive. If `k>=1`, the lower arc point
has squared distance greater than `49/64+4=305/64`; the upper point gives
the reflected contradiction for `k<=-1`. Hence both coefficients in each
printed linear arc expression are strictly positive.

For a closed positive unit quadrant, `alpha+beta>=1`. Its linear
expression is at least the smaller coefficient, so an arbitrary actual
arc point has squared distance at least the minimum of the two endpoint
squared distances. Thus the same original disk contains at least one
upper endpoint and at least one lower endpoint. These are auxiliary
points proved to be in the disk; they are not falsely treated as changed
physical contacts.

All four combinations are checked. The two same-coordinate cases have
mean squared distances greater than `289/64` and `305/64`, respectively.
For the pair `(2,1),(1,-2)`, the first distance forces `(1-k)^2<1`, hence
`k>0`; the second then exceeds `305/64`. Reflection handles the other
mixed case. This proves `R>=17/8` for the entire closed arc family.
Consequently every open-chart force feature has
`R^2>=289/64>9/2`, with the required strict conclusion.

## 4. Both actual corner endpoints

At `s=0`, the retained strict common normal of the AC singleton has
components `(rho,-sigma)` with both strictly positive magnitudes. The
complete A and C translations have strict Northwest and Southeast
outside directions, respectively. Their actual core applications are
the fixed corners `(-1,1)` and `(1,-1)`. No equation at an outside body,
or shortened equation at B, is substituted.

The actual points in their outside units have coordinate separation
`(2+alpha+gamma,-2-beta-delta)`. Expanding its squared length gives the
printed expression. Each positive unit pair has component sum strictly
greater than one, and

    (alpha+gamma)^2+(beta+delta)^2
      =2+2(alpha gamma+beta delta)>2.

Their squared separation is therefore strictly greater than 18. The
actual disk diameter gives `R^2>9/2`. The other endpoint is exactly its
reflection with B and C exchanged. The strict singleton premise is used
at this precise step and is explicitly retained in the theorem; no
boundary normal is silently made strict.

## 5. Full scope and acceptance boundary

The strict bound `R^2>9/2` holds on the entire closed physical chart.
At the research upper bound the reserve is exactly
`9/2-1105/256=47/256>0`. This excludes the whole parallel-core-frame
feature of the remaining direct unloaded triangle, and any larger
original graph containing those three full unloaded stars.

Only the three core frames are parallel. The exterior squares keep their
arbitrary actual frames, loads, degrees, other contacts and circle data.
Repeated exterior identities do not affect any inequality because every
used point is still in its unchanged actual square and the same disk.
No torque equation, nine-body count or lower-radius premise is needed.

The acceptance does not extend the conclusion to nonparallel core frames,
the complete direct-triangle row, a coarse original parent or the full
nine-square theorem. Those limits are accurately stated in the source.

This was a hand review of the entire proof, including its finite exact
four-row cover. No mathematical script, angle sampling, numerical
optimization, generated certificate, Lean, build or CI was used. Only
document identity is checked mechanically. No proof body, original force
system, status ledger or remote branch was changed by the review.
