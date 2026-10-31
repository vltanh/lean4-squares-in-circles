# Full review: the exact eight-unit cross and its seven-atom alternative

**Date:** October 30, 2026 UTC. **Reviewer:** block-ears agent.
**Result:** PASS for both frozen sources. No repair requested.

## Sources read in full

1. `EXACT_EIGHT_BODY_OUTER_FACE_CYCLE_WITH_UNLOADED_BRANCHING_VERTICES_2026_10_30.md`, 8,261 bytes, SHA256 `d04ce78b5bb4656accbef54b0d19cbb94d5480b6e407d697399c0763a9632a4e`.
2. `SEVEN_ATOM_COMPATIBLE_ALTERNATIVE_FOR_THE_EIGHT_UNIT_CROSS_2026_10_30.md`, 6,414 bytes, SHA256 `9fb69f52ce84f5acc2b39499eab380eb04419387b9920e935db4bcce42217f29`.

I independently reconstructed the full coordinate geometry, all per-body
force and moment equations, the actual compatible drawings, the no-ninth
capacity proof, the endpoint-atom representation, and the fixed-aggregate
uniqueness argument. This review does not treat either eight-body example
as a nine-body counterexample or as a global support-minimality theorem.

## 1. Exact cross geometry and complete stress

The four central units tile `[-1,1]^2`. The four outer units centered at
`(±3/2,0),(0,±3/2)` are interior-disjoint from it and from one another.
For every distinct pair of the eight centers, at least one own coordinate
difference is at least one. All frames are parallel, so this is the exact
nonoverlap condition needed here.

The central units have maximum squared corner radius two. Each outer
unit has exactly two circle corners at squared radius `17/4`, and every
other corner has smaller radius. The radius lies strictly above the
lower research endpoint, since `17/4-(79/40)^2=559/1600`, and below Q by
`17/256`.

Each of the twelve positive pair means is the midpoint of its actual
shared segment and also of its two body centers. The first eight segments
have length one half, while the central four have length one. The listed
normals are actual common supporting normals. All other actual contacts,
including the two opposite central pairs at the origin, are retained
geometrically with zero selected force.

At E, the two `lambda=1/8` circle terms give `(1,0)` under the factor-two
convention, and the two `mu=1/2` contact terms give `(-1,0)`. Their origin
moments are `1/8` and `-1/8`. At NE, the four contact forces are the two
opposite horizontal and two opposite vertical half-unit vectors. The
origin moments are `-1/8,1/8,1/4,-1/4`, so both complete equations vanish.
Quarter-turn symmetry supplies the other six body equations without
changing any means or weights. Radial circle forces have zero origin
moment individually. Zero full force converts zero origin moment to
zero center moment. The eight circle coefficients sum to one.

## 2. The outer-face cycle and the completion bound

All center-to-mean strands are actual straight center edges. Their
interiors are disjoint. The cycle
`E--NE--N--NW--W--SW--S--SE--E` is their actual outer boundary, and the
central C4 is drawn inside it. The graph is biconnected because the
spanning C8 remains connected after deletion of any vertex. The four
central vertices have true degree four and are physically circle-clear;
the four outer vertices have true degree two and positive circle load.

Consequently this is a valid obstruction to an unconditional seven-body
outer-face bound for arbitrary compatible force-and-torque certificates.
It does not violate the genuine full-degree hypothesis in the occupied-
arc/channel theorem: that hypothesis fails at all four central vertices.

For the no-ninth claim, the actual center bound is `|c|<91/60`, with the
stated strict excess `31/57600` over Q. An additional unit's open incircle
must avoid the open central block, so its center has distance at least
one half from that block. If both center coordinates lie outside
`[-1,1]`, write their excesses as positive s,t. Then
`s^2+t^2>=1/4` and `s+t>=1/2`, giving `|c|^2>=13/4>M^2`.
If both coordinates lie in those intervals the distance is zero. Thus
exactly one coordinate is beyond the interval, and its magnitude is at
least `3/2`. This puts the center in one of four disjoint caps.

For each cap, the rectangular coordinate-range diameter estimate is
exactly
`(M-3/2)^2+4(M^2-9/4)=29/144<1`.
Distinct physical unit centers have distance at least one. The four
original outer centers already occupy the four caps, so no additional
unit of any orientation fits, even at Q. This argument preserves the
whole central block and all four outer squares.

## 3. The explicit seven-atom certificate

The alternative uses four actual E/W circle corners with coefficient
`1/4` and three actual shared-side endpoint atoms with magnitude two.
All three contact points lie on `y=0` and all three normals are
horizontal. At E and W the circle resultants have magnitude two and
cancel the unique selected contact force. NE and NW each have equal
opposite contact forces. Every other physical body has a zero full
selected equation. All contact and circle forces have zero origin
moment individually, and the total circle coefficient is one.

The actual route alternates centers and original endpoint applications
with strictly decreasing x-coordinate. It is simple. The mean at the
central four-square junction joins only the adjacent NE/NW sectors, so
there is no hidden crossing or invalid junction routing. All eight
physical squares remain present, including the four zero-stress bodies.

The original midpoint certificate has twenty aggregated positive terms.
Its stated endpoint representation has twenty-four contact atoms plus
eight circle atoms. The new three contact atoms and four circle atoms
are all in that fixed thirty-two-atom family. Their exact reweighting is
therefore a literal sub-support certificate, not a claim based on an
unperformed sparse optimization.

## 4. Fixed-mean uniqueness and the selection distinction

At NE in the original aggregate family, full force equates the two
horizontal magnitudes, say alpha, and the two vertical magnitudes, say
beta. Its complete moment equation is `(alpha-beta)/4=0`. Hence all four
incident magnitudes agree. Repeating at the other central bodies and
using the connected central C4 forces all twelve pair magnitudes to one
common mu, including all attached outer pairs. At an outer body,
tangential force balance equates the two circle coefficients; radial
balance gives `lambda=mu/4`. Normalization then gives precisely
`mu=1/2,lambda=1/8`. No alternative normalized stress exists in that
fixed twenty-vector aggregate family.

Keeping only the three path edges at their old mean heights instead
would give a nonzero NE moment `mu/4`. The new endpoint means are
therefore a substantive permitted change of atom support, which the
companion states explicitly. Fixed-aggregate uniqueness does not
contradict the sparser endpoint-atom certificate.

The companion correctly leaves global minimum support and the common-
selection gate open. The exact cross proves a limitation of arbitrary
compatible stress arguments; its sparse alternative shows why that
limitation cannot be transferred automatically to a deliberately
reselected physical certificate. All mathematical and scope statements
in both frozen sources pass this full review.

