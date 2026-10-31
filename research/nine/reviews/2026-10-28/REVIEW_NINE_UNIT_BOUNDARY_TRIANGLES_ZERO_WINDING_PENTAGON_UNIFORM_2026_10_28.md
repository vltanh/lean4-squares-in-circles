# Independent review: nine-unit boundary triangles have zero origin winding

Date: October 28, 2026. Reviewer: pentagon_uniform.

**Verdict: PASS for the complete frozen source and its stated exact scope.**
No source edit is needed. This is a fresh full mathematical review of the
new theorem and its original D0235.L0134 caller, not an acceptance carried
over from a missing historical proof. No whole original graph/load family
is closed by the reviewed source.

## 1. Exact reviewed bytes and read scope

The reviewed source is
`NINE_UNIT_BOUNDARY_TRIANGLES_ZERO_ORIGIN_WINDING.md`, 13,202 bytes,
SHA-256
`cb5ec72a1199615b5f25293ef6280b6ad456ec94f0d7c495d275fc7be79c87aa`,
Git blob
`4200d9bc6aa5c989b510ecf528d12ea3336c1310`.

I read the complete frozen source and independently rederived every
displayed geometric bound, the actual-path homotopies, the zero-moment
endpoint, and all original torque signs. I also read all seven direct
inputs at their operative scopes. In particular, I read the full
quarter-disk source and its full cap-arc proof, Sections 1--3 of the
degree-free port-order source, the full new high-radius four-ring source,
the full boundary angular and moment sources, the full original hexagon
graph/load cover, and the full physical contact-stress source. I checked
the selected drawing and protected circle accesses in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, and reread the one-square corner-angle
proof in Section 1 of `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`.

The seven direct current pins all match their printed source table:

| Source | SHA-256 |
| --- | --- |
| CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md | cb114d31badedf6a11b2b2a87f33f043f39ed439ca2f3ddf2af6724b12f80bbc |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| ROOTED_HIGH_RADIUS_TWO_NEAR_BOUNDARY_FOUR_RING_EXCLUSION.md | f31c67f46c3d4318d67c887afbb4ee93997ac8e587c6d7f3d5a7bdc9fcb28b10 |

The additional transitive bytes inspected here are:

| Source | SHA-256 | Used scope |
| --- | --- | --- |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Complete Section 1 arc estimate underlying the closed quarter-distance endpoint |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Selected opposite-pair compatibility, physical routing, protected exterior circle accesses |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Section 1 one-square corner deviation only |

The two historical digests printed inside the boundary-moment source
are exactly the current angular-source bytes plus one LF and the current
endpoint-separation bytes plus one LF, respectively:
`2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449`
and
`6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708`.
I checked both byte identities directly. No absent historical theorem
or old review is needed for this new proof.

## 2. The full-nine strict center clearance is valid

The quarter-disk input excludes containment of the **closed** disk of
radius 1/4 by any one of the nine actual units. Its eight-other-unit
argument retains every physical completion unit, regardless of stress
support or circle load. At the weak distance endpoint, it correctly
uses total open-interior angular measure, without asserting a single
connected arc when an outer-face point splits that arc.

I checked the underlying cap-arc inequalities and the new equality case.
In particular, for the positive-nearest-corner outer-face calculation,
the derivative comparison factors as

    (A-B)[(A+B-1/4)^2+(A^2+B^2-1/16)(A+B+1)],

which stays nonnegative at distance exactly 1/4. The lower arc-length
comparison still has strict reserve (16-9 sqrt(2))/100. In the missing
interval case A=1/4, the removed point on x=5/4 has zero angular measure;
the remaining total measure is at least 2 asin(2/5)>pi/4. Thus eight
disjoint open-interior angular sets exceed a full turn even at every
closed-distance endpoint.

If a center has norm at most 1/4, both coordinates in its own actual
orthonormal frame have absolute value at most 1/4. Each of its closed
unit intervals then contains [-1/4,1/4], so the actual unit contains the
closed quarter-disk. This proves the reviewed strict conclusion

    |c|>1/4

for every one of the nine actual centers. It does not select a new frame
for the square and does not discard any of the eight other bodies.

For every boundary unit, the independent angular theorem supplies
|a|>5/4, angular shadow less than pi/3, and a touching-boundary minor
center gap less than 2pi/5. Every actual point p of such a unit has

    |p|>=R-sqrt(2)>11/20,

because the distance to any actual circle corner is at most sqrt(2),
and sqrt(2)<57/40. The strict constants hold throughout the complete
printed radius window, including both radius endpoints.

## 3. The bent-edge homotopy and center-triangle exclusion are complete

For an actual K--A contact with A boundary, let c,a be the actual
centers and let p be any point in the full original intersection.
If zero lay in conv(c,p,a), the coefficient of c would be positive:
the segment [p,a] lies in the origin-free convex boundary unit A.
The coefficient cannot be one because c is nonzero. Consequently a
nonzero q in [p,a] lies on the ray -c. The two actual points p,q of A
have angular separation less than pi/3. Therefore

    |p-c|^2
      >121/400+25/400+55/400
      =201/400>1/2.

This contradicts p in K, whose actual circumradius is 1/sqrt(2).
The entire filled triangle conv(c,p,a) therefore avoids O. Since it
is compact, its distance from O is strictly positive. Linear path
interpolation within this triangle, keeping c and a fixed, gives the
claimed homotopy of c--p--a to c--a. It changes no physical square or
original application. The proof includes all side-mean endpoints.

For a physical triangle K,A,B with A and B boundary, the cone on a,b
has angle gamma<2pi/5<pi. If O belonged to conv(c,a,b), then -c would
lie in that cone. At least one of a,b makes angle less than pi/5 with
-c. Since cos(pi/5)>4/5, the corresponding touching center pair would
have

    |z-c|^2>25/16+1/16+1/2=17/8>2,

contradicting its center-distance upper bound sqrt(2). This excludes
the **closed** center triangle, including zero barycentric coefficients
and degenerate triangles.

Every one of the three bent edges of the actual six-segment loop has a
boundary endpoint. Each can therefore be straightened by the proved
homotopy. The straight center triangle contracts in its convex hull
away from O. This proves winding zero for the original full contact
loop, not merely a center-picture diagnostic. Coincident applications,
repeated strands and degenerate loops cause no difficulty: all paths
and homotopies have positive origin clearance. A compatible small
Jordan routing inherits this same winding when its neighborhoods are
chosen below that clearance.

## 4. The positive and zero moment joins retain full true degrees

I checked the complete operative degree-free port-order theorem. Its
one-missing-interval case excludes the far-side support by h<=d and
orders every negative and positive feature. Its two-positive-interval
case covers both a>epsilon and the small-corner range. In the latter,
the actual full unit step along each support normal forces a prohibited
neighbor point in closed D_epsilon; the far-corner cap includes all axis
endpoints. The exact zero angular-change alternative consists only of
the same nearest point at both ports.

For a directed cycle whose original moments are all positive, each
unit consequently contributes nonnegative angular change from incoming
to outgoing application. All changes cannot vanish: at least three
distinct unit tangent sectors of angle at least pi/2 would have to lie
in the single nearest-point half-plane of angle pi. The total change is
therefore a positive multiple of 2pi. This argument has no degree-two
or equilibrium premise, so it applies to every original triangle in
the reviewed caller with all additional forces still present.

If the third unit K of a two-boundary triangle also avoided closed
D_epsilon, that theorem would give positive winding, contradicting
Section 3 above. The boundary units themselves avoid D_epsilon by
their pointwise norm bound. Thus the positive-moment implication really
forces K to meet the closed disk.

The separate zero-moment proof is also complete. For p=t e with t>0,
the outer unit gives t<=d from its center bound and halfwidth at least
1/2. The inner unit I has p as an actual maximum-e support point. If
one reflected own interval is [a,a+1] with a>0, then p=t e in this
interval forces the corresponding e component to be positive, hence
p's coordinate is exactly a+1. Thus a<=t-1<=d-1<=epsilon. If both
own intervals missed zero, both absolute coordinates of p would exceed
one, contradicting t<=d<61/60<sqrt(2). The other interval therefore
contains zero and I contains its actual point (a,0) in D_epsilon. The
case O in I is already included. A boundary unit cannot be I because
all its points have norm greater than 11/20; hence I is K. When d<=1,
the displayed inequality simply makes the origin-free case impossible.

No normal is reselected and no mean is replaced in either moment join.

## 5. Exact D0235.L0134 boundary order and torque table

The original hexagon cover retains rim 01,12,23,34,45,50 and chords
02,35, with precisely loads 0,1,3,4. Thus 1,4 have true degree two,
while 0,2,3,5 all have true degree three. The three remaining physical
units and all additional zero-weight physical contacts remain.

The rim is the actual occupied exterior face, not an arbitrary abstract
cycle. Its protected physical circle accesses give the cyclic order of
the four boundary corner accesses as 0,1,3,4, after choosing the actual
counterclockwise orientation. The center directions have that same
order: each physical circle corner is within pi/12 of its own center,
whereas every pair of boundary centers is more than pi/5 apart. These
disjoint center intervals prevent an order reversal when moving from
each selected corner to its center direction. The angular-neighbor
rule then makes 0->1 and 3->4 their counterclockwise minor traversals;
the reverse minor traversal would contain the other two boundary
center directions. This justifies the two positive initial moments.

Write m_01=x>0 and m_34=y>0. Every individual circle atom has zero
origin torque. Keeping all original equations gives the following full
table, in which r=m_23:

| Unit | Exact original origin-torque equation | Consequence |
| --- | --- | --- |
| 1 | -m_01+m_12=0 | m_12=x |
| 4 | -m_34+m_45=0 | m_45=y |
| 2 | -m_12-m_02+m_23=0 | m_02=r-x |
| 0 | m_01+m_02-m_50=0 | m_50=r |
| 3 | -m_23+m_34+m_35=0 | m_35=r-y |
| 5 | -m_45-m_35+m_50=0 | Consistent with all preceding equalities |

For r<x, triangle 0->1->2->0 has original moments x,x,x-r, all
strictly positive, so unit 2 meets D_epsilon. For r=x, the original
02 moment is zero and the closed zero-moment result gives the same
conclusion. The second triangle 3->4->5->3 gives the identical statement
for unit 5 when r<=y. These conclusions hold throughout the full radius
window. Neither unloaded degree-three body is ever treated as a
two-force transmitter.

## 6. The strict high-radius four-ring premise is exactly satisfied

The selected four-ring is 0--2--3--5--0. Its opposite boundary units
are 0 and 3, and its opposite candidate near units are 2 and 5. Every
displayed edge is an original positive rim or chord edge. Extra forces
at the four units are permitted by the complete geometric theorem.

I independently checked that theorem's full half-lens and center-order
proofs. For near centers of norm at most q=29/40, the origin-side
common-neighbor half-lens has squared radius at most
2881/1600<(27/20)^2. Its two-variable maximum really reduces to the
printed F_1,F_2 endpoints: the relevant functions are convex on their
entire closed intervals, and F_2 separately covers a on either side of
1/sqrt(2). In the strict high-radius interval every boundary center
has norm greater than 27/20. Thus two boundary common neighbors must
both be strictly on the side of the near-center line away from O.

The selected center-order proof retains exactly the positive-junction
compatibility of the original certificate. Any proper crossing of two
nonincident contact center edges would force the aligned 2-by-2 block
and both forbidden opposite junction pairs. The only nonstrict convex
four-ring endpoint is the aligned T configuration. In it the opposite
pair with distance less than two still has the other two centers
strictly on opposite sides of its line. For two units meeting closed
D_epsilon, the bound epsilon+1/sqrt(2)<29/40 makes that distance
strictly less than two. The half-lens and selected-order conclusions
therefore contradict each other, including every weak selected endpoint.

This input is used only for

    sqrt(17)/2<R<=sqrt(1105)/16.

If r<=min(x,y), both actual opposite units 2,5 meet closed D_epsilon,
so this precise four-ring contradiction applies. The surviving necessary
inequality is exactly

    r>min(x,y)>0.

The equality r=min(x,y), both individual zero-chord boundaries, all
physical masks and every original shared-side mean are included in the
excluded high-radius domain. The lower and critical radii are not
silently included in the four-ring application.

## 7. Accepted scope and limits of this review

The source proves a general full-nine physical zero-winding theorem for
every triangle with at least two boundary units, without a force or
degree premise. Its positive-moment and zero-moment consequences hold
for the full original contacts and true degrees. Its exact hexagon
caller excludes the entire high-radius moment domain r<=min(x,y).

It does not exclude the whole original M6.B6.HEXAGON.D0235.L0134 row.
The domain r>min(x,y), the lower/critical-radius continuation, and the
three-extra completion obligation remain open here. It introduces no
new original label and earns no whole fine or coarse closure credit.

Only source-byte hashing was automated. All geometric, continuous
inequality, topological and torque arguments above were checked by
hand. No Lean build, CI, pose sample, optimization, computational
exclusion, source alteration, metadata edit, commit or publication is
part of this review.
