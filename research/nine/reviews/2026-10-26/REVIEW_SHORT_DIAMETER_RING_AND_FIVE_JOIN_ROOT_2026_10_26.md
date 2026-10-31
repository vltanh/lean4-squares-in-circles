# Root review: general short-diameter contact rings and the full five-load join

Date: October 26, 2026.

**Result: PASS for the complete geometric transfer and its stated original
five-load consequences.** I independently read and checked both new sources:

* SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md;
* SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md.

Their mathematical-source SHA-256 values before status-only acceptance
updates are respectively
`2a2687425dabaa6d55f1f6dfd47dd8052b79b2ab606687b9a05400b864c4cf4c` and
`945c4654e23507d95eb0614fbf188e266a6ed4dc9ae4a759e8f22f14a8ad1201`.
The author did not perform this review.

## 1. The exact new geometric scope

The ring theorem assumes actual pairwise interior-disjoint unit squares
inside the fixed disk of squared radius at most Q=1105/256, actual cyclic
contact points, strict diameter below three for all their centers, and
nonzero winding about every point of each proposed whole extra interior.
It does not assume that the center chain is convex or simple, that any
ring square touches the circle, or that a ring body carries positive load.
It has no lower-radius or body-count premise.

The stated weak-junction alternative is sufficient: each compact subset
of an extra interior has positive distance from the limiting contact
curve, because that curve lies in the closed ring units. Winding is
stable under sufficiently small physical Jordan routings. This applies
separately to every proposed extra, including extras in different free
components of the same bounded region. It is not an area count of just
one favorable face.

The entire enclosed unit automatically lies in the containing disk if
needed: nonzero winding places its interior in the convex hull of the
contact curve, which lies in that convex disk. More importantly, all
later actual witness units are the original contained ring units.

## 2. The center-chain replacement is valid without convexity

I read the entire C7_CENTER_POLYGON_LOCALIZATION.md and separated its
uses precisely. Its Section 1 convexity argument uses seven boundary
bodies and is not transferred. Its Section 2 clear-endpoint chord lemma
is a two-endpoint statement about one arbitrary unit square; it needs
neither a polygon nor boundary-circle contact.

For a proposed enclosed unit T, every actual ring center has distance
at least one half from T, by its physical open incircle and nonoverlap.
Every consecutive center edge has length at most sqrt(2), through its
unchanged actual common contact. The chord lemma therefore excludes
that edge from int(T), including the length-equality endpoint.

Each contact-spoke-to-center-edge replacement has a triangular boundary
disjoint from the connected set int(T). That set is either entirely
inside or entirely outside a nondegenerate triangle. The first case
would place its full area one in area at most one quarter, impossible.
Degenerate triangles contribute zero winding directly. Every replacement
thus has winding zero about T, so the actual center chain retains the
nonzero winding of the physical contact loop.

No edge of a convex hull is substituted for an actual center edge. In
particular, no unproved short-edge bound for such a hull is introduced.

The same winding argument supplies each required outward-ray witness.
A ray starting inside the extra must meet the occupied ring before its
winding can become zero at infinity. The corner-diagonal uses also start
at an interior point of the same unit before reaching its outgoing tail.
Thus the imported local ray proofs retain actual physical witnesses.

## 3. Full audit of the new missing-zone extraction

I checked the general left-zone argument against all endpoint and edge
possibilities. In local coordinates T=[-1,0] x [-1/2,1/2], if no center
belongs to x<=-3/2, |y|<=1/2, a leftward ray from T's center must meet
the actual center chain at x<=-1. The intersection cannot be a center
vertex by clearance and the missing-zone premise. A horizontal overlap
would likewise require a prohibited endpoint on that ray.

There is consequently an interior intersection with one endpoint above
and one below. At least one endpoint is at x<=-1; reflection makes it the
lower endpoint B. Clearance and the missing-zone premise force B_y<-1/2.
If the upper endpoint has -1<=x<=0, clearance forces y>=1, giving an
edge longer than 3/2. If it has x>=0 and y<=1/2, clearance forces x>=1/2,
again giving span at least 3/2. If x>=0 and y>1/2, the horizontal span
is at least one and the vertical span exceeds one, giving length greater
than sqrt(2). Equality at x=-1 is excluded by the same vertical argument.
Applying the reflected argument excludes equality for the lower endpoint
as well.

Thus both endpoints have precisely the stated corner-zone forms, with
u,w,v,z>0, u^2+v^2>=1/4, w^2+z^2>=1/4, and v+z<=sqrt(2)-1<1/2.
In particular u,w>1/4. This supplies the exact data used in the original
parallel and nonparallel far-face arguments. The proof needs winding,
clearance, and actual short edges; it needs no convexity.

## 4. Parallel pairs and the far-face theorem

I read the full PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md. Only its
initial ray-to-edge existence used convex polygon containment. The new
missing-zone extraction supplies precisely that premise with actual
ring centers. The remaining proof covers arbitrary gap and stagger:
two occupied outer middle zones give diameter at least three; one empty
zone gives a cross-distance strictly greater than three using the full
corner data; two empty zones give a cross diagonal with square greater
than 91/10. No common position or touching assumption on the two parallel
extras is introduced.

I also read the full C7_INNER_PAIR_FAR_FACE_CENTERS.md. Its sole polygon
use is that same missing-zone extraction. The rest uses actual center
norms below M=91/60 and own coordinates below k=3721/7200. In the empty
outward zone, the mean squared norm has the lower bound F_X(V) stated in
the new source. It increases in X and is concave in V, so its two endpoint
comparisons cover the entire interval. The exact positive endpoint
reserves are 47/900 and 497/90000 above M^2.

The original owned SAT separator gives both outward main coordinates
greater than 9/20. The obtained centers are actual distinct ring centers.
Their horizontal-gap identity and the actual strict diameter below three
give r>1/2-(3/2)tan(theta/2). Neither a perimeter estimate nor a radius-3/2
cover is being inferred from the diameter.

## 5. Full scope audit of both continuous nonparallel branches

I read all relevant mathematical sections of CENTER_COVER_PIERCING.md,
C7_INNER_SIDE_CORNER_RESTRICTIONS.md,
C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md,
C7_SHARP_BALANCED_RADIAL_TAIL.md,
C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md, and
C7_LEFT_OUTSIDE_INNER_EXCLUSION.md. I checked the scalar estimate from
C7_OUTSIDE_INNER_RAY_WITNESS.md at its used domain as well.

The side/corner and outside-face sources already state finite physical
ring hypotheses. Their proofs require actual outgoing witnesses and
the center norm bound, now supplied without convexity. They give the
complete own-coordinate, corner-distance, and relative-angle bounds.
The balanced radial-tail theorem is explicitly a local statement about
two arbitrary actual disjoint units and their ray encounter.

The right and left branch sources initially refer to C7 hypotheses, so
their full proofs, rather than just their theorem names, require the
scope audit. Every actual use is accounted for:

| Used input | Present source in the generalized domain |
| --- | --- |
| Own center coordinates and inner vertex bound | The unchanged local ray and corner lemmas |
| sin(theta)<4/15 | The unchanged whole outside-face/corner proof |
| Actual outward far-face center and its tangential inequality | The new nonconvex missing-zone extraction and strict actual diameter |
| Ring center norms<M | Whole physical unit containment in D_(sqrt(Q)) |
| Distinct ring center distances>=1 | Actual disjoint open radius-half incircles |
| Outgoing ray encounters | Nonzero winding about each whole extra interior |
| Witness near-radial frame | Its actual corner inequality rho^2+rho(cos(psi)+sin(psi))+1/2<=Q |
| Exclusion by an outside witness corner | Every corner of that actual ring square lies in D_(sqrt(Q)) |

No line of those proofs needs a witness to touch the circle. In particular
the difficult left-branch upper-owned alternative finds an actual corner
with squared norm greater than Q; it uses containment, never a circle
equality or a positive circle multiplier.

The two branch joins are exhaustive with the original SAT owner retained.
Both secondary own coordinates have magnitude below one half. Hence the
separator forces either xi>=1/2, or xi<1/2 and alpha>1/2. In the former,
the same physical ray witness is identified with the far-face square by
the small center cap and center separation at least one. The final lower
minus upper function is concave and has endpoint values 4109/5581500 and
136499/2232600, both positive. In the latter, the mixed-down witness is
identified by the strict squared-distance bound 11509/14400<1; all other
owners use the small cap. The complete parameter interval 0<d<e is then
excluded by the upper-minus-lower bound -197/72000<0.

I independently recomputed these displayed rational comparisons. They
are the same continuous inequalities and fixed endpoint comparisons as
the accepted original proofs. This transfer introduces no new coefficient
packet or parameter grid.

## 6. Entire original FIVE physical join

The join retains the actual bare component U-S1-S2-S3-S4-S5-U, all five
positive loads, the original unloaded degree-two U, and all three extras.
I checked its references to the actual cyclic order, full channel-pocket
routing, and whole central-union area bound. The area argument first
forces at least one actual cap extra; it does not assume the new central
capacity. That extra supplies the premise of the separately reviewed
occupied-channel transmitter estimate.

All fifteen center pairs then have strict distance below three: five
U/Si radius sums; seven one- or two-contact boundary pairs; two actual
three-edge boundary paths; and the remaining S1/S5 pair via the actual
two-contact path through U. The new ring theorem therefore applies to
every central extra with the established weak-junction winding convention.
It gives central capacity one, and the complete allocation list is exactly
(central,cap)=(0,3) or (1,2).

I read the complete RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md for the
final consequence. Its statement permits any simple positive cycle with
at least three loaded bodies, one actual side-normal transmitter, and
at least one physical two-circle-corner endpoint. Five loaded bodies
meet that original scope. Its proof retains individual zero radial-corner
weights and every side mean. Its cap capacity one, combined with central
capacity one, contradicts three extras. The other three loaded bodies
have unrestricted original physical masks.

Both radial endpoints give the separately established stronger empty-cap
conclusion. No diagonal-width mask is removed by the width-one theorem.
The cited diagonal restriction R^2<17/4 is correctly retained as compatible
with the same-nine lower bound R>2, not treated as an exclusion.

## 7. Accepted conclusion and limits

The general physical ring capacity-one theorem passes in its full stated
scope. The FIVE central-capacity-one join and the entire side-channel
family with at least one physical radial endpoint also pass. Both original
remaining allocations are retained for unique/unique side channels and
for all diagonal masks not independently excluded.

The entire original FIVE and FIVE.CAP gates remain open. No new gate,
whole coarse-cell closure, global sharp-radius claim, or equality claim
follows solely from these sources. No Lean compilation or CI was run.
