# Fresh independent review of the restored strict common-hub-vertex theorem

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## Decision and exact source chain

**PASS for the entire stated common-strict-vertex feature, including
arbitrary actual hub degree and every physical V--W intersection.**
This is a fresh full review, not an exact-byte recovery of the lost
review fe7c9048bd98a9b9f87add11a9b4f7c0d7cd385318e4c2be7f304793a9865340.

| Source read in full | Exact SHA-256 |
| --- | --- |
| BOUNDARY_TWO_FORCE_TIP_NO_COMMON_STRICT_HUB_VERTEX.md | 5edbfff40e364317e83c4111ff3b0c3ed3cae102211d5fc869994e9659fceb70 |
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | 18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |

The imported coincident-port theorem has a separate fresh full PASS in
REVIEW_RESTORED_LOADED_COINCIDENT_PORT_STAR_PENTAGON_2026_10_28.md,
SHA-256
fff8eed21f20dca2d7c600303c1ca71002af23a2c668313fa6df84ecfe99714c.
That review also reads and checks all five direct sources of the
imported theorem.

The physical-stress source confirms the unchanged common application,
outward support and origin-torque conventions. The graph cover is
used literally for the listed positive edges, degrees and load sets.
No higher-degree body is substituted for the true loaded V2.

## 1. Full shared-side boundary lemma

I checked the entire independent lemma in Section 2. Rotation and a
possible reflection preserve the actual circle origin. Two unit squares
sharing a whole side have parallel frames and can therefore be written

    V=[a,a+1] times [b,b+1],
    W=[a,a+1] times [b-1,b].

Physical circle contact and containment make both farthest-corner
squared norms equal to R^2. Their common horizontal maximum cancels.
If b>0, the upper vertical endpoint has strictly larger absolute value
than either endpoint on W; if b<0, reflection gives the reverse strict
inequality. Thus equality forces b=0, without translating the origin.

For R>sqrt(2), the horizontal endpoint maximum is R^2-1>1.
The unit interval [a,a+1] cannot meet zero, because any unit interval
containing zero has both endpoints of absolute value at most one.
Consequently the UV endpoint coordinate p and every possible original
VW mean coordinate m have one same strict sign.

At a bottom corner of V, the actual U-to-V inward minimum-support
normal n satisfies n_y>=0. The two original pair forces in V's
unchanged torque equation contribute

    -mu*p*n_y-nu*m,

with mu,nu>0. All actual circle atoms have zero origin moment,
regardless of their coefficients. The expression is strictly negative
when p,m>0 and strictly positive when p,m<0. The unchanged VW term
makes this strict even if n_y=0.

This establishes the lemma for every endpoint normal, every original
VW mean including either endpoint, and every physical circle mask.
It does not need V's total circle coefficient to be positive and uses
no equation at W. Its radius hypothesis is weaker than the main
theorem's R>3/2.

## 2. Exhaustive tangent and intersection cover

The two strict nonaxis U normals uniquely expose the same actual U
vertex P. Hence both original applications are P and all of U,V,W
contain P. Since V and W are convex and have disjoint open interiors,
their intersection is a point or a segment.

If it is the singleton P, the true loaded V2 has both original pair
applications at P. Its actual neighbor W is physically boundary.
Every premise of the imported coincident-port theorem holds exactly,
so this entire case is excluded without a selector.

For a positive-length intersection, its line lies in sides of both
squares; consequently their square frames are parallel. If P lay
in the relative interior of the shared interval, it would be in the
relative interior of both sides. Their opposite open half-plane
tangent sectors leave no two-dimensional sector for the actual U.
Thus P is an endpoint of the intersection.

At such an endpoint there are only two remaining types.

* If one of V,W has a vertex at P and the other has a side-interior
  point there, their tangent sectors are one quadrant and the
  opposite half-plane. The available complement is precisely one
  closed quadrant. The actual U has a vertex at P and needs a
  right-angle tangent sector, so its axes must be parallel to those
  of V,W. The original separating normal toward the side-interior
  neighbor is uniquely perpendicular to that side. It is therefore
  an own axis of U, contradicting the strict nonaxis hypothesis.
* If both V,W have vertices at P, the common length-one side
  intervals start at P and extend in the same direction, since their
  intersection has positive length. They coincide for the entire
  unit side. The full shared-side lemma just proved applies.

The first type includes both choices of the side-interior neighbor.
If both neighbors had side-interior points, P would already be in
the relative interior of the intersection, the excluded preceding
case. Hence this cover contains every positive-length shared contact,
including partial overlaps and every unchanged mean on them.

The local origin chosen only to describe tangent sectors never enters
the circle calculation. The metric full-side lemma keeps the actual
circle origin throughout.

## 3. Every literal graph and load join

I reconstructed the real degrees directly from the six cycle edges
and the indicated chords. The following checks cover all twelve
rows in the manuscript's interface table.

| Chords and loaded sets | Actual (U,V,W) | Degrees (U,V,W) |
| --- | --- | --- |
| 02; 014,0134,0135,0145,01345 | (2,1,0) | (3,2,3) |
| 02,03; 124,1234,1235,1245 | (0,1,2) | (4,2,3) |
| 02,04; 0135 | (2,1,0) | (3,2,4) |
| 02,04; 0135 | (4,5,0) | (3,2,4) |
| 02,04; 1235,1245 | (0,1,2) | (4,2,3) |
| 02,04; 1245 | (0,5,4) | (4,2,3) |
| 02,35; 0134 | (2,1,0) | (3,2,3) |
| 02,35; 0134 | (5,4,3) | (3,2,3) |
| 02,03,35; 1245 | (0,1,2) | (4,2,3) |
| 02,03,35; 1245 | (3,4,5) | (4,2,3) |
| 02,04,24; 0135 | (2,1,0) | (4,2,4) |
| 02,04,24; 0135 | (4,5,0) | (4,2,4) |

In each row, V's entire positive pair neighborhood is exactly {U,W},
both V and W occur in the displayed positive load set, and the
UW edge is an actual stated chord or cycle edge. Thus the required
physical boundary status of W is available in every case. No omitted
positive load is promoted to physical boundary status.

In particular, the D0203, chord-path and central-triangle hub
applications have real degree four. The local theorem never uses an
equation at U, so these are valid applications at their full degrees.
The degrees and extra forces at W are likewise untouched.

The table deliberately does not cover other load rows merely by
analogy. For example a single-chord row with W=0 unloaded would need
separate proof that 0 physically touches the circle. The theorem
requires that premise and does not infer it from another mask.

## 4. Scope and preservation

The main proof uses only the complete true V2 system, the actual
physical boundary status of W, and the specified actual strict
U-vertex feature. U can be loaded or unloaded and can have arbitrary
other incident positive forces. UW itself need not have a positive
coefficient in the local statement. Every original caller listed
does have that physical edge.

All normal owners on V and W, all original means, every physical
circle mask, individual zero coefficients and all arbitrary completion
squares remain. The shared-side cases are proved explicitly; they are
not reduced to a singleton by choosing a different mean.

This excludes one whole feature across the stated original rows.
It does not exclude adjacent distinct U vertices, own-axis U normals
or an entire original graph/load row. No fine/coarse gate credit is
assigned by this review.

No Lean compilation, CI, numerical search, sampled parameter argument,
fake leaf or force deletion was used.

