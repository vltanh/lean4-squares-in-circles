# Independent review of the all-owner loaded-tip common-application exclusion

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## Decision and complete source scope

**PASS for the whole stated theorem, including the closed threshold
R^2>=13/4, every original mean and all physical circle masks.**
No repair to the reviewed source is required.

| Source read in full | Exact SHA-256 |
| --- | --- |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba |
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | 18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83 |
| BOUNDARY_TWO_FORCE_TIP_NO_COMMON_STRICT_HUB_VERTEX.md | 5edbfff40e364317e83c4111ff3b0c3ed3cae102211d5fc869994e9659fceb70 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b |

The two imported local geometric inputs also have fresh separate
independent full reviews:

| Review | SHA-256 |
| --- | --- |
| REVIEW_RESTORED_LOADED_COINCIDENT_PORT_STAR_PENTAGON_2026_10_28.md | fff8eed21f20dca2d7c600303c1ca71002af23a2c668313fa6df84ecfe99714c |
| REVIEW_RESTORED_BOUNDARY_TIP_COMMON_STRICT_HUB_VERTEX_PENTAGON_2026_10_28.md | d4e6a48ab776043418ba5aefc3ba340503e318300c7ee6bc254cb7079c87ba63 |

The source's actual theorem is that the unchanged original UV
application P does not belong to W. Its premises are the true
positively loaded V2 with complete pair neighborhood {U,W},
physical boundary status of W, three actual interior-disjoint units
in the same disk, and R^2>=13/4. I checked this full domain,
not merely a strict-hub-vertex subdomain.

## 1. Complete intersection and tangent-sector cover

Assuming P belongs to W makes it an actual common point of U,V,W.
The physical-stress contract ensures that a shared-side mean is a
point of the actual original intersection, so this statement is valid
for variable means as well as singleton applications.

The V--W intersection is a singleton or a segment. In the singleton
case it is {P}, and the original VW application must also equal P.
The loaded coincident-port theorem applies with physical boundary W.
The new radius hypothesis implies R>3/2 strictly, so its radius
premise holds at the new closed endpoint too.

A positive-length intersection lies on actual sides of both squares,
forcing parallel frames. If P is in the interval's relative interior,
both local sectors are opposite half-planes. No two-dimensional
tangent sector of an actual U can avoid them. Thus P is an endpoint.

At least one of V,W has a vertex there. If both do, the two unit
side intervals begin at the same point and extend in the same direction,
so they coincide for their whole length. The imported full-shared-side
boundary lemma applies directly. That lemma uses no strict-hub
premise; it requires only true V2, both physical boundary units,
the original UV endpoint and unchanged VW mean. Its weaker radius
condition R>sqrt(2) also follows strictly.

The two remaining possibilities are exactly the two partial-side
cases proved in the new source. There is no omitted case in which
both units have side-interior points at an intersection endpoint:
then that point would be in the relative interior of the intersection.

## 2. Vertex of V, relative side interior of W

With the circle origin unchanged, the stated rotation/reflection
gives

    V=[a,a+1] x [b,b+1],
    W=[c,c+1] x [b-1,b],
    a-1<c<a, P=(a,b).

At P, V occupies the upper-right quadrant and W the lower open
half-plane. The available tangent sector for U is exactly the
upper-left quadrant. A square has angle at least pi/2 at any
boundary point, so U must have a vertex there, fill that quadrant,
and have the parallel frame. Its complete unit geometry is therefore
[a-1,a] x [b,b+1].

The UV intersection is then a whole vertical side, while VW has
the actual shared horizontal interval [a,c+1] at height b.
Thus the original V normals are exactly West and South, even if
their retained means are endpoints. They are consequences of the
physical sides, not newly chosen normals.

The full resultant is (mu,nu) with both entries positive. If
a<-1/2, every actual farthest V corner has horizontal coordinate
a<0, and every positively weighted radial resultant has negative
horizontal component. The same argument applies to b. Hence the
weak bounds a,b>=-1/2 are necessary and sufficient for the
farthest-corner formula used in the proof:

    R^2=(a+1)^2+(b+1)^2.

The equality coordinate cases are retained. This formula does not
assume that the physical circle corner or its force coefficient is
unique.

The original UV application is the specified P=(a,b). Its torque
contribution is mu*b. The original VW mean is (m,b), with
a<=m<=c+1; its contribution is -nu*m. All circle atoms have
zero origin moment, so the full torque is exactly

    mu*b=nu*m.

If b<=0, then m<=0 and a<=0. Together with a,b>=-1/2,
the actual radius formula would imply R^2<=2. This contradicts
the new threshold. Thus b>0, without division by any individual
circle coefficient.

For a>=0, the entire W horizontal interval lies strictly between
-(a+1) and a+1: its left endpoint is greater than a-1>=-a-1,
and its right endpoint is below a+1. Its vertical interval likewise
lies strictly between -(b+1) and b+1 because b>0. Hence every
actual W corner is strictly inside the disk.

For -1/2<=a<0, the actual radius threshold gives

    (b+1)^2=R^2-(a+1)^2>13/4-1=9/4,

so b>1/2. The strict inequality remains valid when R^2=13/4,
because a<0 makes (a+1)^2<1. The W horizontal absolute values
are strictly below 1-a, and its vertical absolute values are at
most b. Finally

    R^2-((1-a)^2+b^2)=4a+2b+1>0,

including a=-1/2. Thus all W is again strictly inside the circle.
This proves the entire first partial case with every original mean
and physical V mask retained.

## 3. Relative side interior of V, vertex of W

The second global chart is

    V=[a,a+1] x [b,b+1],
    W=[c,c+1] x [b-1,b],
    a<c<a+1, P=(c,b).

Here V occupies the upper half-plane at P and W the lower-right
quadrant. The remaining actual U must fill the lower-left quadrant,
so U=[c-1,c] x [b-1,b].

Both original positive V forces are therefore South. The actual
circle resultant is a nonzero North vector. A nonzero horizontal
center coordinate would make every physical farthest-corner
horizontal coordinate have one same strict sign, contradicting that
resultant. Hence a=-1/2.

A negative vertical center is similarly impossible. If both center
coordinates were zero, the actual farthest radius would be sqrt(1/2),
contrary to the threshold. Thus b+1/2>0, and physical boundary
contact fixes

    b=d=sqrt(R^2-1/4)-1>=sqrt(3)-1>1/2.

The entire physical two-corner mask is retained. The zero horizontal
resultant uses its actual nonnegative coefficients; positive total
load implies the needed nonzero North direction. The argument has
not replaced V by a leaf or discarded one of its pair forces.

Now -1/2<c<1/2, so every W horizontal absolute coordinate is
strictly below 3/2. Its vertical interval [d-1,d] has maximum
absolute value d because d>1/2. Consequently

    max_W |z|^2<9/4+d^2<R^2,

with the second strict inequality exactly 2d>1. This holds at
R^2=13/4 as well. No particular VW mean or torque relation is
needed for this case.

## 4. Full original graph joins

The graph-cover source gives the same twelve actual triangle
interfaces checked in the earlier strict-vertex source. Every such
row has a genuine loaded V2 and physical boundary W. The new
theorem does not use an equation at U, so its real degree three
or four and all its other forces remain. Its conclusion applies
to any coincident original UV/UW application, including own-axis
and shared-side possibilities previously outside the strict
feature.

For the lower house, the actual edges are

    AT, DT, AD, AB, BC, CD,

with the genuine leaf attached at B. In the TDC load family,
T and D are positively circle-loaded. The literal substitution

    U=A, V=T, W=D

therefore has real degrees A3,T2,D3 and exactly the required
T pair neighborhood {A,D}. An original coincidence of AT and
AD would put the unchanged AT application in D, forbidden by
the theorem. This works for either S or D leaf, with no root
orientation, near-port or A-owner assumption.

The whole original radius window meets the threshold, since

    (79/40)^2-13/4=1041/1600>0.

All these joins preserve the remaining units, full physical masks,
extra zero-weight contacts and original side means.

## 5. Exact conclusion and limits

Every actual V--W intersection possibility has been excluded when
the original UV application lies in W. This proves the stated
stronger conclusion, and therefore distinctness of the corresponding
two original hub applications.

It does not forbid an unrelated physical triple junction elsewhere
on an original UV shared segment when its retained mean is different.
It also does not turn a variable shared mean into a fixed physical
singleton or satisfy a selector's additional fixed-point premise.

The proof uses the full true V2 equations where needed. No equation
at U or W is shortened or required. The radius threshold is a
proved sufficient condition and is not claimed optimal.

This is one uniform all-owner feature exclusion across the stated
original callers. No whole original graph/load family or coarse
gate is closed solely by this review. No Lean compilation, CI,
numerical pose, mesh, computational exclusion certificate, force
deletion, changed mean or normal reselection was used.

