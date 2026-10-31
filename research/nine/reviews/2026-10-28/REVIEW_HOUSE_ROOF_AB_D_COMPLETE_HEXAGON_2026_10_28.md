# Independent full review of the house-roof AB diagonal-leaf exclusion

Date: October 28, 2026. Reviewer: hexagon.

**Verdict: ACCEPTED, with no correction requested.** This is a full
independent mathematical and original-domain review, not a review of
an abstract or an inherited acceptance. The reviewed manuscript is

`HOUSE_ROOF_AB_D_COMPLETE_EXCLUSION.md`

SHA-256:
`7b0bd9ee78d84e5d68424034729d55187fa44ea10035f56a57bd1c5fa75dc119`.

I read the entire frozen manuscript and the substantive original
inputs listed below. I independently rederived its complete force
cover, physical support inequalities, endpoint handling, and exact
radius comparisons. I did not use the other independent review as
a substitute for these derivations. The source is unchanged.

## 1. Original family, degrees, and permissible imports

The original roof family has block edges

    AT, DT, AD, AB, BC, CD

and the genuine diagonal leaf edge TL. Its positive block load set
is exactly AB. Reading the original five-body load cover confirms
the literal stars

| Body | Complete positive neighbors | Actual role |
| --- | --- | --- |
| T | A,D,L | Unloaded genuine root of degree three |
| A | T,D,B | Loaded degree three |
| D | T,A,C | Unloaded degree three |
| B | A,C | Loaded degree two |
| C | B,D | Unloaded degree two |
| L | T | Genuine loaded diagonal leaf |

The proof neither applies a two-force equation to A or D nor deletes
the roof's leaf. The actual circle status at A follows from its
positive load. The force equations at A and B are never replaced or
used as smaller stars. The three other packing units remain present.
All actual circle masks and individual zero corner weights are
therefore retained without requiring a mask-dependent case split.

The reflection fixing the roof exchanges A with D and B with C.
It takes the original AB representative to DC, as claimed. It does
not identify this family with AC or with any other roof load orbit.

I checked the source bytes of all seven printed direct inputs:

| Input | SHA-256 |
| --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 |
| UNIT_BYPASS_NORMAL_CHANNEL.md | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 |
| CHORDED_HEXAGON_SIDE_TRANSMITTER_BYPASS_UNLOADED_ENDPOINT_SEPARATION.md | 4a979638b562040455e3058351db24358e7ecb093e5c0c1635dcd6438492eecd |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md | 79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8 |

## 2. The complete one-endpoint separation really applies

C has its genuine unloaded degree-two star with neighbors D and B.
Thus its original positive
forces give the actual normal channel. A is an actual unit bypass,
because both AD and AB are physical contacts. The unit-bypass theorem
therefore forces reserve one and keeps the unchanged transverse mean.
It also supplies the full transverse separation needed to put the
bypass on one side of C; no zero transverse gap is presumed.

The manuscript then uses only the one-endpoint theorem, Sections 1--6
of the fourth input, with the exact substitution

    local transmitter S = C;
    local unloaded endpoint A = D;
    local other endpoint D = B;
    local bypass T = A;
    local external neighbor B = T.

The endpoint here has the complete original D3 star C,A,T. The local
theorem places no load or degree condition on its other endpoint or
on its bypass. In particular the present loaded B is not used as an
unloaded endpoint. The source's later two-endpoint corollary is not
being invoked.

I read and rederived the full one-endpoint feature proof. Its backward
reach bound holds for every actual minimizing face point, including
a variable side mean. Its oblique endpoint cover retains the
coincident transmitter/bypass application, the whole owned upper
side, the upper vertex, both original external-side endpoints, and
the strict external vertices. The full unloaded endpoint torque is
what excludes the problematic lower vertex. In the final upper-vertex
case the force ratio gives the strict backward-reach inequality;
the displayed margin greater than 1/9 is valid on the derived a<1/3
range. There is no boundary premise on the external neighbor.

Consequently its conclusion really is the strict inclusion of the
entire closed roof square behind the channel's near support h:

    T is contained in {z : n dot z < h}.

This strict inequality holds for every physical point of T, not just
its center or one application. It is exactly the conclusion needed
below.

## 3. Strict high radius is derived, including the genuine slider

The genuine diagonal-leaf classification gives an original leaf
vertex at r e, where r=R-sqrt(2), meeting the relative interior of a
root side. The compatible initial bridge selection excludes an
off-origin corner/corner bridge. Thus after placing the genuine leaf
East, the full root chart is

    T=[r-1,r] times [a-1,a], 0<a<1.

Since 0<r<1 in the original radius window, this proves that O is in
the open interior of T. In particular its support h_T(n) is strictly
positive in every direction. This is stronger than merely knowing
that the closed root contains O and is correctly justified here by
the original strict side slider.

The actual far endpoint B lies beyond n-support h+1. The degree-free
contained-unit estimate gives h+1<=d, with
d=sqrt(R^2-1/4)-1. Therefore

    0 < h_T(n) < h <= d-1.

This is an immediate contradiction for every d<=1, including the
critical endpoint. All subsequent use of R>2 and positive epsilon
is therefore legitimate. No independent nine-square radius-two
certificate is needed by this proof.

I independently checked the exact comparisons giving

    0<epsilon=d-1<1/60, R<25/12,
    r>1/2, s=1-r>1/3, r^2-s^2>1/16.

The root support is a sum of four nonnegative terms. Since both its
horizontal margins exceed 1/3, the strict bound h_T(n)<epsilon
implies |n_x|<3epsilon<1/20. A global vertical reflection may make
n_y positive; it changes a to 1-a if necessary and moves no unit.
The same support formula then gives

    n_y>19/20, a n_y<epsilon, a<1/57<1/4.

No origin shift, channel-normal replacement, or centering of the
roof's actual slider has entered this deduction.

## 4. Full audit of the force-free shallow diagonal-leaf screen

I read the entire shallow-side input, including its actual free
vertex/vertex feature cover, rather than just its theorem statement.
Its premises are now satisfied: R>2, the genuine radial D leaf is
still physically present, 0<a<1/4, and A physically touches both T
and the circle. It permits arbitrary degree and circle weight at A.

For a positive vertical roof normal, the upper-left roof vertex is
impossible because its norm is below r. The remaining North port
(q,a) has q>sqrt(6)/5, |(q,a)|<3/4, and r+q>1. These are genuine
physical point bounds from A's boundary status.

For every upward vertex frame, writing its inward-axis sum as
(Delta,sqrt(2-Delta^2)), the real leaf prevents Delta>=1/2 by an
actual unit segment entering the leaf interior. Its crossing occurs
strictly before length one and below the leaf's upper vertex. The
opposite-corner norm is increasing in Delta on the entire retained
interval, including negative Delta. The resulting bound is
553/144<4. The adjacent corners have norm below 7/4. Thus every
physical circle corner is excluded, independently of its weight.

The North side-owned frame retains the full actual side mean. The
real leaf bounds its right edge, and all four corners have norm
squared below 41/16. For a Northeast contact owned by the neighbor,
the complete original mean rho remains in [0,1]; leaf disjointness
gives rho<=a/(c+d), and the actual inward normal segment gives
d>1/8. The negative tangential far endpoint is strictly inside the
circle. The other endpoint is handled by convexity and the exact
far-corner comparison (65-46sqrt(2))/8<0. Its sign follows from
2*46^2-65^2=7.

Finally, the genuinely free Northeast vertex contact is covered by
the physical tangent-sector alternatives. A nonpositive inward
side angle enters the real leaf. A positive angle is precisely the
already excluded upward-vertex frame. This keeps all possible
selected free normals and both side-axis endpoints. The input
therefore supplies m_y<=0 at the present full scope, without a
hidden proper-concurrence or two-force premise.

## 5. The unchanged T3 equation exhausts all contact normals

Let the two actual roof-to-block normals be m,k. Its full unloaded
equation is

    alpha East + beta m + gamma k = 0,
    alpha,beta,gamma>0.

If m_y=0, then k_y=0. Opposite horizontal normals would put A and D
beyond opposite sides of T and make their actual AD contact
impossible. Both East is incompatible with the positive East leaf.
Thus both are West.

If m_y<0, then k_y>0. An owned South m or owned North k has negative
dot product with the other normal. The complete physical triangle
side-normal theorem excludes these possibilities with all means
retained. The two normals are therefore strict lower/upper vertex
normals. Their two opposite-vertex pairings are excluded by the
physical triangle support-span proof. The remaining right/right
pair has positive horizontal sum and contradicts the full T3 force
equation. Only Southwest m and Northwest k remain.

This reconstructs the exact two-row cover. The argument uses the
actual physical triangle T,A,D, not a circle-force triangle or a
triangle obtained by discarding a force.

## 6. Both rows contradict the actual AB application

Every actual AB point z has n dot z>=h+1>1 by the original B
channel half-plane. It is enough to bound the full actual square A.

For strict Southwest m, its roof application is the actual lower-left
vertex (-s,a-1). The support-span lemma applies to A at that same
minimum-m point in direction North, because m_y<0. It gives
max A_y<a for every A frame and every original support-face mean.
Containment gives |z_x|<=R, hence

    n dot z < R/20+a n_y < 29/240 < 1.

For West/West, the actual mean is P=(-s,y), y<=a. Because A is
physical boundary, the reverse triangle inequality and unit diameter
give |P|>=R-sqrt(2)=r. Thus y^2>1/16. The positive branch is
impossible because y<=a<1/4, and y<-1/4 follows strictly.

At a maximum-x support face, an aligned square reaches upward by at
most one from every actual point of that face. At a unique maximum-x
vertex the inward orthogonal axes have upward reach strictly less
than one. Those two alternatives exhaust the physical frames;
the weak side endpoints are retained in the first. Therefore
max A_y<3/4 and

    n dot z < R/20+3/4 < 41/48 < 1.

Negative y causes no reversal in this last bound because 0<n_y<=1
and the upper bound 3/4 is positive. Both rows contradict the actual
AB point. This completes the whole original family, not merely a
necessary-domain reduction.

## 7. Independent exact checks and final scope

In addition to the hand derivations above, I independently evaluated
the following positive rational differences using exact fractions:

| Comparison | Exact positive value |
| --- | --- |
| (121/60)^2-1041/256 | 31/57600 |
| (25/12)^2-1105/256 | 55/2304 |
| (133/64)^2-1105/256 | 9/4096 |
| 2-(140/99)^2 | 2/9801 |
| 2/3-(133/64-140/99) | 17/6336 |
| (47/32)^2-2 | 161/1024 |
| (29/20)^2-2 | 41/400 |
| 399/400-(19/20)^2 | 19/200 |
| 1/4-1/57 | 53/228 |
| 1-29/240 | 211/240 |
| 1-41/48 | 7/48 |
| 4-553/144 | 23/144 |
| 4-41/16 | 23/16 |
| 2*46^2-65^2 | 7 |
| 1-2/9-2/3 | 1/9 |

All eight source hashes in Section 1, including the reviewed caller,
were checked against the actual current bytes. These arithmetic
checks supplement the complete continuous proof; they are not pose
samples or a finite replacement of the physical feature cover.

The verdict is full independent acceptance of exactly
M6.B5L.HOUSE.ROOF.LAB.D and its roof-preserving reflected load set.
All radii in the stated window, every original mean and circle mask,
the full true degrees, and all nine units are retained. The S
companion and all other load or coarse families remain separate.
No source correction, new normal choice, force deletion, motion,
Lean compilation, CI, remote write, or metadata mutation was used.
