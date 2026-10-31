# Full independent review: the diagonal-leaf roof AB house family

Date: October 28, 2026.
Reviewer: triangle_bridges, separate from the root author and the other
independent reviewer.

**Verdict: ACCEPTED in the entire stated original family, without any
mathematical or exposition correction.** This is a full source and
original-domain audit. It does not itself edit any gate or ledger.

## 1. Frozen source and the original graph

I read the entire source

`HOUSE_ROOF_AB_D_COMPLETE_EXCLUSION.md`

at SHA-256

    7b0bd9ee78d84e5d68424034729d55187fa44ea10035f56a57bd1c5fa75dc119.

The reviewed source has 13,344 bytes. I independently rederived its
physical and force arguments rather than accepting the author's proposed
summary. I also read the original house-roof load row and its reflection
in the current graph/load cover, the operative genuine-leaf classification,
the complete unit-bypass theorem, the complete one-endpoint separation
proof, the whole shallow-D boundary-neighbor proof, and both degree-free
triangle facts at their literal scopes.

The actual positive edges are

    AT, DT, AD, AB, BC, CD, TL.

The original loaded block vertices are exactly A,B; L is the positive
genuine D leaf. Thus T has its complete unloaded root star A,D,L;
D has its complete unloaded star T,A,C; C is the actual unloaded
two-force transmitter between D and B. A is loaded degree three and
B loaded degree two. Every one of these forces remains. In particular
the proof never applies an unloaded equation at B, a two-force equation
at D, or a leaf-free equation at T.

The roof-preserving reflection exchanges A,D and B,C while fixing T,L.
It takes AB to DC and gives precisely the second actual member of the
original load orbit. All nine squares remain present, including the
three arbitrary completion units and every additional zero-weight
physical contact. Neither loaded body's circle mask or individual
corner weights are restricted by the proof.

## 2. Literal one-endpoint theorem substitution

I read and independently checked Sections 1--6 of
`CHORDED_HEXAGON_SIDE_TRANSMITTER_BYPASS_UNLOADED_ENDPOINT_SEPARATION.md`,
including every aligned/tilted endpoint, coincident application, variable
side mean and force sign. Its full later two-endpoint and original graph
join were also read, but those stronger force hypotheses are not imported.

The actual C is an unloaded two-force transmitter. The actual A touches
both endpoints D,B, so the complete unit-bypass theorem gives width
exactly one and full transverse separation. It does not force a zero
transverse gap, center any mean, or assume a common endpoint frame.
In the unchanged original channel direction n, the endpoint supports are

    D subset {n.x<=h},   B subset {n.x>=h+1}.

The literal substitution into the one-endpoint theorem is

| Source role | Present actual unit | Required property |
| --- | --- | --- |
| Transmitter S | C | True unloaded degree two |
| Endpoint A | D | True unloaded degree three, neighbors C,A,T |
| Other endpoint D | B | Physical channel endpoint; load and degree unrestricted |
| Bypass T | A | Actual contacts to both D and B; load and degree unrestricted |
| External neighbor B | T | The remaining original positive D neighbor |

The transmitter's actual mean is translated to the source origin, and
the transverse sign is chosen from the actual bypass separation. This
is a rigid coordinate change, not a motion or a normal reselection.
The conclusion is the strict containment of the entire closed roof:

    T subset {n.x<h}.

In particular it is stronger than a bound on its center or its D port.
The original theorem requires no unloaded condition at the present B or
at the present loaded A. There is therefore no degree/load mismatch.

For completeness, my rederivation of the imported local argument checked
the following points. At any actual minimum-support point p, a normal
with negative x component permits forward x reach at most |n_y|<1.
For an upward-steep normal (c,d), 0<c<d, the whole reach is at most c+d.
These estimates include every original support-face mean. They force
the bypass normal's x component nonnegative and the external normal's
x component strictly negative by the full unloaded three-force equation.

At a tilted endpoint with inward axes u=(-a,b), v=(-b,-a), the actual
bypass port is only P, the complete upper side, or the upper vertex.
The coincident P case uses the full torque and eliminates both adjacent
external vertices. The upper-side case excludes its entire opposite
shared-side mean and then gives two strictly negative torque terms at
the remaining lower vertex. At the upper vertex the unchanged torque
gives, with t=c/d,

    t<(b-a)/(a+b),
    1+a<=c+d<sqrt(2)b,
    (3a-1)(a+1)<0.

Thus a<1/3. The exact external ratio has

    D0=b-a-bt>a(b-a)/(a+b)>a^2/b,
    |m_y|=a/sqrt(D0^2+a^2)<b.

The last comparison uses 1-2a^2-2ab>1/9. This proves strict external
half-plane containment in every actual feature, including the full
variable opposite-side mean. The theorem therefore supplies precisely
the strict conclusion used in the new house proof.

## 3. All lower radii and the genuine root chart

The sharp degree-free support bound at the actual contained B gives
h+1<=d, where d=sqrt(R^2-1/4)-1. The genuine D leaf attaches at the
relative interior of its root side under the original compatible
preselection. Its inner radius r=R-sqrt(2) is strictly between zero
and one throughout this problem. Consequently its actual root has O
in its open interior, so h_T(n)>0 for every unit n. Combining this
with the strict roof inclusion gives

    0<h_T(n)<h<=d-1.

This already excludes the entire d<=1 domain, including equality,
and yields R>sqrt(17)/2>2. No higher-radius premise has been silently
applied before it is proved.

Orient the genuine D leaf East. The exact remaining root is

    T=[-s,r] times [a-1,a],
    r=R-sqrt(2), s=1-r, 0<a<1.

The strict slider is the actual relative-interior contact condition;
there is no assumption that the leaf contact is centered on the root
side. The real D leaf at (r,0) remains an obstacle in the subsequent
physical theorem.

I rechecked the complete exact margins r>1/2, s>1/3 and
r^2-s^2>1/16 from the stated radius window. The intermediate bound
R<133/64 follows from a squared reserve 9/4096. The other exact
comparisons in the source give r<2/3 and the required positive norm
difference. No approximate decimal inequality is needed.

For n=(u,v), the displayed support function is the exact rectangular
support, with four nonnegative terms. Hence |u|<3 epsilon<1/20.
The unit-length constraint makes v nonzero. Reflecting the actual
configuration vertically, if needed, gives

    v>19/20,   a v<epsilon,   0<a<1/57<1/4.

The reflection interchanges the genuine root slider margins and keeps
all original means and normal directions consistent. The inequalities
are strict where used, because h_T(n)<h and epsilon<1/60 are strict.

## 4. Full shallow-D physical input and complete T3 feature cover

I read and rederived the entire current
`D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md`. It assumes only the actual
root, actual D leaf and a physically boundary-touching neighbor. It
allows arbitrary degree, physical masks, zero total boundary load and
every common support point and normal. In particular it does not need
the loaded A to be a two-force tip or to have a proper concurrence.

At the shallow top side, its complete upper-neighbor proof first
excludes the northwest root corner by the physical boundary-point norm.
An upward minimum vertex has only its opposite corner available for
circle contact; crossing the real D leaf bounds its tilt and makes that
corner strictly inside. The aligned North side keeps the entire actual
mean and is excluded by the real leaf interval. For a neighbor-owned
strict Northeast side, both its side offset and its inward segment are
controlled by the real leaf, and every possible far corner is inside.
The remaining vertex/vertex sector either crosses the leaf or is the
already excluded upward vertex frame. Thus the actual TA normal m
indeed satisfies m_y<=0 without any force premise at A.

The complete unchanged root force equation is

    alpha East+beta m+gamma k=0,   alpha,beta,gamma>0,

where k is the original TD normal. I checked every force-sign endpoint:

* If m_y=0, the vertical equation gives k_y=0. Opposite horizontal
  directions would separate A and D by the roof's full unit width,
  contradicting their actual AD contact. Both East cannot balance the
  positive East leaf. Both normals are therefore West.
* If m_y<0, then k_y>0. An owned South m or owned North k would have
  negative dot product with the other actual triangle normal, contrary
  to the degree-free owned-normal triangle theorem. Both are strict
  vertex normals.
* The two opposite-vertex choices are excluded by the complete physical
  triangle support-span proof. Of the two remaining same-side pairs,
  Southeast/Northeast cannot balance the positive East leaf. Exactly
  Southwest/Northwest remains.

This yields precisely the two source alternatives. It retains the
parallel West/West means, every axis endpoint and both entire strict
normal cones. The argument uses the real TAD triangle and the true T3
equation; no D force is dropped or replaced.

## 5. The two actual boundary-neighbor reach contradictions

The positive original AB edge supplies an actual common point z with
n.z>=h+1>1. This is the only fact about AB used after the complete
root cover. It remains true regardless of AB owner, degree, mask or
original mean.

In the strict Southwest row, the root application is P=(-s,a-1).
The same P minimizes m on the actual A. Since m_y<0, the complete
strict support-span lemma in direction North gives max_A y<a.
This covers a side-interior minimum on A and its endpoint means as
well as a strict vertex. With |z_x|<=R, |u|<1/20 and a v<epsilon,

    n.z < R/20+a v <25/240+1/60=29/240<1.

No projection is bounded using an altered application point.

In the West/West row, the unchanged TA mean is P=(-s,y),
a-1<=y<=a. Because A physically reaches the radius-R circle, every
point of A has norm at least R-sqrt(2)=r by its actual diameter.
Thus y^2>=r^2-s^2>1/16. Since y<=a<1/57, the actual mean satisfies
y<-1/4. Weak equality in the diameter inequality therefore causes
no problem.

At its maximum-x support point, an aligned square has upward reach
at most one for every side mean. A tilted square has inward axes
(-c,t),(-t,-c), c,t>0, and upward reach exactly t<1. These exhaust
all actual A frames, with the axis limits included in the side case.
Consequently max_A y<3/4. Since 0<v<=1, the estimate v z_y<3/4
also holds when z_y is negative. Therefore

    n.z < R/20+3/4 <25/240+3/4=41/48<1.

Both complete root alternatives contradict the actual AB contact.
No circle force or torque equation at loaded A or B is used.

## 6. Exact arithmetic and input readback

I independently recomputed eighteen rational identities or reserves
using Python Fraction arithmetic. The complete checks included:

| Comparison | Exact result |
| --- | --- |
| (121/60)^2-1041/256 | 31/57600 |
| (25/12)^2-1105/256 | 55/2304 |
| (133/64)^2-1105/256 | 9/4096 |
| 2-(140/99)^2 | 2/9801 |
| 2/3-(133/64-140/99) | 17/6336 |
| (47/32)^2-2 | 161/1024 |
| 1-(1/20)^2-(19/20)^2 | 19/200 |
| 1/4-1/57 | 53/228 |
| 1-29/240 | 211/240 |
| 1-41/48 | 7/48 |
| 1/2-(5/8)^2, in the real-leaf crossing input | 7/64 |
| 4-553/144, in the physical upward-corner input | 23/144 |
| 2*46^2-65^2, in the physical Northeast input | 7 |

The other five checks were the exact source sums or simplifications,
including the three explicitly zero identities. All passed. Strict
comparisons following one of those identities are supplied by the
strict preceding bounds, not by treating zero as positive.

All seven printed dependency pins match the current readable bytes:

| Source | SHA-256 |
| --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 |
| UNIT_BYPASS_NORMAL_CHANNEL.md | d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8 |
| CHORDED_HEXAGON_SIDE_TRANSMITTER_BYPASS_UNLOADED_ENDPOINT_SEPARATION.md | 4a979638b562040455e3058351db24358e7ecb093e5c0c1635dcd6438492eecd |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md | 79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8 |

The contained-unit and physical opposite-vertex parts of the end-triangle
source are the only parts imported. Its loaded degree-two tip force
theorem is not used in the house. The read complete independent
one-endpoint review agrees with the newly checked literal scope; the
acceptance here is based on the full mathematical source, not merely
that earlier review.

## 7. Accepted whole consequence and limits

The whole original `M6.B5L.HOUSE.ROOF.LAB.D` family, including its DC
reflection, is independently accepted as excluded. All radii in the
original interval, all actual root sliders, all support owners and
means, both loaded physical masks, and all zero individual circle
weights are covered. The proof keeps the entire nine-unit packing.

The S companion and other roof load families are separate. This review
does not assert a whole house, five-body-block or coarse-cell closure.
It does not mutate metadata or authorize publication. The frozen source
requires no correction; the separate second review requested for this
root-authored proof remains an independent record.
