# A finite support-feature alphabet for loaded seven-rings

**Status:** hand classification of necessary local candidates; independent
full mathematical review passed on 2026-10-29, including the side-endpoint
check in Section 6. The alphabet is a cover by necessary candidates, not
a realization theorem. The subsequent independently reviewed corner,
cap and enlarged-core assembly theorems now exclude every loaded
seven-ring of the jointly selected certificate; Section 6 records that
closure. The original 25 local symbols and 34 proper-contact schemes
are retained as the fixed combinatorial cover.

Use the entirely loaded physical seven-ring from
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). Keep the
original nonzero pair forces `f_i`, actual contact points `p_i`, and positive
circle loads. The reviewed
[force-origin theorem](SEVEN_RING_FORCE_ORIGIN.md) gives strictly increasing
force-ray angles with

```text
0<delta_i=arg(f_i)-arg(f_(i-1))<pi,
sum_i delta_i=2pi.                                      (1)
```

On body `i`, the incoming actual force is `f_(i-1)` and the outgoing
actual force is `-f_i`. Their sum is its outward circle-load resultant
`g_i`. Incoming and outgoing below always use this fixed cyclic order.

## 1. Support features retain boundary contacts correctly

For each applied pair force, use its inward supporting normal on the body.
A square's exposed support feature is exactly one of:

* `S`: a whole edge, when the normal is perpendicular to that edge;
* `V`: a single vertex, when the normal is strictly inside that vertex's
  inward normal cone.

The application point for an `S` incidence may be an endpoint of its
support edge. Thus a geometric corner contact is not automatically a `V`
incidence. This convention retains force-normal boundary cases without
perturbing the stress or changing any application point.

The two application points on one ring body are distinct. Otherwise its
two ring neighbors would touch at that same point; they are nonneighbors
of one another, contrary to the loaded-ring separation theorem. Also no
application point is a point of the containing circle: two packed squares
cannot share such a point, as proved in Section 1 of
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md).

Every pair contact has one of the four ordered support types

```text
SS, SV, VS, VV.                                        (2)
```

An `SS` pair has parallel supporting edges, with either segment overlap or
endpoint intersection. `SV` and `VS` pairs have a vertex on a supporting
edge. A `VV` pair has two strictly exposed vertices at its contact point.
These are support-feature statements, not generic-position assumptions.

## 2. Ten candidates when the circle vertex is unique

Choose a positively oriented square frame and local unit-square labels so
that its unique circle vertex is `W=(1,1)`. Its physical coordinates relative
to the disk center are `(X,Y)` with `X,Y>1/2`. Normalize the total circle
load to one, so `g=(X,Y)` has both coordinates strictly positive.

Label the other vertices and the edges as follows:

```text
A=(0,0): opposite corner,    B=(1,0),    C=(0,1),
L: left edge, D: bottom edge, R: right edge, T: top edge.
```

Here the coordinates in these labels specify locations within the unit
square; its physical opposite corner is `(X-1,Y-1)`.
The inward directions for `L,D,R,T` are respectively
`(+1,0),(0,+1),(-1,0),(0,-1)`. The strict inward cones at `A,B,C` are
respectively `(+,+),(-,+),(+,-)`. The circle vertex `W` cannot be used.

Every body is in the following table. An arrow means its incoming support
feature followed by its outgoing support feature.

| Candidate | Incoming → outgoing | Force turn | Additional necessary coordinate restriction |
|---|---|---|---|
| U1 | `D → L` | `delta=pi/2` | — |
| U2 | `D → A` | `pi/2<delta<pi` | `X<1<Y` |
| U3 | `A → L` | `pi/2<delta<pi` | `Y<1<X` |
| U4 | `R → A` | `0<delta<pi/2` | `X<1<Y` |
| U5 | `A → T` | `0<delta<pi/2` | `Y<1<X` |
| U6 | `D → C` | `0<delta<pi/2` | — |
| U7 | `B → L` | `0<delta<pi/2` | — |
| U8 | `B → A` | `0<delta<pi` | `X<1<Y` |
| U9 | `A → C` | `0<delta<pi` | `Y<1<X` |
| U10 | `B → C` | `0<delta<pi/2` | — |

No assertion is made that each row can occur in a complete packing.

### Completeness of the table

Write the two actual inward forces as `a,b`, so `a+b=(X,Y)`, with
`a=f_(i-1)` and `-b=f_i`. The counterclockwise turn from `a` to `-b`
is the number in (1).

For two edge supports, positivity of both components of `a+b` forces the
pair of inward directions `L,D`. The allowed order is `D → L`; the reverse
order would have force turn `3pi/2`.

If one support is the corner `A`, positivity allows any of the four edge
directions. The turn condition leaves precisely
`D → A`, `A → L`, `R → A`, and `A → T`.
If the corner is `B`, only the edge direction `L` can supply the missing
positive first component; the allowed order is `B → L`.
If the corner is `C`, the analogous argument gives `D → C`.

For two strict vertex supports, equal vertices are excluded by distinctness
of the application points. The pair `A,B` allows only `B → A`, and `A,C`
allows only `A → C`. For `B,C`, positivity of the sum forces the
counterclockwise order `B → C`. Its two force rays belong to the same open
quadrant, so its turn is acute. This exhausts all possibilities.

The turn bounds also follow directly from the inward cones. For a mixed
edge/vertex body, an incident edge and vertex have actual inward-force
angle below `pi/2`, hence force-ray turn above `pi/2`. A nonincident edge
and vertex give the reverse inequalities. The two adjacent strict-vertex
rows U8 and U9 may have either acute or obtuse turn and are deliberately
left unrestricted within (1).

### Why the opposite-corner rows have a small own coordinate

Whenever the strict support vertex `A` is used, the
[inner-corner clearance lemma](LOADED_INNER_CORNER_CLEARANCE.md) gives

```text
min(X,Y)<1.                                            (3)
```

If both coordinates exceeded one, the neighbor would be circle-clear.
If their minimum were one, the only loaded-neighbor exception would be a
shared-side square with a boundary normal, not a strict `V` support.
The case `X=Y=1` is outside the radius window.

For U2, write the bottom-side application point as
`(X-1+xi,Y-1)` and its positive inward force as `(0,h)`.
The other force acts at `A`. Taking the total torque about the original
origin gives

```text
Y-X=h*xi>0,
```

where `xi>0` because the two application points are distinct.
For U8, write the incoming force at `B` as `(-b,h)` with `b,h>0`;
the same torque calculation gives `Y-X=h>0`. Together with (3) and
`X^2+Y^2>=6241/1600>2`, these yield `X<1<Y`.

For U4, the neighbor supported beyond the outer right edge has minimum
first coordinate at least `X`. Every unit square has projection width at
least one in any direction, so disk containment gives `X<=R_disk-1`.
Consequently

```text
Y^2=R_disk^2-X^2>=2R_disk-1>1.
```

Equation (3) then forces `X<1<Y`.
Reflection across the coordinate diagonal, combined with reversal of the
cyclic order, proves the stated restrictions for U3, U5, and U9.

## 3. The radial-side boundary cases are also finite

A loaded square has either one circle vertex or two adjacent circle
vertices. Indeed the farthest-corner formula is

```text
|center|^2+1/2 +/- center dot u +/- center dot v.
```

Two corners tie only when one center coordinate vanishes. Four ties would
put the center at zero and give radius `1/sqrt(2)`, outside this problem.
Thus there are no additional circle-feature cases.

For a radial-side body, the circle-load resultant is a positive multiple
of a point of the outer circle edge, allowing either endpoint if just one
geometric circle vertex has positive load. First suppose both components
of the resultant are nonzero. Choose the positively oriented square frame
so that both are positive. The circle edge is then either the outer right
edge or the outer top edge.

No contact can use that outer circle edge as an `S` support. Its distance
from zero is `sqrt(R_disk^2-1/4)>R_disk-1`; a unit square beyond its
supporting line would have maximum projection greater than `R_disk`.
Both endpoints of the circle edge are forbidden application points as well.

Applying these deletions to the ten-row cone table gives:

| Circle edge | Allowed local candidates |
|---|---|
| Right (`R_x`) | `D→L`, `D→A`, `A→L`, `A→T`, `D→C`, `A→C` |
| Top (`R_y`) | `D→L`, `D→A`, `A→L`, `R→A`, `B→L`, `B→A` |

The coordinate restrictions in the unique-vertex table are not transferred
to these rows: their circle-load resultant need not be a circle vertex.
The support-cone turn classifications do transfer unchanged.

If the resultant is exactly radial, orient the first axis outward, so its
components are `(positive,0)` and the circle edge is the right edge.
The only candidates are

```text
D → C,        A → T,        A → C.                     (4)
```

This follows by imposing cancellation of the second force components.
The first two rows have acute turn; the last is in `(0,pi)`.
Thus a finite alphabet of `10+6+6+3=25` local candidates covers every
circle-load and support-feature case. Continuous force ratios, contact
positions, and frame angles remain attached to these candidates.

## 4. A turn budget and an incidence identity

A body with two edge supports must have adjacent supports. Equal edge
directions would give force-ray turn `pi`, and opposite directions would
give turn zero. Therefore every `SS` body has turn exactly `pi/2`.
Every mixed body whose edge and vertex are incident has turn strictly
larger than `pi/2`.

Since there are seven strictly positive turns summing to `2pi`,

```text
number(SS bodies) + number(incident mixed bodies) <= 3.  (5)
```

Let `b_SS,b_VV` count the body types with two like support features.
Let `e_SS,e_VV` count the corresponding pair-contact types in (2).
Counting all fourteen incidences in the two ways gives the exact identity

```text
b_SS-b_VV=e_SS-e_VV.                                   (6)
```

This remains valid for geometric shared-side endpoints, because their
support features were retained rather than assigned by the application
point alone.

## 5. Thirty-four coarse words when every pair has one edge and one vertex

Assume all seven pair contacts have type `SV` or `VS`. Orient each contact
from its `S` body to its `V` body. An `SS` body is then a source, a `VV`
body a sink, and a mixed body transmits the arrow. Sources and sinks
alternate around the cycle. Equations (5)--(6) give

```text
b_SS=b_VV=r in {0,1,2,3},
number(mixed bodies)=7-2r.                              (7)
```

For `r=0`, all arrows have the same cyclic orientation. There are two
coarse words: every body has incoming `V`, outgoing `S`, or every body has
incoming `S`, outgoing `V`.

For `r>=1`, start at a source and record the numbers of mixed bodies on
the successive runs between alternating sources and sinks. These are
`2r` nonnegative integers with sum `7-2r`:

| r | Run-length tuples | Number before identifying repeated cyclic starts |
|---|---|---:|
| 1 | `(l_0,l_1)`, sum `5` | `6` |
| 2 | `(l_0,l_1,l_2,l_3)`, sum `3` | `20` |
| 3 | `(l_0,...,l_5)`, sum `1` | `6` |

The counts are the elementary composition counts
`binom(6,1)`, `binom(6,3)`, and `binom(6,5)`.
Together with the two pure words, these give a cover by at most
`2+6+20+6=34` coarse cyclic schemes. Some schemes may agree after a
cyclic shift; no uniqueness of this representation is asserted.
Each body in a scheme must also satisfy its row of the 25-symbol local
alphabet and the turn budget (5).

## 6. Successive reductions and closure of all ownership families

In the pure incoming-`V` word, if every body has a unique circle vertex
and row U7 (`B→L`), the support-edge application points are in fact
strict side-interior points. This needs a separate endpoint check because
the definition of `S` above deliberately allows edge endpoints.

Rotate each local frame to the notation of
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md). Then

```text
p_(i-1)=w_i-u_i,
p_i=w_i-lambda_i u_i+v_i,       0<=lambda_i<=1.
```

The force-turn table gives `0<delta_i<pi/2`. The force and torque
calculation in that note, which does not require strictness of lambda,
gives `lambda_i mu_i=mu_(i-1)cos(delta_i)>0`. Thus `lambda_i>0`.

Suppose `lambda_i=1`. At this contact use the first body's frame and write

```text
P=A_i=(a,-H),       w_i=(a+1,-H-1),
c=cos(delta_(i+1)), s=sin(delta_(i+1)),       c,s>0,
w_(i+1)=P+(c,s).
```

The first body's unique-farthest-vertex sign gives `H>-1/2`.
The next body's corresponding sign is
`Z:=a*s+H*c>1/2`. Equal squared norms of the two circle vertices give

```text
a(1-c)+H(1+s)=-1/2.
```

Using `c^2+s^2=1` and `s>0`, this identity implies

```text
Z-1/2 = -[(1+s+c)/s]*(H+1/2)<0,
```

contradicting `Z>1/2`. Therefore `lambda_i<1` as well. All contacts
indeed satisfy the strict pattern, which is already excluded by the
[hand cap proof](SEVEN_RING_RADIAL_CAP_BOUND.md).
Its reflection and reversal is the pure incoming-`S` word with row U6
(`D→C`) everywhere, and is excluded by the same theorem.

The newer [inner-face capacity theorem](SEVEN_RING_INNER_FACE_CAPACITY.md)
and its [radial-side extension](SEVEN_RING_RADIAL_INNER_FACE_CAPACITY.md)
exclude every proper `SV/VS` ring whose unique-circle local rows all
belong to `U1,U6,U7,U10`, including nonuniform source/sink schemes and
arbitrary radial-side bodies. The
[shared-side extension](SEVEN_RING_SHARED_SIDE_CAPACITY.md) also permits
SS pair contacts whenever no VV pair is present, under the same restriction
on unique-circle rows.
Moreover the [incident mixed exclusion](LOADED_INCIDENT_MIXED_EXCLUSION.md)
rules out U2 and U3 in any entirely loaded ring, regardless of the pair
support types. These deductions prune the raw alphabet; they do not
change its original 25-symbol coverage or the 34 coarse-scheme count.

The [all-pair inner-face capacity theorem](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md)
also absorbs VV pair defects under a stronger certificate selection.
Its additional normal choices are made before the positive graph is
classified and are compatible with the preceding finite-polynomial
exclusions. Consequently every remaining loaded ring of that certificate
contains at least one unique-circle body U4,U5,U8 or U9. The subsequent
[outer-edge reduction](SEVEN_RING_OUTER_EDGE_REDUCTION.md) also absorbs
U8/U9: their opposite V contact equals their core corner and contributes
only a degenerate triangle. Therefore U4 or U5 is necessary in every
remaining loaded ring of this certificate.

A finite cover of the ownership problem remaining at that stage was:

1. Proper `SV/VS` pair contacts with no sources or sinks, and at least one
   unique-circle outer-edge/opposite-corner row U4 or U5.
2. Proper `SV/VS` pair contacts with `r=1,2,3`, represented by the
   `6+20+6` source/sink schemes above, and at least one unique-circle row
   U4 or U5.
3. At least one strict `VV` pair contact and at least one unique-circle
   U4 or U5 body. Every unique-circle endpoint of a VV pair is U4--U7
   and has its other positive pair on a shared SS segment with aggregate
   application in its relative interior. Radial endpoints retain their
   separate load-split scope.
4. No `VV` pair, but at least one `SS` pair contact and at least one
   unique-circle U4 or U5 body. Endpoint and shared-segment cases remain
   included.

All four families are now excluded by the reviewed outer-body extension:

* [Outer-corner clearance](LOADED_OUTER_CORNER_CLEARANCE.md) strengthens
  the compatible normal selection and proves that every U4/U5 extra
  inner-boundary corner has squared norm below `33/20`.
* The [outer-spike cap](OUTER_SIDE_SPIKE_CAP_BOUND.md) and its
  [capacity margin](OUTER_SIDE_CAPACITY_MARGIN.md) put every inner-square
  vertex in an outer proper-contact spike below squared radius `83/50`.
* The [enlarged-core assembly](SEVEN_RING_OUTER_CORE_ASSEMBLY.md) includes
  those extra corners and spikes, all SS boundary replacements, every
  VV degeneracy, and every radial load split. All three inner squares
  would lie in the disk of squared radius `83/50<425/256`, contradicting
  the known three-square minimum.

The strengthened intervals and finite-polynomial conditions are imposed
jointly before constructing and classifying the stress; this conclusion
does not require preservation of a previously selected positive graph.
Thus every word in the original 34-scheme proper-contact cover is excluded,
and both SS/VV defect families are excluded as well. The raw 25-symbol
alphabet and 34-scheme denominator are unchanged: their continuous
realizations have been excluded by one geometric capacity theorem, rather
than counted by a new enumeration. This closes the loaded seven-ring
case C04; it is not a proof of the other n=10 component cases.
