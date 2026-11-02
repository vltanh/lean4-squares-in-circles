# Frame selection: exact controls and a sharp-radius obstruction family

November 2, 2026. Computer discovery followed by exact integer checks and
the hand arguments below. No Lean or CI. These results do **not** close
another fixed mask or prove the desired extraction inside the Q-disk.

Put Q=1105/256. The proposed extraction is: after choosing a frame and
relabeling original units, find a cone four-chain whose two outer links
are actual projection comparisons, together with a disjoint cone
three-chain. Its long mask would be 000 or 010.

**Results.**

1. The property for a fixed physical configuration has an exact finite
   frame-event test; no dense angular sampling is required.
2. Seven original squares strictly inside Q can have a cone 4+3 witness
   and nevertheless have no cone four-chain with actual outer links in
   any frame. The two unselected originals cannot be discarded.
3. For every delta>0, nine original unit squares can fit in a disk with
   squared radius strictly between Q and Q+delta and have no such
   four-chain in any frame. They retain a designated 001/00 witness.
   Thus a successful Q-restricted extraction theorem must use the sharp
   radius boundary: it cannot extend to any uniform larger radius.

The third result does not refute the proposed theorem at q<=Q. At the
limit q=Q, the displayed family has an actual four-chain.

## 1. A finite event lemma for real frame directions

Let e be the horizontal unit vector and e-perp its positive quarter-turn.
For a fixed directed original pair with center difference d, its cone
comparison is

`e dot d >= |e-perp dot d|`.

This is the intersection of two homogeneous closed linear inequalities
in e. Its angular boundary consists of the two directions making d
diagonal in the frame. A cone edge between distinct centers has a
positive horizontal gap and restricts e to a closed quarter-circle.

An actual directed projection comparison between physical squares S,T
is equivalent to

`e dot (t-s) >= 0` for every corner s of S and corner t of T.

There are sixteen such homogeneous linear inequalities. Their nontrivial
boundary directions are perpendicular to nonzero original corner
differences t-s. A zero corner difference supplies an identity and can
be omitted.

Fix an ordered four-tuple and, if wanted, a disjoint ordered triple.
Require all their cone links and require the four-chain's outer links
actual. The allowable directions are the intersection of the stated
closed half-planes with the unit circle. If nonempty, this set has a
boundary direction because one of its cone edges already restricts it
to a quarter-circle. At a boundary, at least one nonzero defining linear
form vanishes. Hence the same witness exists at either:

- a center-cone diagonal event; or
- an original-corner projection contact event.

This includes singleton direction sets and all weak-contact boundaries.
Reversing e reverses both chain orders and preserves the two-outer-link
property, so directions can be taken modulo pi.

For nine squares there are at most 2*36=72 cone directions and at most
16*36=576 projection directions, before coincidences: at most 648 in
their union. The checkers also allow a redundant reference direction.
For a rational pose, all candidates can be represented by integer
vectors; support, cone, and projection comparisons then use only exact
integer arithmetic. No trigonometric rounding is involved.

For a cone chain without actual-link requirements, the cone events alone
suffice. This smaller version supplies the 52-row table in Section 4.

## 2. Exact controls that explain the necessary hypotheses

### 2.1. A compact seven-unit control inside Q

Take aligned unit squares with centers

`(-1,-1), (0,-1), (1,-1), (-1,0), (0,0), (1,0), (0,1)`,

then translate all centers upward by 1/3. Their interiors are disjoint.
Their farthest original corners have squared norm

`(3/2)^2+(7/6)^2 = (1/2)^2+(11/6)^2 = 65/18 < Q`.

In the 45-degree frame, the original sequences

`(-1,-1), (0,-1), (1,-1), (1,0)`

and

`(-1,0), (0,0), (0,1)`

are disjoint cone chains of lengths four and three. The common translation
does not change their comparisons.

Nevertheless no frame has a cone four-chain with both outer links actual.
Indeed for an arbitrary unit horizontal vector e=(e1,e2), all seven
halfwidths are h=(|e1|+|e2|)/2, while their total center-projection span
is at most 2(|e1|+|e2|)=4h. The two actual outer links of a four-chain
would already consume 4h. Its positive middle cone gap would require a
strictly larger span. This is impossible.

Exactly the same span argument applies to the full aligned 3-by-3 grid
of nine squares. That grid requires q=9/2>Q; it is a radius-free control,
not a counterexample to the desired Q-restricted extraction.

### 2.2. One explicit strict nine-unit control just above Q

The file `rational_nine_no_outer_control.json` specifies nine exact
rational centers and original frames. It is a rationalized, slightly
expanded version of a floating 001/00 discovery pose. Six first axes
are (1,0); the other three are

`(40044/40045, -283/40045)`.

The identity 40044^2+283^2=40045^2 makes these exact unit axes. The
separate checker `verify_rational_frame_control.py` verifies all 36
physical pairs and all 36 original corners. Its exact least pair
separation reserve is

`9276542653/1001125000000000 > 0`.

The largest original corner norm squared is

`43258067159502148998899413/10011250000000000000000000`

and is strictly less than

`4321/1000 = Q+147/32000`.

The complete finite event check has 521 distinct directions and finds
zero cone four-chains with both outer links actual. This is stronger
than merely finding no accompanying three-chain. The checker imports
no floating search or numerical evaluator.

## 3. A simple rational limit pose at Q

Let p=7/15, d=p-1/16=97/240. At parameter zero take all nine units
aligned, with these centers:

| Unit | Center |
|---|---|
| 0 | (-3/2,1/16) |
| 1 | (-1/2,1/16) |
| 2 | (1/2,7/15) |
| 3 | (3/2,1/16) |
| 4 | (-1,-15/16) |
| 5 | (0,-15/16) |
| 6 | (1,-15/16) |
| 7 | (-13/15,17/16) |
| 8 | (2/15,22/15) |

All 36 original pairs separate along a coordinate. The pairs at equality
are exactly

`01,04,07,12,14,15,17,23,28,36,45,56,78`.

Every other pair has a positive coordinate separation margin.
Units 0,3,4,6 have farthest squared corner norm Q. Units 7,8 have the
strict reserves

`Q-[(41/30)^2+(25/16)^2]=13/1800`,

`Q-[(19/30)^2+(59/30)^2]=2737/57600`.

The remaining units have still larger reserve. Thus this is an exact
nine-unit Q-packing. Its main four-chain 0,1,2,3 is actual and is a
cone chain; the disjoint bottom triple 4,5,6 is actual and is a cone
chain.

## 4. The only outer-actual cone four-chain at the limit

The 36 center differences give exactly 52 distinct cone-event directions
modulo sign. The exact event table below lists every ordered four-chain
at those events, up to reversal. By Section 1 it therefore covers every
cone four-chain in every real frame. The nine possible labelings are:

| ID | Four-chain up to reversal | Required actual outer normals | Consequence |
|---|---|---|---|
| 1 | (0,1,2,3) | +x,+x | Only the horizontal frame survives |
| 2 | (0,1,5,6) | +x,+x | The middle gap (1/2,-1) is not an x-cone gap |
| 3 | (0,4,5,6) | -y,+x | Incompatible outer normals |
| 4 | (0,7,2,3) | +y,+x | Incompatible outer normals |
| 5 | (3,2,1,4) | -x,-y | Incompatible outer normals |
| 6 | (3,6,5,4) | -y,-x | Incompatible outer normals |
| 7 | (4,1,2,8) | +y,+y | The middle gap (1,97/240) is not a y-cone gap |
| 8 | (4,1,7,8) | +y,+x | Incompatible outer normals |
| 9 | (6,5,1,7) | -x,+y | Incompatible outer normals |

Here the asserted unique normals are elementary. Two aligned units with
directed center difference (1,s), |s|<1, can have an actual separating
projection only in the positive horizontal direction: for any e,

`e1+s*e2 >= |e1|+|e2|`

forces e2=0 and e1>0. Reflections and coordinate interchange give all
the other entries. The printed centers verify every listed contact and
middle-gap failure directly.

For completeness, the entire cone-event table is printed here. A vector
represents its horizontal direction without normalization. IDs refer to
the preceding table. The integer centers used to obtain these vectors
are 240 times the displayed centers.

| Direction | IDs | Direction | IDs |
|---|---|---|---|
| (1,-5) | none | (1,-3) | none |
| (1,-1) | 2,3,9 | (1,1) | 6 |
| (1,3) | none | (1,5) | none |
| (1,29) | none | (3,-7) | none |
| (3,-1) | 1,2,3 | (3,1) | 1,4,5,6 |
| (3,7) | 7,8 | (5,-1) | 1 |
| (5,1) | 1 | (7,-8) | none |
| (7,-3) | 2,3 | (7,3) | 6 |
| (8,7) | 6 | (9,665) | none |
| (11,-49) | none | (17,43) | none |
| (19,41) | 7,8 | (23,697) | none |
| (29,-1) | 1 | (41,-101) | none |
| (41,-19) | 2,3,9 | (43,-17) | 1,2,3 |
| (49,11) | 1,4 | (55,729) | none |
| (101,41) | 1,5,6 | (143,-337) | none |
| (143,337) | 7,8 | (185,-489) | none |
| (185,-471) | none | (217,-457) | none |
| (217,457) | none | (305,-849) | none |
| (337,-143) | 1,2,3 | (337,143) | 1,5,6 |
| (369,785) | none | (383,577) | none |
| (457,-217) | 2,3,9 | (457,217) | 6 |
| (471,185) | 1,4,5,6 | (489,185) | 1,4,5,6 |
| (545,-609) | none | (577,-383) | 2,3,9 |
| (609,545) | 6 | (665,-9) | 1 |
| (697,-23) | 1 | (729,-55) | 1 |
| (785,-369) | 2,3,9 | (849,305) | 1,4,5,6 |

The standalone exact checker `verify_limit_frame_family.py` reconstructs
the center differences, divides each event vector by its integer gcd,
checks all ordered four-tuples at every event by exact dot products,
and verifies the unique-normal and middle-gap table. The saved report
is `limit_frame_family_replay.json`. Its complete finite table is
`limit_frame_family_table.json`, SHA-256
`bf9f975444d34b251239d32b7c5c0a4b52f0edf0cd0ace91c6d70a732d85226f`.

It follows that, up to reversal, the limit packing's only cone
four-chain with actual outer links is 0,1,2,3, and its only possible
horizontal direction is (1,0).

## 5. A physical perturbation with incompatible outer contact normals

For a parameter t>0 sufficiently small, put

`a=(1-t^2)/(1+t^2)`, `b=2t/(1+t^2)`, `h=(a+b)/2`,

and retain d=97/240. Give units 2,3,8 the common original frame

`u=(a,-b)`, `v=(b,a)`;

all other original units remain aligned. Define

`X=(2/15)*a+(3/2)*b`, `Y=7/15+a+(11/30)*b`,

and use these original centers:

| Unit | Center at t |
|---|---|
| 0 | (-3/2,1/16) |
| 1 | (-1/2,1/16) |
| 2 | (h,7/15) |
| 3 | (h+(1-d*b)/a,1/16) |
| 4 | (-1,-15/16-b) |
| 5 | (0,-15/16-b) |
| 6 | (1,-15/16-b) |
| 7 | (X-h-1/2,17/16) |
| 8 | (X,Y) |

Every pose tends to the displayed limit as t tends to zero. If t is
rational, every center and frame component is rational.

### 5.1. All original physical pairs remain valid

The strict-margin pairs at t=0 remain separated for all sufficiently
small t by continuity. Each of the thirteen contact pairs listed in
Section 3 is retained or improved explicitly:

- 01,45,56 retain their aligned horizontal separation one.
- 12 and 78 have horizontal gap h+1/2, their actual support sum.
- 07 and 17 retain their aligned vertical gap one.
- 04,14,15 have vertical gap 1+b, at least their support sum one.
- 36 has vertical gap 1+b>=h+1/2 because a<=1.
- For 23, the directed center difference is `u+s*v`, where
  `s=(b-d)/a`. Its original u-normal gap is exactly one.
- For 28, the directed center difference is `v-(11/30)*u`.
  Its original v-normal gap is exactly one.

The same original frames occur in both contact formulas. The remaining
pairs have the positive limiting margins already noted, so this checks
all 36 physical pairs without substituting a proxy for an original unit.

### 5.2. The designated 001/00 witness remains

The original sequence 0,1,2,3 remains a cone four-chain for sufficiently
small t: its vertical gaps are 0,d,-d, while its positive horizontal
gaps tend to one. Links 01 and 12 are actual. The final link is strictly
weak because its horizontal gap is `(1-d*b)/a`, whereas its actual
support sum is a+b, and

`(a+b)-(1-d*b)/a = b*(a+d-b)/a > 0`

for all sufficiently small positive t. The disjoint bottom triple
4,5,6 is still an actual horizontal cone three-chain. Hence the full
original-nine packing carries mask 001/00 in the displayed frame.

### 5.3. No other frame repairs both outer links

At t=0 every ordered four-tuple other than 0,1,2,3 and its reversal has
no direction satisfying the cone and two-outer-actual conditions.
These conditions are closed and continuous in the original poses and
unit frame direction. If any such tuple became feasible arbitrarily
close to t=0, take a sequence tending to zero. There are finitely many
tuples and the circle of directions is compact. A subsequence would
converge to a feasible nonmain tuple at t=0, contradicting Section 4.
Consequently one common positive parameter neighborhood excludes every
nonmain tuple.

For the main tuple itself, the first actual link 01 forces e=(1,0), by
the aligned-contact calculation above. In the last pair 23, the two
units share the original tilted frame and their center difference is
u+s*v with |s|<1 for small t. Writing e_u=e dot u and e_v=e dot v, an
actual directed comparison would require

`e_u+s*e_v >= |e_u|+|e_v|`.

This forces e_v=0 and e_u>0, hence e=u. Since b>0, u is not (1,0).
Thus the two outer links cannot both be actual in one frame. Reversal
gives the same contradiction. Together with the compactness argument,
this excludes every cone four-chain with actual outer links for all
sufficiently small positive t.

### 5.4. The radius approaches Q strictly from above

Let q(t) be the maximum of the 36 actual squared corner norms. It is a
continuous function of t and q(0)=Q. The far bottom corner of unit 4
already has squared norm

`(3/2)^2+(23/16+b)^2 = Q+(23/8)*b+b^2 > Q`.

Therefore q(t)>Q for t>0, while q(t) tends to Q. For every delta>0,
choose a sufficiently small positive rational t in the neighborhood
established above and with q(t)<Q+delta. This gives the asserted exact
rational physical packing, with all nine originals retained and no
frame admitting the proposed long chain. This completes the third
result.

As a concrete instance, t=1/10000 has exact input
`rational_frame_family_member.json`. All 36 pairs and 36 corners pass
the independent integer/Fraction checker, and 340 distinct frame events
contain no outer-actual cone four-chain. It fits

`q<=690721/160000 = Q+3/5000`.

The saved exact replay is `rational_frame_family_member_replay.json`.

## 6. Consequence for the remaining proof

The Q-restricted structural extraction remains open. None of these
controls lies below Q with nine originals. The first-birth theorem alone
preserves cone comparisons and cannot supply actual outer links; the
examples show that a geometric argument using the full nine-unit radius
bound is necessary for this proposed reduction.

The family also explains why checking many nearby generic directions is
insufficient at equality: at its limit, the sole repairing frame is an
isolated original contact direction. Exact event directions and weak
contact conventions must be retained.

No fixed mask, gate ID, or positional root is reclassified by this note.
