# Five unchanged core squares leave room for at most three other units

Date: October 30, 2026. Author: pocket_capacity continuation.

**Status: complete conditional geometric theorem with a compact exact rational
cover, replayed by the supplied standard-library checker. Independent audit and
Lean verification are not claimed.** This is a genuine uniform physical
completion exclusion, not an infeasibility claim inferred from a pose sample.
It applies to an explicit closed neighborhood of five physical squares. It
does **not** yet prove that the entire original D02 row enters that neighborhood.

The reference points were suggested by the Type II A-only algebraic-system
exploration. Their origin is not an assumption in the proof: every reference
coordinate below is an exact rational, and the theorem holds for every actual
packing satisfying the twenty stated vertex inequalities. In particular, the
reference quadrilaterals need not themselves be exact unit squares.

## 1. Uniform physical theorem

Put

    Q = 1105/256, M = 91/60, epsilon = 1/25.

Let actual independently oriented closed unit squares have pairwise disjoint
open interiors in the disk centered at O with squared radius at most Q. Use
one orthonormal coordinate frame centered at O. Suppose five distinct actual
squares, named V,A,D,B,C, have vertices v[k,0],...,v[k,3] paired with the
following exact rational reference points r[k,j]. Each printed ordered pair
is divided by **10,000,000**.

| Actual core square | Reference 0 | Reference 1 | Reference 2 | Reference 3 |
| --- | --- | --- | --- | --- |
| V | (6418133,5643113) | (12921853,13239272) | (5325694,19742991) | (-1178026,12146832) |
| A | (-10863863,1877850) | (-863863,1877850) | (-863863,11877850) | (-10863863,11877850) |
| D | (9084566,5914966) | (10098849,-4033462) | (150420,-5047745) | (-863863,4900683) |
| B | (-6332838,-4157234) | (-14329839,-10161229) | (-20333835,-2164227) | (-12336833,3839768) |
| C | (12593641,-3026787) | (16335596,-12300286) | (7062097,-16042240) | (3320143,-6768742) |

Assume the twenty **closed** Euclidean vertex-error bounds

    |v[k,j] - r[k,j]| <= 1/25,    k in {V,A,D,B,C}, 0<=j<4.      (1)

Equivalently their squared distances are at most 1/625. The four points
v[k,j] are the vertices of that actual square; the proof only uses their
membership in that square and its convexity. No stress, force magnitude,
degree, side mean, load or circle-mask premise is imposed.

**Theorem.** There are at most **eight** actual unit squares in the disk.
Every unit other than V,A,D,B,C retains its arbitrary independent orientation,
position, contact graph and physical circle mask.

For a nine-square D02 packing, those other four units are the original N and
the three original completion squares. Thus (1) excludes that entire physical
neighborhood simultaneously for every N slider, every N load, every original
side mean, every individual zero circle coefficient and every completion
contact. The argument never fixes, optimizes or omits N.

## 2. Force-free center restrictions

For a contained unit square with center c and orthonormal side directions u,v,
its farthest vertex has squared norm

    |c|^2 + 1/2 + |c dot u| + |c dot v|
      >= |c|^2 + |c| + 1/2.

The inequality uses (|c dot u|+|c dot v|)^2 >= |c|^2. The right-hand
polynomial is increasing for |c|>=0, and the exact endpoint comparison is

    M^2 + M + 1/2 - Q = 31/57600 > 0.

Consequently every actual center satisfies

    |c| < M.                                                   (2)

Two distinct actual centers are at distance at least one: their radius-one-half
open incircles lie in the respective square interiors and are disjoint.

More strongly, if c is the center of any square other than core square S,
then

    |c-q| >= 1/2 for every q in the closed square S.             (3)

Indeed, if |c-q|<1/2, the open incircle about c contains q and some open
neighborhood of q. Every neighborhood of every point of a closed square
contains an interior point of that square. This would overlap the two square
interiors. This proves (3) also at a core vertex or a weak contact endpoint.

## 3. Rational witnesses transfer uniformly to actual core points

For each of the five rows and integers 0<=i,j<=8 set t=i/8, s=j/8 and

    w0=(1-t)(1-s), w1=t(1-s), w2=t*s, w3=(1-t)*s,
    p[k,i,j] = sum_(a=0)^3 wa*r[k,a],
    q[k,i,j] = sum_(a=0)^3 wa*v[k,a].                            (4)

The four exact weights are nonnegative and sum to one. Thus q[k,i,j]
belongs to the corresponding actual square by convexity. From (1),

    |q[k,i,j] - p[k,i,j]| <= sum wa/25 = 1/25.                  (5)

The p[k,i,j] are only rational reference witnesses; they are not asserted
to lie in an actual square. Formula (5) is precisely the error retained when
using them. This avoids silently replacing the real core by a rounded pose.

If an alleged other center c satisfies

    |c-p[k,i,j]| < 23/50,                                     (6)

then (5) and the triangle inequality give |c-q[k,i,j]|<1/2,
contradicting (3). This proof is uniform over all twenty closed-error balls.

There is a polynomial-only form of the same robust step, useful for Lean.
For u=c-p and v=p-q,

    50|u|^2 + 575|v|^2 - 46|u+v|^2 = |2u-23v|^2 >= 0.         (7)

Since (23/50)^2=529/2500 and (1/25)^2=1/625,

    50*(529/2500) + 575*(1/625) = 23/2 = 46*(1/4).

The first assumed bound is strict, so (7) gives |c-q|^2<1/4. There is
no division by a geometric parameter and no lost singular or endpoint case.

## 4. Exact finite cover: only an eastern cap or a southern band remains

The following rectangles use the unchanged O-centered coordinates:

    E = [13/10,M] x [-1/5,7/10],
    S = [-1,1/4] x [-M,-3/4].                                  (8)

**Rational cover lemma.** Every point c in [-M,M]^2 either belongs to
E or S, has |c|>=M, or satisfies (6) for one of the 405 rational
witnesses (4).

The full exact certificate is

    certificates/d02_type_ii_a_only_five_core_capacity.json

and its independently structured rational replay is

    ../../scripts/n9_five_core_capacity.py.

The certificate has **157 nodes**, including **118 leaves**, with maximum
depth **8**. Its only node/leaf rules are the following.

| Rule | Exact check | Number |
| --- | --- | ---: |
| Split | Retain all four closed midpoint subrectangles | 39 |
| Outside | Minimum squared norm on the rectangle is at least M^2 | 21 |
| Core witness | Maximum squared distance on the rectangle from one p[k,i,j] is strictly below 529/2500 | 77 |
| Eastern cap | The whole closed rectangle is contained in E | 9 |
| Southern band | The whole closed rectangle is contained in S | 11 |

The root is exactly [-M,M]^2. The fixed child order is southwest,
southeast, northwest, northeast. Every child interval includes its midpoint
endpoint; therefore the four children cover the whole closed parent. The
checker rejects omitted children, repeated nodes, cycles and unreachable data.

For a closed rectangle [a,b] x [d,e], the two numerical checks have
explicit exact formulas:

    min |c|^2 = max(a,0,-b)^2 + max(d,0,-e)^2,
    max |c-p|^2 = max(|a-px|,|b-px|)^2
                 + max(|d-py|,|e-py|)^2.                       (9)

Both follow by optimizing each independent coordinate on its closed interval.
All inputs and comparisons in (9) are rational. Induction from the leaves
through the split rules proves the cover lemma. Shared subrectangle boundaries
cause no problem because each leaf conclusion holds on its entire closed box.

The smallest strictly positive core-witness squared reserve in this certificate
is

    673110163827 / 400000000000000.

The replay recomputes this minimum; it is not an unchecked assertion in the
certificate. There are no numerical interval-library calls or floating-point
comparisons in the checker. The exact regeneration mode uses the same rational
predicates to construct the finite cover, and replay checks it afresh.

For an actual other unit center, (2) rules out every outside leaf and
Sections 2--3 rule out every core-witness leaf. The cover consequently yields

    every center of a unit other than V,A,D,B,C belongs to E union S.    (10)

## 5. Three diameter bounds complete the whole physical capacity proof

Split the southern band at its exact midpoint x=-3/8:

    S_left  = [-1,-3/8] x [-M,-3/4],
    S_right = [-3/8,1/4] x [-M,-3/4].                        (11)

The squared diagonal of E is

    (91/60-13/10)^2 + (7/10+1/5)^2
      = 617/720 < 1.

Both southern rectangles have squared diagonal

    (5/8)^2 + (91/60-3/4)^2
      = 14089/14400 = 1-311/14400 < 1.                     (12)

Every two points in one of these rectangles have distance strictly less than
one. By center separation, each rectangle therefore contains centers of at
most one actual unit. One may assign a point on x=-3/8 to the left rectangle;
any overlaps are harmless because a deterministic assignment still gives an
injection from the other units to the three labels E,S_left,S_right.

There are at most three units other than the named five, hence at most eight
units in total. This proves the theorem at its full stated physical scope.
It is stronger than a three-extra obstruction with fixed N: it already counts
N among the only three available remaining center slots.

## 6. Concrete reproducibility and remaining original-row obligation

Run from the repository root:

    python scripts/n9_five_core_capacity.py
    python scripts/n9_five_core_capacity.py --regenerate

The replay checks every rational leaf, all tree coverage, the radius comparison,
the three rectangle capacities and the exact strict reserve. Its reported
mathematical result is conditional on (1). It expressly reports that the
original D02 row is **not** closed and that Lean verification is not claimed.

To turn this into a whole Type II A-only branch exclusion, prove that every
solution of the original full graph/contact/force/torque/circle system in that
branch, after an allowed common orthogonal coordinate change, satisfies (1),
or cover the other surviving domains by additional certified center covers.
An isolated numerical root does not establish that universal entry theorem.
In particular no uniqueness or exhaustive algebraic isolation is inferred
from the exploration that suggested the reference table.

This source does not modify any original coarse or fine checkbox. It supplies
a compact exact physical completion certificate, including an open region of
poses around the suggested root, and a polynomial-only robust exclusion step
for eventual ordinary-kernel Lean replay. Independent source audit, the global
algebraic entry theorem and compiled certificate soundness remain separate.

## 7. Stronger closed neighborhood: vertex errors up to 2/25

The same five-core physical conclusion also holds with every bound in (1)
enlarged from 1/25 to **2/25**. This stronger version is useful for proving
entry from coarse real-algebraic interval boxes. It uses the same twenty exact
reference points and the same incircle/convex-witness argument, with witnesses
at t=i/16, s=j/16 for 0<=i,j<=16.

Use the three rectangles

    E'  = [13/10,M] x [0,3/4],
    SL' = [-49/50,-17/50] x [-297/200,-18/25],
    SR' = [-7/20,23/100] x [-M,-18/25].                   (13)

They have squared diagonals, respectively,

    1097/1800, 39793/40000, 87397/90000,

all strictly less than one. The two southern boxes overlap in their horizontal
intervals; this is intentional and only enlarges their union. As in Section 5,
a deterministic assignment from centers to covering rectangles gives at most
three other units.

The stronger cover is in

    certificates/d02_type_ii_a_only_five_core_capacity_wide.json.

Its **549 nodes** comprise 137 splits and **412 leaves**: 135 core-witness
exclusions, 33 disk exclusions, 14 eastern-cap leaves, 125 left-southern leaves
and 105 right-southern leaves. Its maximum depth is 12. The minimum strict
core-witness squared reserve is

    6434357519 / 368640000000000.

Every core leaf proves distance strictly less than **21/50**, since
21/50+2/25=1/2. The radius and convexity arguments are otherwise unchanged.
Its polynomial-only robust step is

    100|u|^2 + 525|v|^2 - 84|u+v|^2 = |4u-21v|^2 >= 0,
    100*(441/2500) + 525*(4/625) = 21 = 84*(1/4).       (14)

Thus nominal squared distance <441/2500 and actual witness-error squared
distance <=4/625 imply actual squared distance <1/4. All closed error,
circle, cap and box-splitting endpoints remain covered.

Replay or regenerate the stronger version with

    python scripts/n9_five_core_capacity.py research/nine/certificates/d02_type_ii_a_only_five_core_capacity_wide.json
    python scripts/n9_five_core_capacity.py research/nine/certificates/d02_type_ii_a_only_five_core_capacity_wide.json --regenerate

The checker preserves the original version-1 certificate and handles this
version-2 profile with its exact new error bound, sixteenth-grid witnesses and
three capacity rectangles. Its cover induction and every numerical predicate
remain rational. Enlarging the physical neighborhood does not prove the missing
universal algebraic entry theorem or change an original roadmap flag.

## 8. Direct algebraic-box interface, without a uniform perturbation ball

An algebraic interval proof may enclose the twenty actual vertices more sharply
in different coordinate directions than in a single Euclidean error radius.
The checker consequently exports `verify_actual_vertex_boxes`. Its input is
five rows of four vertex boxes, each given by exact closed rational x/y
intervals. Its success remains conditional on the actual physical vertices
belonging to those intervals; it does not assert that an arbitrary polynomial
branch has entered them.

At a spatial core leaf C=[a,b] x [d,e], form the actual convex witness q by
the same nonnegative weights used by that leaf. Weighted interval endpoints
give an enclosure q in [l,h] x [m,n]. The exact sufficient exclusion is

    max(|a-h|,|b-l|)^2 + max(|d-n|,|e-m|)^2 < 1/4.       (15)

This is the maximum squared distance over the product of the two independent
closed rectangles. Hence every c in C is at distance strictly less than one
half from that actual point q in the unchanged core square, contradicting (3).
The implication requires no nominal reference-point error estimate at all.
Every non-core leaf keeps its previously checked disk/cap conclusion. If (15)
holds at every core leaf, the same three-cap pigeonhole proof excludes nine
units throughout that entire actual-vertex interval family.

For repeated algebraic boxes, `prepare_actual_vertex_box_check` replays the
spatial certificate once and caches its exact leaves. The public helper checks
that any supplied cache is exactly the one belonging to the fully replayed
certificate; an empty, edited or mismatched cache is rejected. Cached keys
retain the complete serialized certificate, rather than trusting an external
hash or a claimed leaf count. A failed inequality reports an unproved leaf and
never asserts either feasibility or infeasibility of the original system.

This direct interface is useful for a future **complete** rational subdivision:
each algebraic leaf can end in a scalar contradiction or a verified physical
center-capacity exclusion, instead of requiring a uniqueness theorem or a
tight interval around one numerical root. The global algebraic subdivision
must still cover the entire stated original branch and retain its real physical
entry conditions. No such universal subdivision is claimed by this interface.

## 9. Broader shifted-reference cover with three disk caps

A third certificate gives a substantially broader physical exit, particularly
near the beta=pi/4 limiting face of the algebraic system. It uses **different
exact reference points**, in the same O-centered orthonormal frame. Every
ordered pair in this table is again divided by 10,000,000.

| Actual core square | Reference 0 | Reference 1 | Reference 2 | Reference 3 |
| --- | --- | --- | --- | --- |
| V | (6581556,5566049) | (13129292,13124076) | (5571265,19671810) | (-976471,12113784) |
| A | (-10819389,1979293) | (-819389,1979293) | (-819389,11979293) | (-10819389,11979293) |
| D | (9144046,5782826) | (9979336,-4180608) | (15901,-5015898) | (-819389,4947536) |
| B | (-6335263,-3922856) | (-14297092,-9973136) | (-20347373,-2011306) | (-12385543,4038974) |
| C | (12671851,-3199450) | (16112473,-12583432) | (6728491,-16024054) | (3287869,-6640073) |

**Third physical theorem.** The same capacity-eight conclusion holds whenever
all twenty actual paired vertex errors from this new table are at most
**3/25**. The new table was chosen to span two exploratory candidate poses;
its exact meaning is only the literal rational data above. No existence,
uniqueness or feasibility assertion about either exploratory pose enters the
theorem.

Replace the rectangles by the three closed disks of common radius 12/25
with centers

    (10/7,9/25), (-29/50,-21/20), (-3/25,-31/25).          (16)

Every two points in one such disk have distance at most 24/25<1, by the
triangle inequality. Their common squared diameter is 576/625. Thus each
disk has actual-center capacity at most one, with no need to partition the
disks into disjoint regions.

The certificate is

    certificates/d02_type_ii_a_only_five_core_capacity_midpoint_balls.json.

Its **281 nodes** comprise 70 splits and **211 leaves**: 122 core-witness
exclusions, 18 disk-boundary exclusions, and respectively 9,44,18 leaves in
the three capacity disks (16). Its maximum depth is 9. Witness parameters are
i/16,j/16. Every core leaf proves nominal distance strictly below 19/50;
adding the allowed 3/25 witness error gives strict actual distance below one
half. The minimum exact strict core-witness squared reserve is

    152092123147 / 90000000000000.

The new capacity-leaf predicate merely checks the maximum squared distance
from its whole closed rectangle to the relevant disk center against
(12/25)^2. Formula (9) computes that maximum exactly. All split, physical
incircle and convexity arguments in Sections 2--4 therefore apply unchanged.

For a polynomial-only robust-distance proof one may use

    150|u|^2+475|v|^2-114|u+v|^2=|6u-19v|^2>=0,
    150*(361/2500)+475*(9/625)=57/2=114*(1/4).            (17)

The strict nominal squared-distance bound and closed error bound imply
actual squared distance strictly below one quarter. Every circle, error,
capacity-disk and spatial splitting boundary is retained.

The same direct-vertex-box interface of Section 8 accepts this version-3
certificate. Consequently an algebraic interval leaf may use (15) directly
instead of proving the twenty radius-3/25 error bounds. The old two covers
remain available; no claimed inclusion of their entire error neighborhoods
in the new one is needed.

Exact replay and all-rational regeneration are:

    python scripts/n9_five_core_capacity.py research/nine/certificates/d02_type_ii_a_only_five_core_capacity_midpoint_balls.json
    python scripts/n9_five_core_capacity.py research/nine/certificates/d02_type_ii_a_only_five_core_capacity_midpoint_balls.json --regenerate

This larger physical neighborhood still supplies a **conditional completion
exclusion**. A complete original algebraic-domain cover, compiled Lean replay
and any original fine/coarse parent closure remain separate obligations.

## 10. Additional exact capacity neighborhoods along the candidate branch

Two additional version-4 certificates use the same geometric soundness theorem
and exact rational subdivision. Their references are specified completely by
their twenty integer coordinate pairs and common denominator 10,000,000 in the
listed JSON files. Their names record only where the exploratory reference
poses were suggested; they are **not** theorems about an entire half-angle
interval or assertions that the reference poses solve every original equation.

| Certificate in `certificates/` | Closed vertex error | Nodes / leaves | Maximum depth |
| --- | --- | --- | --- |
| `d02_type_ii_a_only_five_core_capacity_curve_45.json` | 3/25 | 285 / 214 | 8 |
| `d02_type_ii_a_only_five_core_capacity_curve_47.json` | 1/10 | 241 / 181 | 7 |

Each supplies the following actual physical theorem: any packing in the target
disk whose five named actual squares satisfy the twenty corresponding closed
vertex-error inequalities has at most eight units in total. As before, N and
all completion squares have arbitrary independent orientations and contacts.

All six capacity disks have radius 49/100, so each has diameter 49/50<1
and squared diameter 2401/2500. Their exact centers are:

| Certificate | First center | Second center | Third center |
| --- | --- | --- | --- |
| curve_45 | (1395/1000,406/1000) | (-543/1000,-1023/1000) | (-58/1000,-1253/1000) |
| curve_47 | (1383/1000,440/1000) | (-494/1000,-1056/1000) | (-21/1000,-1262/1000) |

The curve_45 certificate has 126 strict core-witness leaves, 32 outside leaves
and 7+31+18 capacity-disk leaves. Its minimum strict squared core-witness
reserve is 233546588008231/115200000000000000. The curve_47 certificate
has 116 strict core-witness leaves, 29 outside leaves and 8+21+7 capacity-disk
leaves. Its minimum reserve is 880480547723/5760000000000000.

Version 4 generalizes only the finite data: it explicitly supplies the three
rational disk centers/radii, the rational error bound and the witness-grid
denominator. The checker requires exactly three disks, each with positive
radius strictly below one half, and an error bound strictly between zero and
one half. It then checks the same complete subdivision and strict witness
inequalities. A caller cannot certify a fourth capacity region or a disk with
diameter at least one merely by editing the data. For the two concrete files
the witness grid is again i/16,j/16.

The global original-case contractor may use the union of these conditional
theorems and the three preceding profiles. Each algebraic leaf must prove the
actual vertex enclosure for at least one profile, either via its explicit
closed error balls or through the direct interval predicate (15). No assertion
that a sampled continuation exhausts the original solution set is needed or
permitted. These additional neighborhoods are geometric exits for a future
complete exact parameter cover, not replacements for that cover.

For a contractor whose vertex intervals already have dyadic integer endpoints,
`verify_actual_vertex_dyadic_boxes` implements exactly (15) with integer
arithmetic. An input integer z denotes z/2^P for the supplied precision P.
The routine takes a common positive denominator D for those weighted vertex
intervals and the spatial leaf endpoints. After exact scaling, it checks

    D^2-4*(dx^2+dy^2)>0,

where dx,dy are the maximum absolute coordinate differences of the two scaled
closed rectangles. This is equivalent to (15), with no rounding. The cache
retains the complete certificate and the precision, and the spatial data are
fully replayed before caching. This implementation avoids repeated rational
normalization in a large global parameter subdivision; it proves precisely the
same conditional geometric implication as the Fraction-based interface.
