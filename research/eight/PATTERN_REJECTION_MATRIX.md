# Actual exclusions and remaining cases for unrestricted eight-square packing

**Scope and purpose.** All eight squares are independently oriented unit
squares with pairwise disjoint **open interiors**, packed into a disk
centered at zero. Work at the proved rational search ceiling

    q=R^2 <= q_plus=9789/2500 <2257/576<98/25<4.

The existing exact construction shows every radius minimizer can be
examined in this range. The central-square theorem
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md guarantees exactly one square C
whose open interior contains zero.

This is a **pattern rejection ledger**, not a claim of the missing
unrestricted sharp inequality R8>=Rhat. Every row below preserves
its geometric hypotheses. 'Beyond a central side' means a **whole**
square is contained in the indicated outward half-plane because
of a valid central-owned support separator; it does NOT merely
mean its center lies in that half-plane.

## 1. Rejections that already have hand proofs

| Proposed pattern | Verdict at q<=q_plus | Exact reason |
| --- | --- | --- |
| Four squares anywhere in one closed half-disk through zero | **Impossible** | Reflect all four to get eight exterior squares and contradict the analytic central-square theorem; HUMAN_CENTRAL_COMPACTNESS.md section 1 |
| Four squares beyond any one central side | **Impossible** | A central side has positive signed distance h from zero, so its cap is contained in a forbidden half-disk |
| Three squares beyond one central side and two beyond its opposite | **Impossible** | Orientation-free three- and two-square cap theorems require q>=2257/576; HUMAN_OPPOSITE_CAP_OCCUPANCY.md |
| All seven noncentral squares have a common frame (central square arbitrary) | **Impossible** | The exact seven-parallel-exterior theorem gives q>=2257/576; HUMAN_SEVEN_EXTERIOR_PARALLEL.md |
| Four squares in one sequential straight separating-axis chain | **Impossible** | The arbitrary-frame straight-chain theorem gives R^2>=(4^2+1)/4=17/4>4; HUMAN_CYCLE_ANALYSIS.md section 7 |
| An actual-contact cycle with 3--6 vertices, all of whose centers have norm >=1 | **Impossible** | Private outer-center rays make it the full induced outer cycle; its winding would enclose at least two other units, contradicting radial escape; HUMAN_OUTER_GRAPH_REDUCTION.md |
| The two neighbors on opposite central sides touch one another | **Impossible** | Their center distance is >=2, whereas touching unit squares have center distance <=sqrt(2); see section 3 below |
| Sevenfold rotationally symmetric seven-square outer ring below R=2 | **Impossible** | Whole-angle separating-axis and containment argument; HUMAN_SEVENFOLD_RING_BOUND.md |
| Three square centers of norm >=1 in an angular sector of width pi/2+1/40 | **Impossible** | Sharp orientation-independent sector bound; HUMAN_OUTER_QUADRANT_CAPACITY.md |
| A diameter crosses only the open central square, with all other seven wholly to its two sides | **Impossible** | Each closed half-disk holds at most three whole squares, so seven cannot be divided across both sides; HUMAN_CENTRAL_COMPACTNESS.md section 2 |

The first row is **stronger** than the independent slice proof of
HUMAN_FOUR_SQUARE_CAP_SLICE.md, which by itself only excludes
four units in the offset cap h>=1/100. There is **no surviving
h<1/100 exception** once the analytic semicircle theorem is used.

The six-outer-cycle rejection concerns the actual graph induced
by **centers of norm at least one**. It does not say an exterior
cycle containing a noncentral square with center norm <1 is
impossible: such cycles occur and must be retained.

## 2. New exact quantitative pruning for opposite central-side counts

Fix one signed side normal n of C. Write

    t=n dot p_C,       -1/2<t<1/2,
    h_plus=1/2+t,     h_minus=1/2-t,               (1)

so the positive and negative central side lines have distances
h_plus,h_minus from zero, with h_plus+h_minus=1.
Let N_plus,N_minus count **distinct whole exterior squares**
lying beyond those central-owned support lines.

**Proposition (a complete side-pair pruning rule).**
At q<=q_plus:

1. If N_plus>=3, then h_plus<3/10 and t<-1/5.
   Necessarily N_minus<=1.
2. If N_minus>=3, the reflected conclusion holds.
3. If N_plus>=2 and N_minus>=2, then

       |t| <=sqrt(q-1)-3/2 <5/24.                 (2)

4. Every N_plus,N_minus is at most three. Consequently,
   the only *cardinality* pairs surviving these
   side-local restrictions are

       (0..3,0..3) except
       (3,2), (3,3), (2,3),

   with (3,1),(1,3) allowed only if the central
   side coordinate satisfies the offset restriction
   in (1), and pairs (2,2) forcing (2).

These are **necessary conditions**, not claims that every
listed pair is geometrically attainable or compatible with
the seven other exterior squares.

**Hand proof.** Four is excluded by section 1.
Suppose N_plus>=3 and put h=h_plus.
The sharp three-square cap theorem gives, when
0<=h<=1/3,

    q>=(1+h)^2+9/4.                                (3)

If h>=1/3, the smaller cap at h=1/3 would
already require q>=145/36>4, impossible.
Thus the actual h lies below 1/3 and (3) applies.
If h>=3/10, (3) would give
q>=169/100+9/4=197/50=3.94>q_plus.
Therefore h<3/10, yielding t<-1/5.

If two more squares lay beyond the opposite side,
the three-square cap and the two-square cap for
h_minus=1-h in (2/3,1) give

    q>=max[(1+h)^2+9/4, (2-h)^2+1].

The first bound strictly increases with h;
the second strictly decreases. Their
intersection occurs at h=7/24, where both
equal 2257/576>q_plus. Thus N_minus<=1.
Reflection proves the symmetrical case.

Now assume at least two squares are served by
both opposite sides. Choose the side whose
distance from zero is larger, h_big=1/2+|t|.
It belongs to [1/2,1), inside the interval
[2/5,1] of HUMAN_EXTENDED_TWO_SQUARE_CAP.md.
The two-square cap theorem yields

    q>=(1+h_big)^2+1
      =(3/2+|t|)^2+1.

Rearranging gives the first inequality in (2).
For the rational strict upper bound, if
|t|>=5/24 then

    q>=(3/2+5/24)^2+1
      =(41/24)^2+1
      =2257/576>q_plus,

a contradiction. This proves (2) and all
the cardinality assertions. QED.

Notice that side-cap populations on **perpendicular**
central sides can share a square that is beyond
both central sides. The counts N_plus,N_minus
are only for *opposite* caps; those caps are
disjoint, so the comparison above uses truly
distinct squares. No exclusive global assignment
of the seven exterior squares to four sides
is being presumed.

## 3. Another exact forbidden local contact pattern

Let A and B be two distinct unit squares wholly
separated from C beyond its opposite sides
along n,-n. Their support inequalities add to

    n dot(p_A-p_B)
      >=h_A(n)+2*h_C(n)+h_B(n)>=2,

since each centered unit square has
support half-width at least 1/2.
Consequently |p_A-p_B|>=2.

But if A and B actually touched at z,
their centers would satisfy

    |p_A-p_B|<=|p_A-z|+|z-p_B|
             <=1/sqrt(2)+1/sqrt(2)=sqrt(2)<2.

Contradiction. This excludes a triangle
C--A--B--C whose two central contact
directions are opposite. It does **not**
exclude a four-vertex cycle C--A--T--B--C;
the exact candidate has such cycles.

## 4. Surviving branches we must NOT erase

| Case | Why it remains |
| --- | --- |
| Seven exterior squares form a full actual-contact ring, with central spokes | The sharp five-corner construction actually realizes this, at exactly Rhat; ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md |
| A noncentral exterior square has center norm <1 | The original tilted candidate and rational seven-ring examples contain this possibility |
| Central square with actual degree 3 or 4 | ANALYTIC_SHARP_FOUR_CENTRAL_CONTACTS.md constructs a sharp-family packing with four central neighbors |
| One exterior orientation differs from six mutually parallel ones | The seven-*parallel*-exterior theorem does not treat this case; HUMAN_ONE_ROTATED_QUADRANT_CAPACITY.md treats only its quadrant-cell subcase |
| Three squares beyond one central side and one beyond the opposite | The 3+2 cap bound does not exclude 3+1; remaining squares may use side or corner-owned separators |
| Two squares beyond each of two opposite sides | Feasible by side bounds when C is sufficiently centered; the global interaction with the remaining squares is unresolved |
| Corner-separated exterior squares, or contacts with zero stress weight | A center-side occupancy number does not classify their actual separating axes |
| Seven-outer-center paths joined through inner attachments | Not covered by the full-ring argument; contact graph analyses retain these branches |

## 5. Next exact proof obligations, in priority order

The **side-count** branching is now genuinely finite:
each side has capacity 0,1,2,3; any 3 on a side
has at most 1 opposite; any 2+2 opposite
requires |n dot p_C|<5/24.

But it is **not an exhaustive geometric classification**
of the seven exterior units because corner-owned
separators may bypass all four central side counts,
and adjacent-side memberships can overlap.

The next high-value hand theorem would show that
each surviving side-count/corner-exception combination
either supplies the coherent five-corner projected
inequalities or obeys a *strictly stronger*
radius bound. For the seven-outer actual ring,
one must retain the full central square:
RATIONAL_SEVEN_EXTERIOR_CONTACT_CYCLE.md and
HUMAN_RATIONAL_RING_POCKET_AREA.md demonstrate
that a winding seven-ring alone can be smaller
than Rhat but may lack room for the central
unit square.

**Not proved:** the unrestricted reverse inequality
R8>=Rhat. This ledger is intended to prevent
known-impossible patterns being revisited and
known-feasible equality configurations being
accidentally excluded.


## 6. New orthogonal corner-cap rejection: opposite double-side assignments vanish

HUMAN_SHARP_DOUBLE_CORNER_CAP.md proves the sharp
one-square arbitrary-orientation inequality

    S subset D_R intersection {x>=h_x, y>=h_y},
    h_x,h_y>=0
        => R^2 >=(h_x+1)^2+(h_y+1)^2.                  (13)

Equality requires the axis-parallel unit
square resting on both lines. The proof uses
two **actual** far-corner vertices of a
rotated square, one positive convex weighting,
and the exactly nonnegative identity

    alpha*|V_top|^2+(1-alpha)*|V_right|^2
          -(h_x+1)^2-(h_y+1)^2
      =[2*h_x*(1-c)*(1-s)
          +s*(1-s)+c^2*(1-c)]/c >=0,

where c=cos(theta), s=sin(theta) with
0<=theta<=pi/4, and
alpha=(1-s)/c in (0,1].
A reflection covers negative orientations.

For the central square C centered at (a,b)
in its own side frame, any **double-side**
status in the stated corner requires:

    RU: q>=(3/2+a)^2+(3/2+b)^2,
    RD: q>=(3/2+a)^2+(3/2-b)^2,
    LU: q>=(3/2-a)^2+(3/2+b)^2,
    LD: q>=(3/2-a)^2+(3/2-b)^2.                (14)

At q<=q_plus<9/2, the **opposite pairs**
RU with LD and RD with LU are impossible:
averaging the two requirements gives
q>=9/2+a^2+b^2>q_plus.

Consequently **at most TWO** of the
four double-side statuses can occur,
and if two occur they must be **adjacent
types sharing a signed central side**.
Each individual double type has capacity
one by HUMAN_ORIGIN_SECTOR_REPLICATION.md.

There is a stronger mixed-pattern rejection:
if RU and RD both occur, (14) implies

    q>=(3/2+a)^2+(3/2+|b|)^2
      >=(3/2+a)^2+9/4,

which forces a<-5/24 at the sharp search
ceiling. But any 2+2 population on right
and left central sides forces |a|<5/24
by section 2. Therefore **RU and RD
cannot coexist with two whole left-cap
squares**. All reflected/rotated versions
follow. Two double statuses on one side
force that opposite side population <=1.

Each double type also requires a specific
central-center diagonal displacement,
for example

    RU => a+b<-487/2500,
    RD => a-b<-487/2500,
    LU => -a+b<-487/2500,
    LD => -a-b<-487/2500.                       (15)

If |a|,|b|<=1/10, no double type can
occur at all: each corner cap has two
offsets >=2/5 and (13) would require
q>=2*(7/5)^2=98/25>q_plus.

These rules reject **complete geometric
status patterns**, not merely new
radius estimates in a conditional
candidate orientation family.
They do **not** exclude the genuine
seven-outer contact ring or the central
degree-four equality representative.


## 7. A triple side blocks every opposite-side corner cap

Theorem 5 of HUMAN_SHARP_DOUBLE_CORNER_CAP.md
gives a new **joint count/status** exclusion
not encoded by the older 3+2 cap theorem.

If a side n of the central square serves
three whole unit squares, its offset h
satisfies the strictly stronger rational
bound

    0<h<7/24,                                      (16)

because the three-square cap inequality at
h=7/24 is already
q>=2257/576>9789/2500.
The *opposite* central side has offset
1-h>17/24. Any square simultaneously
served by that opposite side and one
perpendicular side would fall in a
perpendicular corner cap whose sharp
minimum squared radius is strictly
greater than

    (41/24)^2+1=2257/576>q_plus.

Hence the opposite side can contain
**only single-side statuses**; no
perpendicular double-side assignment
is permitted, even when its total
population is just one. In notation:

| Triple side | Additional impossible statuses |
| --- | --- |
| R serves 3 | LU, LD |
| L serves 3 | RU, RD |
| U serves 3 | RD, LD |
| D serves 3 | RU, LU |

The same principle applies to *any*
central side at offset at least 17/24,
whether or not the other side serves a
triple: that distant side cannot
participate in any adjacent double-side
status.

Combined with the opposite-double ban
and adjacent-double/2+2 prohibition of
section 6, these restrictions cut the
finite status enumeration further.
They do not prohibit the one opposite
**single-side** square in the 3+1
profile, nor corner-only exceptions.


## 8. The surviving far-side unit is forced into a central lane

HUMAN_DISTANT_SIDE_TRANSVERSE_LANE.md adds a
whole-orientation geometric restriction
**inside** the surviving 3+1 branch.

Suppose a central side lies at signed
distance h>=17/24 from the disk origin.
At q<=q_plus it can serve **at most one**
whole exterior square (by the
two-square cap bound). If it serves
one S, the exact one-square cap
center-envelope theorem gives

    (1+h)^2+(|y_S|+1/2)^2<=q
       <2257/576,

where y_S is S's center coordinate
parallel to that side. Because
h>=17/24 this forces

    |y_S|<1/2.

The projected vertical half-width of
any unit square is at least 1/2,
so S's *open interior* crosses the
diameter perpendicular to the side.
The sharp corner-cap theorem also
prohibits S from serving another
adjacent central side: that would
require q>(41/24)^2+1.

Consequently every **3+1** central
side pattern has a uniquely constrained
opposite singleton, if present:
it is a **single-side** status,
its transverse center coordinate
lies strictly between -1/2 and 1/2,
and its open interior intersects
the perpendicular diameter through
the origin. No common frame or
circle contact is being assumed.

This supplies a geometrically testable
placement lane for the remaining four
or five squares, rather than
incorrectly discarding the 3+1 case.


## 6. Stronger fine-status and continuous-offset pruning (next continuation)

TRIPLE_DOUBLE_STATUS_PRUNING.md now integrates the already
proved **triple-side vs opposite double-side**
incompatibility as an actual Boolean status filter:
if R serves three, statuses LU and LD are impossible;
if L serves three, RU,RD impossible; if U serves
three, RD,LD impossible; if D serves three, RU,LU
impossible. With the other exact filters above, the
number of labeled twelve-status **symbolic**
assignments drops from 4,566,800 to
**3,995,040**, eliminating 571,760 further words.
The unlabeled nonnegative integer multiplicity
vectors drop from 2,060 to **1,656**.
The file supplies a factorial coefficient
formula, not a numerical packing solver.

That note also strengthens the central-center
diagonal displacement forced by a double-corner
square. In central frame coordinates (a,b),

    RU => a+b< -1/5,
    RD => a-b< -1/5,
    LU => -a+b< -1/5,
    LD => -a-b< -1/5.

Two adjacent double-corner statuses sharing a
central side at positive distance h require
either **h<1/4**, or the central center's
perpendicular signed coordinate has
absolute value **<1/29**. This dichotomy
comes from the exact one-square corner-cap
inequality and the rational comparison
`52709/13456>9789/2500`. Neither option is
claimed impossible in every eight-square
packing.

HUMAN_ALL_SIDE_OFFSET_INTERVALS.md supplies
a complete **one-axis signed center interval**
for each of the eight surviving opposite-side
count profiles. If a positive side serves
at least 1, 2, or 3 entire exterior squares,
respectively, its signed center coordinate
t=n dot p_C must satisfy

    t<83/200,     t<5/24,     t< -5/24.

The first bound is from a new elementary
one-square whole-cap vertex inequality
`R^2>=(h+1)^2+1/4`. The second uses the
sharp two-square cap theorem at h>=2/5,
and for h<2/5 follows trivially from
the already established analytic lower
R8>sqrt(2)+1/2. The triple bound is the
original sharp three-square cap inequality.
Reflecting gives the opposite-side lower
bounds. In particular the **3+1 branch**
has `-83/200<t<-5/24` and the
**2+2 branch** has `|t|<5/24`.

These are **necessary continuous-domain
restrictions**, and by themselves they
do not remove any more of the 31 coarse
count profiles. Their utility is to shrink
the signed central-center intervals before
examining the rotated-corner exceptions
and the remaining neighboring-square
separator choices.


## 7. Perpendicular triple sides must share a double if their offsets are not too small

**New continuous case exclusion** from
HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md:

Suppose two perpendicular sides of the
unique central square, e.g. R and U,
each serve three whole exterior squares.
If both of their outward offsets from
zero satisfy

    h_R>=11/50,      h_U>=11/50,

then one actual exterior square must
have the **RU double-side status**.
The proof uses a new orientation-free
three-square mid-cap chord theorem:
each triple supplies a whole square
in its common *positive* origin quadrant;
that quadrant has capacity one, so
the two selected squares coincide.

In particular the completely
single-side S1=(3+0,3+1) count type
cannot occur with the two triple-side
central projections both >=-7/25.
After naming the triples R and U, it
must satisfy

    min(a,b)<-7/25.

This eliminates an actual nonempty
continuous subset of S1 rather than
merely an arrangement of discrete
separator labels. S1 with a smaller
triple offset is still open.

Moreover when an offset h<11/50 has
an opposite whole-square singleton,
that opposite side is at distance
>39/50 and the singleton center's
transverse coordinate is strictly
less than 3/8 in absolute value.
These conditions must not be
misread as a global S1 exclusion
or as assigning a corner-only
square to a whole origin quadrant.
