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


## 7. New radial-ray pattern eliminations within all triple-side branches

HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md now proves that
any central side with **three** whole exterior
square members has at least one **single-side**
member crossing that side's outward origin
cardinal ray through its **open interior**.
Otherwise all three entire squares would be
confined to the two adjacent origin quadrants,
each of capacity one. This holds at *every*
positive cap offset and for arbitrary frames;
it is stronger at small offsets than requiring
the whole-quadrant witness theorem, which has
its own offset threshold.

In the adjacent-double D2 case RU+RD with
R count exactly three, the third R square
**must be the positive-x-ray crosser**;
the two double members are wholly above
and below the axis and cannot cross it.
This clears every placement subcase
where the third R member avoids that
diameter, independently of its frame.

HUMAN_OPPOSITE_TRIPLE_DIAMETER_CHAIN.md
adds the opposite-side singleton. Every
3+1 population pair has *two distinct
single-side* exterior members crossing
the opposite cardinal rays, with the
central square's diameter interval between
them. The far-side singleton crosses its
own ray because its outward cap offset
is >17/24, forcing its transverse center
coordinate to have absolute value <1/2.
Thus one may discard all 3+1 placements
where the distant singleton lies **wholly
inside either adjacent origin quadrant**,
or where the three-square near cap never
crosses the opposite positive cardinal ray.

HUMAN_SATURATED_TYPE_A_RAY_ROUTING.md then
shows saturated Type A (3+1,3+1) forces
**four distinct single-side square open
interiors** across all four cardinal rays,
plus its RU double square entirely inside
the origin NE quadrant. If both triple
offsets >=13/60, the other two singles
are wholly in the origin SE and NW
quadrants; these seven roles are fully
determined without common orientations.
If either offset <13/60, the singleton
beyond the opposite distant side has
a strict transverse center lane
|coordinate|<9/25. This gives a complete
high-offset / narrow-lane split of the
saturated Type A branch.

HUMAN_CORNER_ONLY_DOUBLE_RAY_BOUND.md
supplies another exact **conditional
placement exclusion**: a corner-only
own-axis square assigned NE, intersecting
both positive origin cardinal rays through
its open interior, forces

    sqrt(1/2+a)+sqrt(1/2+b)<sqrt(2),

where p_C=(a,b). Thus when a,b>=0
such simultaneous positive-ray wrapping
is impossible. Reflect/rotate for other
corners. This does **not** forbid the
corner-only type itself or an intersection
with only one of its bordering rays.

The purely symbolic **twelve-status
assignment count remains 3,995,040**:
these new theorems reject *continuous
placements inside surviving statuses*,
not further status-label combinations.
Do not report a decreased finite count
without an additional exact status
implication. In particular two squares
of a right cap **can both cross the same
positive ray**; the triple-ray note
includes a fully rational, exactly
disjoint two-square example. Ray
uniqueness is not a proved premise.


## 8. Far 2-square cap polarization (new exact numerical-free placement exclusion)

HUMAN_FAR_TWO_CAP_POLARIZATION.md proves that whenever
two complete squares lie beyond a line of offset
h>=3/5 in the q<=9789/2500 disk, their centers'
**perpendicular** coordinates have strict opposite
signs and magnitudes **greater than 7/25**.
The hand proof bounds the absolute transverse
coordinate by 133/200 and the possible
longitudinal center difference by 8/25.
If one transverse center coordinate had
absolute value <=7/25, the two center
distance squares would obey

    |dp|^2<(189/200)^2+(8/25)^2
           =39817/40000<1,

contradicting disjoint inscribed half-unit disks.

**Direct saturated Type C application.**
For central populations (2+2,2+2) with
one double RU square, the sharp corner
cap theorem forces a+b<-1/5.
Therefore a<-1/10 **or** b<-1/10.
In the first case the two whole L squares
have center y coordinates of opposite
signs and absolute magnitude >7/25;
in the second the two D squares have
center x coordinates similarly polarized.
If both central coordinates are below
-1/10, both cap pairs are polarized.
These are exact necessary location cases,
not a claim that Type C is impossible.

**Saturated Type B application.**
With a 3+1 axis perpendicular to a 2+2
axis, either the central coordinate along
the 2+2 axis lies inside (-1/10,1/10),
or the *farther* cap pair on that axis
has transverse centers of opposite signs
and magnitudes >7/25.
This is another exhaustive real-variable
subcase split for Type B.

These conditions preserve mixed square
frames; opposite center signs do **not**
mean entire-square membership of
corresponding origin quadrants. They
do not yet reduce the symbolic
3,995,040 twelve-status assignment count,
since each remaining status word may
still admit one of the permitted
continuous placements.


## New coupled side-cap / outer-center case elimination (October continuation)

The status-only total is unchanged, but the geometric
branches now have rigorous **outer-center count filters**.

**(i) Two-square cap polarization**
(HUMAN_TWO_CAP_CENTER_SIGN_SPLIT.md).
At q<=9789/2500, two complete unit squares
beyond a side at h>=3/7 must have center
coordinates of strictly **opposite signs**
perpendicular to that side. If h>=1/2
the signs have clearance >1/10, and
both centers have norm >1. In a 2+2
opposite-side count, the farther cap
always has h>=1/2, hence contains
two such outer-center squares.
If the central center component
has |t|<=1/14, both cap pairs
have opposite transverse center signs.

**(ii) Moderate cap with two members cannot
have two inner centers** (the cap-inner-pair
lemma of HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md).
If h>=2/5, any two whole cap squares
cannot both have center norms <1:
otherwise their center projections
on the outward side lie in [9/10,1),
and transverse projections have
absolute value <sqrt(19)/10.
Their squared center distance would
be <77/100<1, contradicting their
disjoint radius-1/2 inscribed disks.
If h>=1/2 **every** cap member is outer.

**(iii) Three whole cap squares cannot all have
inner centers** (HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md).
The center direction of any square with
center norm <1 in a nonnegative cap
lies strictly within 60 degrees of the
cap's outward normal. But two such
centers with distance at least one
have angular gap strictly larger
than 60 degrees. Three cannot fit
within a 120-degree sector. Hence
every triple cap has an outer member.

The corresponding **newly rejected full
subcases** are:

| Macro-status | Outer count and central-position restriction now impossible |
| --- | --- |
| Saturated Type C (2+2,2+2 with one RU double) | **Every k=3 or k=4** (HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md) |
| All-single-side S2=(3+0,2+2) | k=3 if |t_(2+2)|<=1/14 |
| All-single-side S3=(3+1,2+1) | k=3 if the 2-member side has offset h>=2/5 |
| All-single-side S4=(2+1,2+2), containing candidate equality | k=3 if its 2-member side on the 2+1 axis has h>=2/5 |
| The same S4 | k=4 if also |t_(2+2)|<=1/14 |

No equality-bearing S4 type as a **whole**
has been rejected: its surviving geometric
positions and center populations still require
a sharp obstruction. All outer counts here
refer to **center norm >=1**, not circle contact
or the square omitting zero.

**(iv) True radial-ray crossings**
(HUMAN_TRIPLE_CAP_RAY_CROSSER.md and
HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md).
A whole triple cap must have some square
whose *open interior* intersects that side's
outward origin ray. In a two-double RU,RD
common-R triple, it must be the remaining
single-R square. In the fully saturated
Type A pattern, four distinct single-side
squares cross the four cardinal rays;
the double RU square instead lies
entirely in the NE origin quadrant.
This is compulsory geometric routing,
not a demand that those squares' frames
be aligned with the central frame.

These filters shrink genuine continuous
subcases. **They do not change the certified
symbolic twelve-status word total 3,995,040**,
because an eliminated k/offset combination
need not eliminate its parent separator
status word for other positions.


## 9. Two entire Type C / outer-center macro-cases are eliminated

HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md proves, for all orientations,
that the saturated Type C fine-status branch

    RU, R, L, L, U, D, D,
    with four side counts (2,2,2,2),

has **at least five exterior square centers with norm >=1**.
Therefore its intersections with the outer-center
k=3 and k=4 macro-branches in FINITE_PATTERN_TAXONOMY.md
are **impossible**. These are genuine case exclusions,
not just a restriction on a continuous center interval.

A compressed hand proof: the corner RU square itself is
outer, because the 2+2 offset bounds give |a|,|b|<5/24
and its center components exceed 1+a,1+b>19/24, so
its norm squared exceeds 2*(19/24)^2>1.
If a,b<=0, the whole left and lower side pairs have
offset >=1/2, so all four of their distinct centers
have norm >=1; with RU this gives five.

If a>=0,b<0, the right and lower pairs similarly
give four distinct outer centers. The RU corner-cap
inequality a+b<-1/5 and a>-5/24 imply a<1/120,
so the two left-side centers lie in a cap of offset
1/2-a>59/120>2/5. They cannot *both* have norm <1:
if they did, both would have normal center coordinate
in [9/10,1), transverse coordinate absolute value
<sqrt(19)/10, and therefore mutual center distance
squared <1/100+19/25=77/100<1. This contradicts
the two unit-square inscribed disks. Hence the L pair
contributes a fifth distinct outer center.
The case a<0,b>=0 is the perpendicular reflection.
The three cases exhaust a+b<-1/5.

The symbolic count of twelve-status words remains
3,995,040, because k (number of outer center norms)
was not part of those twelve statuses.
The **joint status-by-outer-center** case table,
however, now rejects Type C with k=3 or 4.
All Type C branches k=5,6,7 remain to be treated,
as does the real candidate equality branch
D0/S4. No unrestricted R8>=Rhat proof follows.


## 10. Additional actual status-by-outer-center cells are eliminated

HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md proves a
whole-orientation center-count rule for a
*three-square* outward cap: at least one
member must have center norm >=1. If all
three centers had norms <1, their
projected normal components would all
be >1/2; their polar directions would
lie within an **open 120-degree** sector.
But distinct inner centers of disjoint
unit squares require angular gaps >60
degrees (by the unit inscribed-disk
center separation), so three such
centers cannot fit in that sector.

Combining this with the established
two-square cap-inner-pair theorem
(h>=2/5 guarantees at least one
outer center) and the fact that
a cap of offset h>=1/2 consists
entirely of outer centers gives these
further **genuine k-cell exclusions**
in the all-seven-single-side branches:

| Single-side type | Eliminated k branch | Additional exact central offset hypothesis |
| --- | --- | --- |
| S2=(3+0,2+2) | k=3 | the 2+2 center coordinate has abs <=1/14 |
| S3=(3+1,2+1) | k=3 | the two-member side on the 2+1 axis has offset >=2/5 |
| S4=(2+1,2+2) | k=3 | the two-member side on the 2+1 axis has offset >=2/5 |
| S4=(2+1,2+2) | k=4 | the same two-member side has offset >=2/5, AND the 2+2 axis center coordinate has abs <=1/14 |

The equality candidate is in S4, so these
strictly conditional subcase exclusions do
**not** discard S4 itself; they confine its
low-k configurations to narrower central
offset strips. See the cited note for
the short center-count proofs for each
row and a careful distinction between
*distinct single-side statuses* and
overlapping double memberships.

Together with section 9, Type C/k=3,4
are entirely eliminated, while the
four rows above are eliminated on
specified exact continuous regions.
None of these improvements changes
the old **purely symbolic**
3,995,040 count, because that count
does not encode k or signed offsets.


## 11. Exact full rejection of S2/k=3 and S4/k=3

The newest [HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md)
proves a **six-square angular crowding obstruction** under the actual
eight-square squared-radius ceiling \(9789/2500\):

* two distinct **inner-center** squares wholly beyond a positive
  central side R;
* two further **inner-center** squares wholly beyond the
  perpendicular nearer U side with \(h_U>7/24\);
* two further **outer-center** squares wholly beyond its opposite
  D side, at offset \(1-h_U\).

These six labels cannot coexist for arbitrary square frames.
Four inner-center rays force an R-center radius \(>4/5\) at
polar angle \(<-\arcsin(19/24)\); the two D outer rays occupy
a southern arc of half-angle \(>\arctan(4/3)\).
The inscribed-center distance bound excludes all D rays
within \(\pi/6+1/100\) of that R center, leaving angular
width \(<\pi/4-1/100\), too small for two outer centers
whose angular gap must exceed \(\pi/4-1/500\).

Consequently:

| Exact exclusive-side status / outer-count cell | Verdict |
| --- | --- |
| **S2=(3+0,2+2), k=3** | **Impossible for every central offset** |
| **S4=(2+1,2+2), k=3** | **Impossible for every central offset** |

This **supersedes** the earlier *partial* S2/k=3 and S4/k=3
offset strips, which remain historical, mathematically valid
necessary filters but are no longer the strongest result.
**Do not** promote the six-square forbidden pattern to
other D1/D2 statuses without proving four **distinct inner**
cap labels and the two **distinct outer** opposite-cap labels.

The entire S2 and S4 status classes are not excluded:
S2/k=4,5,6 and S4/k=4,5,6,7 remain, including the
explicit candidate's S4/k=7 equality. This does not
establish the unrestricted \(R_8\ge\widehat R\).


## 12. Entire high-offset region of the remaining S3/k=3 branch is impossible

[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
supplies a new **genuine continuous-region exclusion** for
four **distinct inner-center whole-cap members** (two R,
two U) together with one additional R **outer-center**
whole-cap member. It excludes every such configuration
when \(h_R>17/200\) and \(h_U\ge21/100\), for all
square frames and without any contact premise.

For the exclusive S3=(3+1,2+1), k=3 branch this is an
**unconditional-in-the-remaining-frames** elimination of
the complete strip \(h_U\ge21/100\).
The complementary still-unresolved region obeys
\[
17/200<h_R<13/100,\qquad 17/200<h_U<21/100.
\]

The new
[HUMAN_S3_K3_REMAINING_TWO_LANES.md](HUMAN_S3_K3_REMAINING_TWO_LANES.md)
additionally proves the outer R-center ray must lie in
one of only two open angular intervals
\((-5\pi/36,-2\pi/45)\) or
\((7\pi/36,13\pi/45)\), and the distant L/D
singleton center transversals satisfy
\(|p_L.y|<3/20,\ |p_D.x|<11/32\).

For S1/k=3, when its 3+1 U-triple offset is
\(\ge21/100\), its perpendicular 3+0 R-triple
offset must be \(\le17/200\). This is another
strict **offset subdomain** rejection, not an
elimination of S1/k=3.

The five-square theorem may be applied to other
D1/D2 branches **only if** its two R-inner,
two U-inner and one R-outer witnesses are shown to
be five distinct actual whole-square members.
A shared RU square cannot be counted twice.
No S4 equality is excluded, and no general
\(R_8\ge\widehat R\) proof is claimed.


## 13. Further S2 and S3 continuous region pruning (October 12)

The all-frame
[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
theorem excludes the entire **S3/k=3** subdomain
where the two-member 2+1-side cap has outward offset
\(h_U\ge21/100\). The remaining exact offset region is
\(17/200<h_R<13/100\) and \(17/200<h_U<21/100\).
HUMAN_S3_K3_REMAINING_TWO_LANES.md further splits
the sole R outer center into two disjoint angular sectors
and pins the distant L/D transverse centers.

[HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md](HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md)
and [HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md](HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md)
give the following stronger **joint center-count and
continuous-position exclusions**:

| Actual exclusive S2 center-class hypothesis | Newly forced condition |
| --- | --- |
| Both members of the nearer 2+2 U cap have inner centers | **Exactly k=4** (not k=3 or 5) |
| The same, with R triple offset h_R | **0<h_R<1/10** |
| The same, ordered outer R center rays psi_1<psi_2 | psi_1 in (-pi/4+17/125,-pi/18+1/500), psi_2 in (67/500,7*pi/36) |

In particular S2/k=5 with **both** near-U centers
inner is **fully impossible** (not the entire S2/k=5
class). S2/k=4 with that near-inner pair is
**fully impossible for h_R>=1/10**; its
remaining small-offset interval is still open.

These results depend on inner/outer center norms
and polar geometry, so **do not** reduce the
independent 3,995,040 symbolically admitted
twelve-status labels or the 31 coarse count
profiles. Also do not promote opposite center
transverse signs into whole-quadrant membership:
the actual rotations and mutual separating axes
of the remaining square labels still matter.

The S4 equality-bearing configuration and the
unrestricted \(R_8\ge\widehat R\) proof obligation
remain untouched.


## 14. Revised strict S2/k4 and S3/k3 center-coordinate domains

The newest *arbitrary-frame analytical* pruning supersedes
the earlier weaker S2 \(h_R<1/10\) and S3
\(h_U<21/100\) bounds, under their exact
respective inner/outer center hypotheses.

| Status / actual center subcase | Necessary remaining domain |
| --- | --- |
| Exclusive S2, both near-U cap centers inner | **k=4 exactly**, \(0<h_R<1/20\); R outer center rays have strict opposite signed y; U inner transverse x values are \(<-9/25\) and \(>9/25\); D outer transverse x values are \(<-29/100\) and \(>29/100\) |
| Exclusive S3, k=3 | \(17/200<h_R<13/100\) and \(17/200<h_U<1/5\), with the sole R-outer ray either \(-\pi/9<\psi<-2041/10500\) or \(311/500<\psi<8959/10500\); distant L/D center transverse magnitudes \(<3/20\), \(<13/40\) |

Proof files:
[HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md](HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md),
[HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md](HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md),
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md),
and [HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md).

**Audit guardrail:** the exact rational S2/k4 eight-center
relaxation in RATIONAL_S2_K4_CENTER_RELAXATION.md
passes only its explicitly stated weak radial/center-distance
conditions. Its R1/D2 and D1/D2 outer-center angle gaps are
too small to satisfy HUMAN_STABLE_OUTER_ANGLE.md;
their exact angle tangents are both \(<9/10\), while
\(\tan(\pi/4-1/500)>249/251\). It is **not** an
actual square packing or evidence that the full S2/k4
case is realizable. Stronger center-angle obstructions
might still suffice.

These refinements preserve the S4/k7 exact equality
configuration and do not yet establish
\(R_8\ge\widehat R\).


## 15. An entire S3/k=3 outer-center angular sector is now excluded

The earlier two-sector S3/k=3 center-ray description is
**superseded** by
[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md):
the **whole negative R-outer ray sector** is impossible.
The sole surviving R outer-center ray must obey
\[
\boxed{311/500<\psi<8959/10500.}
\]
The proof iteratively increases the lower inner R
center radius from \(>7/10\) to \(>9/10\) using
actual whole R-cap center projections, then obtains
an exact mixed angular separation contradiction
to the same cap projection. It does not assign
a square frame or physical contact.

Furthermore
[HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md](HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md)
excludes the entire center-sign subdomain
\(x_D\ge0\) for the **far D singleton**:
\[
\boxed{-13/40<x_D<0,\quad y_D<0.}
\]
The angular proof first forces the R-minus inner
center to radius \(>17/20\); every outer D center
on or right of the y axis would then be too close
in center-ray angle for the necessary unit
center separation.

The remaining S3/k3 offset rectangle is unchanged:
\[
17/200<h_R<13/100,\qquad
17/200<h_U<1/5.
\]
No claim of full S3/k3 nonexistence is made.
These are **continuous** geometric exclusions,
not new deletions from the purely symbolic
3,995,040 twelve-status count. The real
S4/k7 candidate equality branch is preserved,
and \(R_8\ge\widehat R\) remains OPEN.


## 16. Entire S3/k=3 outer-count macro-cell eliminated

**This replaces the previous S3/k3 residual
two-offset rectangle and one-positive-ray
survivor descriptions in sections 12–15.**

The arbitrary-frame
[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md)
proves **exclusive S3=(3+1,2+1) with exactly
three outer centers is impossible**, unconditionally
over its allowed central square offsets,
square frames, contacts and pair separators.

The key **new exact center-distance bound** uses
both inner R whole-side square centers.
Their positive-y member must satisfy \(y>49/500\).
The sole outer R square is *R-only* (cannot have
a whole U separator), so its center is below
\(h_U+\sqrt2/2<227/250\).
The previously proved sole positive outer R ray
and universal center radius \(<283/200\)
bound its x-coordinate above by \(230079/200000\).
The two distinct centers then have squared distance
\[
<1-969139759/40000000000,
\]
contradicting the inscribed half-unit disks.
No common frame or actual contact is assumed.

| Exact all-single-side macro-cell | Verdict |
| --- | --- |
| **S3/k=3**, any central offset, all frames | **Impossible** |
| S3/k=4,5,6,7 | Remain unresolved |
| S4/k=7 | Valid known sharp equality realization |

The exclusive D0/S=7 k queue now is
S1 k=3..6; S2 k=4..6; S3 k=4..7;
S4 k=4..7. This is a **joint status/outer-count
rejection**, not a new deletion from the previously
enumerated symbolic 12-status word total.
The global \(R_8\ge\widehat R\)
remains OPEN.


## 17. Complete exclusion of S2 with two inner nearer-2+2 centers

**This supersedes all historical conditional 'S2 near-inner
k=4 h_R<1/20 remains' entries above.**

The exact all-frame
[HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
proves **exclusive S2=(3+0,2+2) is impossible when
both squares on its nearer two-member 2+2 cap
have center norms <1**. It combines the
previous outer-center ray polarity (two R outers,
one R inner, two U inners, two D outers) with:

* two new exact mixed inner/outer angular gap
  lemmas, \(>12/25\) and \(>33/50\) radians;
* an orientation-free proof that the inner R
  ray lies strictly between its two R-outer rays,
  forcing the positive R-outer ray \(>43/100\);
* the near-U positive-x inner-center rectangle
  \(9/25<u_x<31/50,\ 79/100<u_y<47/50\);
* a four-endpoint **analytic concavity bound**
  proving its distance from the positive R-outer
  center has squared norm
  \(<4923651/5000000<1\).

The last contradicts the two actual whole
squares' center separation. This is a complete
continuous subbranch rejection, **not** a
generated numeric classifier.

| Exclusive S2 subcase | Current status |
| --- | --- |
| k=3 (all near-center allocations) | Entirely impossible (older result) |
| **Both nearer U pair centers inner**, any k | **Entirely impossible (new)** |
| k=4, exactly one U outer and one R outer | Remains unresolved |
| k=5,6, at least one U outer | Remains unresolved |

No deletion of the purely symbolic 3,995,040
twelve-status assignments is inferred, since
these inner/outer flags were not in that
symbolic enumeration. The S4/k=7 exact
equality configuration remains valid.
The unrestricted \(R_8\ge\widehat R\)
still requires additional global geometry.


## 18. New far-side two-square outer-center theorem and S2/S4 k=4 offset strip exclusions

[HUMAN_TWO_OUTER_HIGH_CAP.md](HUMAN_TWO_OUTER_HIGH_CAP.md)
proves for **two distinct, arbitrarily oriented
whole unit squares** in the n=8 disk ceiling
that a common outward cap offset
\[
h\ge97/200
\]
forces **both centers to have norm at least one**.
This is stronger than the trivial single-square
cutoff \(h\ge1/2\). If one center were inner,
the sharp one-square cap transverse envelope
and the universal farthest-vertex radius bound
would give the contradictory
\[
|p-q|^2<
199457/200000
=1-543/200000.
\]
The proof is for the *entire* continuous frame
and center domain. All its numerical endpoints
are exact rationals, audited separately in
[verify_two_outer_high_cap.py](verify_two_outer_high_cap.py).

For the **exclusive one-side** status types with
an opposite 2+2 population, write t for the
central center's signed coordinate on that
axis. If \(|t|\le3/200\), both 2+2 caps
are at offsets at least 97/200, and all
**four distinct** squares on that axis have
outer centers. The perpendicular other axis
of S2 or S4 contributes at least one
**different** outer center. Therefore:

| Exact still-open status/outer-count case | New central-coordinate restriction |
| --- | --- |
| S2=(3+0,2+2), k=4 | **\(|t_{2+2}|>3/200\)** |
| S4=(2+1,2+2), k=4 | **\(|t_{2+2}|>3/200\)** |

These are strict **continuous offset subregion
exclusions**, not complete elimination of
S2/k4 or S4/k4 and not new reductions of the
purely combinatorial twelve-status counts.
Do not transfer the **five-distinct-outer**
count to overlapping double-side labels
without proving distinctness separately.
The real S4/k7 equality branch is preserved.

Current stronger parent closures remain:
* S2/k3 and S4/k3 impossible;
* S3/k3 impossible;
* S2's entire **nearer 2+2 both-inner**
  branch impossible.

The unrestricted \(R_8\ge\widehat R\)
remains OPEN.


## 19. Mixed inner/outer two-square cap: exact angular and same-sign exclusion gates

For the **remaining exclusive S2/k=4** case,
the nearer of its opposite 2+2 whole-cap sides
has exactly one inner and one outer center
(the previous both-inner and k=3 branches
are globally eliminated). New all-frame
hand proofs supply the following exact
continuous restrictions:

| Necessary geometric case | Proven bound / rejection |
| --- | --- |
| Any nearer-cap inner/outer pair, h>=7/24 | **Polar center-ray gap >3/4 radians**, HUMAN_MIXED_NEAR_CAP_POLARITY.md |
| Both nearer-cap centers with same **strict** transverse x sign | Inner x magnitude <1/4; outer x magnitude >7/10; outer ray is farther from the +y diameter |
| Same-sign mixed pair with near-cap offset **h>=2/5** | **Impossible**, HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md |
| Same **weak** transverse sign at offset h>=7/24 and both frames within 1/2600 rad of cap-aligned axes | **Impossible**, HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md |
| Opposite transverse signs | Not excluded by these lemmas |
| Same-sign pair in 7/24<h<2/5 with sufficiently oblique frame | Still open; cannot promote the conditional near-axis theorem to full-frame exclusion |

The high-offset sign theorem uses the sharp
arbitrary-frame single-square cap center envelope
to trap a hypothetical same-sign pair in a
rectangle whose **squared center-distance upper
bound** is \(9189/10000<1\).
The near-axis theorem uses centered axis-parallel
inscribed squares of side \(2600/2601\) to derive
the strict radius contradiction
\[
R^2\ge q_++21634201/270608040000>q_+.
\]

These are actual continuous center/frame constraints,
**not** additional eliminations from the purely
symbolic twelve-status word total. They do not
eliminate all S2/k=4, S2, S4/k=7,
D1/D2 or the missing unrestricted
\(R_8\ge\widehat R\).
