# A finite but continuous taxonomy of all n=8 packing patterns

## Status and scope

This note answers what "all patterns" means for the unrestricted
eight-unit-square-in-a-disk problem. Let R8 be the attained least
radius, q_plus=9789/2500, and Rhat the exact five-corner family
radius. The proved construction gives R8<=Rhat<sqrt(q_plus).
We may therefore inspect potential minimizing packings satisfying
R^2<=q_plus<98/25<4.

**Result:** the space has a finite, exact **combinatorial** branch
decomposition, but each surviving branch is a **continuous
semialgebraic feasibility problem** in centers and orientations.
The taxonomy is not a list of all realizable contact graphs,
and no theorem R8>=Rhat is claimed.

An exact full disjunction is given in section 5. Sections 1--4
give a much smaller hand-geometric hierarchy of branches.
Do not confuse the number of occupancy profiles with the
number of geometrically realizable packings.

## 1. Fix the central square

HUMAN_GLOBAL_GEOMETRY_CLOSURE.md proves the unique square
C whose open interior contains zero. By rotating axes, let
C have horizontal and vertical sides, with center
p_C=(a,b), |a|,|b|<1/2. All seven other squares omit
zero in their closed sets.

For any exterior square S, consider all **available**
separating axes of the pair C,S, not merely the one
chosen in a stress proof. A central-owned separator
may place the **whole** square beyond a side of C.
The four signed side labels are R,L,U,D.

There are exactly 12 mutually exclusive pair statuses:

* **One central side (4):** R, L, U, D.
* **Two adjacent central sides (4):** RU,RD,LU,LD.
  Opposite-side membership is impossible: the
  two beyond-side half-planes are disjoint.
* **No central side (4):** own-axis corner separators
  at NE,NW,SE,SW. A square of this kind is called
  corner-separated. HUMAN_STRUCTURAL_LEMMAS.md
  proves that the center and unique separating normal
  lie in the assigned strict corner quadrant.

The one-corner capacity theorem says **at most one**
corner-separated square at each of the four corners.
Thus at most four of the seven are corner-separated,
and **at least three distinct exterior squares have
a genuine central-owned side separator**. A square
with two adjacent side separators is counted twice
in the four side populations but is one actual square.
These statuses are exhaustive regardless of frames:
they follow from the separating-axis theorem.

There are finitely many label assignments of these
12 statuses to the seven exterior squares, but most
assignments violate occupancy or pairwise nonoverlap.
The assignments do not fix centers, frames or contacts.



## 1A. New exact capacity of the four *double-side* statuses

HUMAN_ORIGIN_SECTOR_REPLICATION.md proves the following
stronger necessary condition, using the central-square
theorem and a 90-degree rotational copy argument:

    count(RU),count(RD),count(LU),count(LD) <= 1.         (A)

Indeed two different whole squares each served beyond,
say, both central right and central upper sides would
lie entirely inside the positive origin quadrant.
Rotating the pair by 0,90,180,270 degrees would
create eight interior-disjoint unit squares, none
containing zero in its open interior, contradicting
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md.

This is a true **whole-square** exclusion for every
R^2<=98/25. It is not merely a result about two
center directions occupying the same quadrant.

Consequently each of the four double-side types,
and each of the four corner-only types, can occur
**at most once**. Only the four single-side types
can occur repeatedly (up to three instances
each by semicircle capacity).

The previous 31 coarse side-count profiles
are **not** reduced by (A): all 31 still admit
at least one combinatorial assignment under
these capacity constraints, though many may be
geometrically impossible. The new rule does
prune finer labeled and unlabeled **status
multiplicities**, which a side-count profile
does not record.

For a check on its combinatorial impact:
restrict seven labeled squares to the twelve
statuses, impose one corner-only square
per corner, side counts <=3 and the 3+2
opposite-pair exclusions. Those filters permit
8,551,760 labeled status assignments if
double-side statuses are allowed arbitrary
multiplicity, but **6,663,440** after (A).
These are finite algebraic counts, not
counts of feasible packings. They can be
reproduced from the coefficient expression

    7! * [z^7] (1+z)^4
      * exp(z*(x_R+x_L+x_U+x_D))
      * product_(adjacent i,j) (1+z*x_i*x_j),

retaining only monomials with individual
x exponents <=3 and excluding exponents
(3,2),(2,3),(3,3) for both opposite
pairs. The old count replaces the last
product by exp(z*sum_(adjacent i,j) x_i*x_j).
Each term of the exponential is used
only through degree seven; multiplication
by 7! gives an integer.



## 1B. Sharper pruning: only an adjacent PAIR of double-side statuses can survive

The sharp corner-cap theorem
HUMAN_SHARP_DOUBLE_CORNER_CAP.md strengthens
the preceding sector argument:

* **Opposite double statuses are incompatible:**
  RU+LD and RD+LU are impossible at
  q<=9789/2500.
* Hence of RU,RD,LU,LD, **at most two**
  can be occupied, and if two are present,
  their labels must share a signed central side.
* **Two adjacent occupied double statuses
  forbid population >=2 on their common
  side's opposite side**.
* If the central-square center is (a,b)
  with |a|,|b|<=1/10, **all four double
  statuses are impossible**.
* A single double status imposes one of
  four strict central-center displacement
  constraints, e.g. RU requires
  `a+b<-487/2500`.

The key orientation-free one-square
inequality is

    S subset {x>=h_x,y>=h_y} intersect D_R,
    h_x,h_y>=0
      => R^2>=(1+h_x)^2+(1+h_y)^2.

It is achieved only by the aligned
unit square touching both cap lines.

**Exact combinatorial effect.** For seven labeled
exterior squares, impose at most one
corner-only status at each corner,
each central-side population <=3,
and no opposite 3+2 populations.
The numbers of labeled status
assignments remaining after successive
logically necessary filters are:

| Filter | Labeled status assignments |
| --- | ---: |
| Original corner/side/opposite-cap restrictions | 8,551,760 |
| Plus double-status capacity <=1 each | 6,663,440 |
| Plus no opposite double-status pair | 4,808,720 |
| Plus double-pair versus opposite 2+2 exclusion | 4,566,800 |
| Plus triple-side versus opposite double-status exclusion | **3,995,040** |

These are **purely finite assignment counts**,
not realizable packing counts. A reproducible
formula is given in section 1A: expand the
generating function through z^7, discard
monomials violating the cap conditions,
then impose the two forbidden double-pair
combinations and the four indicated
double-pair/side-count conjunctions.

This eliminates 4,556,720 of the original
8,551,760 labeled **status assignments**,
approximately 53.3 percent. Nevertheless
all **31 coarse side-count profiles** still
admit some compatible status assignment,
so the number 31 must **not** be presented
as decreased by this refinement. Further
elimination needs geometry *within* those
profiles, not merely their side counts.



**Triple-side upgrade.** Any central side with
population three has whole-cap offset
`h<7/24` and makes the opposite side
offset exceed `17/24`. By the sharp
perpendicular corner-cap inequality, the
opposite side can then serve **no**
square also served by a perpendicular
central side. This removes 571,760
additional labeled status assignments
from the previous total of 4,566,800.

The four exact rejection conditions are:
`N_R=3 => count(LU)=count(LD)=0`;
`N_L=3 => count(RU)=count(RD)=0`;
`N_U=3 => count(RD)=count(LD)=0`;
`N_D=3 => count(RU)=count(LU)=0`.
The coarse 31 four-side *count* profiles
remain untouched, because each retains
some compatible status assignment.

## 2. The eight possible opposite-side count profiles

Let N_R,N_L,N_U,N_D denote the populations of **whole**
exterior squares beyond the corresponding signed side.
Every N is in {0,1,2,3}, by the semicircle capacity
theorem in HUMAN_CENTRAL_COMPACTNESS.md.

The three-square and two-square cap bounds exclude
an opposite-side profile (3,2),(2,3),(3,3) at the
search ceiling. Modulo reflection of the selected
central axis, the **complete list of profiles
not eliminated by those two cap counts** is:

| Profile of one opposite pair | Condition |
| --- | --- |
| 0+0 | No extra cap condition |
| 0+1 | No extra cap condition |
| 0+2 | No extra cap condition |
| 0+3 | Triple side has offset h<3/10 |
| 1+1 | No extra cap condition |
| 1+2 | No extra cap condition |
| 1+3 | Triple side has offset h<3/10 |
| 2+2 | Central-center signed side coordinate has magnitude <5/24 |

These are **necessary count profiles**, not eight
realizable classes. For every triple side the
opposite side population is at most one.
For two plus two, the more distant side is
at h=1/2+|a| (or 1/2+|b|), and the sharp
two-square cap theorem gives

    R^2 >=(3/2+|a|)^2+1,

hence |a|<=sqrt(R^2-1)-3/2<5/24
(and analogously for b).

The x and y axes each have 13 *signed* ordered
opposite-pair profiles: 4 possibilities when one
sign has count zero, 4 when it has one, 3 when
it has two, and 2 when it has three.
Thus there are at most 13^2=169 ordered four-side
**count profiles** to consider before applying
further geometry. Independent flips of the x,y
axes and an exchange of axes identify these into
36 unordered pairs of the eight types above.

The corner-capacity result imposes the additional
necessary condition

    N_R+N_L+N_U+N_D >= 3.                          (1)

Five of these 36 coarse profiles violate (1):
(0+0,0+0), (0+0,0+1), (0+0,0+2),
(0+0,1+1), and (0+1,0+1).
Therefore **at most 31 coarse numerical
profiles survive these particular count tests**.

This is only a necessary-filter count. A side square
may appear in two adjacent populations; the seven
*distinct* squares, corner assignments and all
pair separations must still be tracked. Many of
the 31 profiles may be impossible; none is thereby
proved realizable.

## 3. Independently classify centers inside/outside the unit circle

The center norm of each noncentral square is >1/2.
Call any square **outer** when its center norm is
at least one, and **inner** otherwise.
The unique central square C is always inner, since
its center local coordinates both have absolute
value <1/2.

There are **at least three and at most seven outer
centers** among the eight packed squares.
Here is a short new elementary proof of the lower
bound k>=3.

The open inscribed radius-1/2 disks of the squares
are pairwise disjoint, so distinct centers
satisfy distance >=1. Suppose six centers
had norm strictly less than one. If one were
zero, it would be at distance <1 from each
other such center, contradiction. Otherwise
sort their six polar directions. Some consecutive
gap is at most 2*pi/6=pi/3.
If those two center radii are 0<r<=s<1
and their angular gap is at most pi/3, then
by the cosine law

    |p-q|^2 <=r^2+s^2-r*s
            =s^2-r*(s-r) <=s^2<1,

contradicting center separation. Thus at most
five centers have norm below one, and among
eight there must be at least three with
norm >=1. Since C is inner, k<=7.

HUMAN_OUTER_CENTER_VISIBILITY.md proves that
outer-outer **actual** contacts join only
neighbors in the cyclic angular order of
these k outer centers. The outer-induced
actual-contact graph is therefore either

* a disjoint union of paths and isolated vertices; or
* the **entire** k-cycle.

HUMAN_OUTER_GRAPH_REDUCTION.md and the radial-escape
theorem exclude a full outer-only cycle unless k=7.
Thus the following coarse classification is
**exhaustive** at the current search ceiling:

| k outer centers | Other noncentral inner centers | Outer-induced actual-contact shape |
| ---: | ---: | --- |
| 3 | 4 | Paths and isolated vertices only |
| 4 | 3 | Paths and isolated vertices only |
| 5 | 2 | Paths and isolated vertices only |
| 6 | 1 | Paths and isolated vertices only |
| 7 | 0 | Paths/isolates **or** one full seven-cycle |

The table lists necessary graph alternatives and
does not assert that k=3,4,5,6 are realizable
at the sharp radius. Noncentral inner squares
can attach to outer paths and form cycles in the
**full** graph even when the outer-induced graph
has no cycle. An exterior square is not
necessarily outer: the original tilted candidate
has a noncentral inner center in some of its
valid slider placements.

At k=7 the outer-cycle branch is a **genuine
candidate equality branch**: the exact construction
ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md
realizes a full actual-contact seven-cycle
with central spokes at Rhat. It must not be
excluded simply by its existence.

## 4. Contact and stress patterns: do not mix representatives

For a radius minimizer chosen with **fewest actual
contacts**, HUMAN_CONTACT_COMPONENTS.md proves
there is exactly one nontrivial actual-contact
component, with other vertices possibly isolated.
The actual-leaf and actual-bridge theorems and
the degree-two transmitter alignment apply to
this specifically selected representative.

Separately, HUMAN_CONNECTED_MAX_CONTACT_REPRESENTATIVE.md
and HUMAN_TWO_CENTRAL_NEIGHBOR_REPRESENTATIVE.md
allow selection of a same-radius packing with a
connected full actual-contact graph and at least
two actual central neighbors, while preserving
the old physical stress on its fixed stressed
core. But this is not generally a
minimum-actual-contact-count representative.
It may acquire new **zero-stress actual contacts**.

A proof may use either representation, or
carefully couple them via the core-preserving
construction, but must not assign the
minimum-contact leaf/bridge theorems to
newly created contacts.

A contact graph alone omits which support side
of each square is used, possible point-versus-edge
contacts, circle-contact vertices and the
nonnegative stress weights. All of these yield
additional **finite discrete choices** plus
continuous values and equations.

## 5. A completely exhaustive algebraic branch encoding

This section supplies a formal finite disjunction
covering **every** geometric packing, irrespective
of all heuristic or hand classifications above.

For each of the eight labeled squares take a
center p_i=(x_i,y_i) and unit frame vector
e_i=(a_i,b_i) with

    a_i^2+b_i^2=1,
    f_i=(-b_i,a_i).

The four true square vertices are

    v_i(eps,eta)=p_i+(eps*e_i+eta*f_i)/2,
    eps,eta in {-1,+1}.

Disk containment is the 32 simultaneous conditions

    |v_i(eps,eta)|^2 <= q.                        (2)

For a pair i<j, define its centered support

    h_i(n)=(|n dot e_i|+|n dot f_i|)/2.

The separating-axis theorem says their open
interiors are disjoint **if and only if**
at least one of the eight *signed* axes

    n in {+e_i,-e_i,+f_i,-f_i,
          +e_j,-e_j,+f_j,-f_j}

satisfies

    n dot(p_j-p_i) >= h_i(n)+h_j(n).             (3)

There are C(8,2)=28 unordered pairs, so
selecting one valid signed axis for each pair
produces at most

    8^28

complete **separator-owner/sign patterns**.
An actual packing can satisfy multiple branches
at once; the branches need not be disjoint.
The absolute values in (3) can each be replaced
by a finite sign split, leaving only polynomial
equalities and inequalities in the 32 center/frame
coordinates and q. The unit-circle equations
for e_i are polynomial too.

Consequently each chosen discrete branch defines
a **semialgebraic** set. There are finitely many
branches, but infinitely many possible centers
and rotations within each. Indeed the exact
five-corner packing has a proven nontrivial
G-square slider interval at one fixed radius,
with the exterior contact ring preserved:
its continuous family is an explicit example,
not just a theoretical possibility.

In principle, because Rhat^2 is specified
algebraically by the exact stationary family
and isolating conditions, the statement that
no eight-square packing has q<Rhat^2 is
decidable via real-closed-field quantifier
elimination. That does not make a full
8^28-branch elimination or a hand proof
practical: the feasible orientation/contact
branches share nonlinear constraints, and
near equality the inequalities can have
extremely small margins.

## 6. The honest remaining proof task

The existing rejections are already strong:
no 4-square central cap, no opposite 3+2,
no four-square straight chain, no seven
parallel exterior frames, no short all-outer
actual-contact cycle, and only one
corner-owned exception per central corner.

But they do not force one concrete seven-edge
separator class. A candidate equality packing
can have a full seven-outer actual-contact ring
and three or four actual central contacts.
The last step is to prove, **for every surviving
continuous geometric branch**, either

    R>=Rhat by the coherent five-corner
    projected inequalities,

or a stronger alternative obstruction.
Equivalently one can find a direct sharp
inequality simultaneously retaining the
central unit square and all seven exterior
squares. A ring-only bound or a numerical
survey of a few orientations is insufficient.

Thus the answer is **finite combinatorics
plus continuous exact geometry**, not
infinitely many unrelated contact types,
and not a solved 31-case checklist.


### Auditable count by total side memberships

For the strongest finite filters above, let
`m=N_R+N_L+N_U+N_D`. A label counted
twice (one adjacent double-side status)
contributes two to m; a corner-only
label contributes zero. Expanding the
stated multinomial coefficient formula
with the four triple/opposite-double
conjunctions removed gives

| m | Remaining labeled status assignments |
| ---: | ---: |
| 3 | 53,760 |
| 4 | 372,960 |
| 5 | 1,118,880 |
| 6 | 1,534,400 |
| 7 | 814,240 |
| 8 | 100,800 |
| **Total** | **3,995,040** |

No assignment with m<3 is possible by
the corner-only capacity four; no
assignment with m>8 survives because
there are seven squares and at most
one populated status in each double
corner, with no opposite pair.

A direct finite formula for each entry is

    7! * sum_(n_R+n_L+n_U+n_D
             +d_RU+d_RD+d_LU+d_LD
             +c_NE+c_NW+c_SE+c_SW = 7)
           [side conditions and sum(side)=m]
           / product(factorial(n_i),factorial(d_j),factorial(c_k)),

where each d_j,c_k is 0 or 1; all n_i are
nonnegative integers. The side conditions
are exactly the count<=3, no-opposite-3+2,
no opposite-double, adjacent-double/opposite-2+2,
and triple/opposite-double exclusions described
above. This is finite **integer arithmetic**.
It is a reproducibility check, not a
geometric feasibility certificate.

In the *near-center subcase* `|a|,|b|<=1/10`,
the sharp corner-cap theorem forces all
d_j=0. Then only 588,000 labeled assignments
satisfy the older side/corner cap filters;
the extra triple/double filters are vacuous.
The position subcase is not asserted to be
feasible for any of those assignments.


**Why m<=8 without a computer.** Each double-side
square contributes one additional membership,
so m=n_side+d, where n_side<=7 is the number
of side-separated exterior squares and d
is the number of double-side squares.
We proved d<=2. For d<=1, m<=8 immediately.
For d=2, the two doubles must share one
side, say R. Its opposite side L has
population <=1 by the corner-cap theorem;
R itself has population <=3. The other
opposite side pair U,D has total
population <=4, because each is at most3
and a 3+2 opposite pair is forbidden.
Thus m=N_R+N_L+N_U+N_D<=3+1+4=8.
This explains the membership-bin cutoff
used in the finite count table above.


## 2A. The next certified reductions: 3,995,040 fine assignments and eight signed intervals

TRIPLE_DOUBLE_STATUS_PRUNING.md uses the existing
orientation-free **triple-side vs opposite double-side**
incompatibility to remove a further **571,760 labeled
status assignments**. The exact sequence is

    8,551,760  side/corner/opposite-cap filters,
    6,663,440  plus multiplicity <=1 of each double type,
    4,808,720  plus no opposite double-corner pair,
    4,566,800  plus adjacent double-pair vs opposite 2+2,
    3,995,040  plus triple side forbids opposite double.

The last count has only 1,656 **unlabeled integer
multiplicity vectors**, versus 2,060 before the last
filter. Each count is the exact sum of multinomial
weights 7!/(product m_type!) over twelve-status
vectors satisfying the stated conditions. This is
a finite combinatorial reduction, **not** a claim
that millions of packings remain feasible.

The same note improves the necessary central
center diagonal condition for any double-side
status: at q<=9789/2500,

    RU => a+b < -1/5,
    RD => a-b < -1/5,
    LU => -a+b < -1/5,
    LD => -a-b < -1/5.

If two adjacent double statuses share a central
side at positive offset h, then either
`h<1/4` or the central center's
**perpendicular** signed coordinate has
absolute value <1/29. These bounds follow
from the exact arbitrary-frame corner-cap
inequality, with a rational endpoint
comparison `52709/13456>9789/2500`.

HUMAN_ALL_SIDE_OFFSET_INTERVALS.md further
shows that **each side's population controls
its own central-center coordinate**, without
any frame assumption:

    side count >=1 => t<83/200;
    side count >=2 => t<5/24;
    side count  =3 => t< -5/24,

where t is the central-center projection toward
that signed side. Reflecting gives lower bounds
from the opposite side. In particular all eight
opposite-side count types now impose explicit
open rational intervals for t, ranging from
`(-1/2,1/2)` for 0+0 to
`(-83/200,-5/24)` for 3+1 and
`(-5/24,5/24)` for 2+2.

These **signed interval bounds shrink the
continuous domains** but do not yet eliminate
any of the 31 coarse count profiles solely
on their own. The exact rational three-square
example in TRIPLE_DOUBLE_STATUS_PRUNING.md shows
that one corner-only exception and one adjacent
double-side square *can* coexist at the same
central corner; removing that status conjunction
without a full eight-square argument would
be incorrect.


## 2B. Branches forced by the total number of central-side memberships

FORCED_CORNER_EXCEPTION_D2.md gives an exact
status identity and three-way fine count
table. Write D=0,1,2 for the number of
occupied two-side statuses, E for the
number of own-axis corner exceptions, and
S=sum of all four side populations.
Because seven distinct exterior squares
each contribute zero, one or two memberships,

    E=D+7-S.                                          (B)

The cap and corner-cap filters impose S<=8 and
D<=2. For the two-double macro-branch D2,
the shared side has at most three members,
the opposite side at most one and the
perpendicular sides at most two each.
Thus S<=8, and E=9-S>=1. If the shared side
has exactly two members, S<=7 and E>=2.
**Every D2 case therefore has a genuine
corner-only own-axis square**. A proof
assuming all seven squares are central-side
separated cannot cover that branch.

The exact labeled status word counts after
all existing necessary Boolean filters are:

| Total memberships S | D0 | D1 | D2 |
|---:|---:|---:|---:|
| 3 | 53,760 | 0 | 0 |
| 4 | 211,680 | 161,280 | 0 |
| 5 | 231,840 | 806,400 | 80,640 |
| 6 | 82,880 | 967,680 | 483,840 |
| 7 | 7,840 | 322,560 | 483,840 |
| 8 | 0 | 20,160 | 80,640 |
| **Total** | **588,000** | **2,278,080** | **1,128,960** |

These are combinatorial assignment weights,
not counts of continuous feasible packings,
and do not represent new eliminations beyond
the prior 3,995,040 total.

SINGLE_SIDE_SEVEN_BRANCHES.md now further
splits the **D0,S=7** case (all seven exterior
squares with one central-side separator and
no corner exception) into exactly four
coarse types up to symmetry:

    S1=(3+0,3+1), S2=(3+0,2+2),
    S3=(2+1,3+1), S4=(2+1,2+2).

The exact optimized five-corner candidate is
a **genuine S4 equality construction**,
not an excluded status profile. Its seven
single-side labels are R,R,L,L,U,D,D,
proved by full analytic inequalities
in SHARP_CANDIDATE_SIDE_STATUS.md.

HUMAN_STATUS_ANGULAR_LANES.md adds direct
whole-square geometry from sector replication:
every square wholly in one origin quadrant
and omitting zero crosses that quadrant's
diagonal ray through its open interior;
three whole squares in one half-disk must
have actual vertices in both angular
regions beyond +30 and below -30 degrees
about the half-disk axis. Hence the D2
double statuses occupy both +/-45-degree
diagonal rays of their shared side, while
a triple side reaches both 30-degree
extreme cones. These are **continuous
geometric constraints**, not additional
finite status-count exclusions.


## 6A. The triple and saturated Type A branches now have compulsory ray witnesses

HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md proves a new
**unrestricted-orientation** geometric requirement:
whenever a central side serves three complete
exterior squares, one of those three has an
open-interior intersection with that side's
outward cardinal ray through the disk origin.
Such a square is **single-side**, not a
double-side member; its other two central
perpendicular side separators are unavailable.

The proof is a two-quadrant pigeonhole:
without any ray crossing, all three complete
squares would be wholly in the two origin
quadrants adjacent to that side, with
capacity one per quadrant, a contradiction.
This holds at **every positive side offset**,
including offsets where the earlier stronger
whole-quadrant triple-cap theorem is not
available.

HUMAN_SATURATED_TYPE_A_RAY_ROUTING.md
then gives an exhaustive geometrical
routing for the maximally saturated
Type A side populations (3+1,3+1),
whose exact statuses are

    RU, R, R, L, U, U, D.

Four **different** single-side squares
cross the four *cardinal* rays in their
open interiors, respectively: one R
crosses +x, the L singleton crosses -x,
one U crosses +y, and the D singleton
crosses -y. The RU double lies entirely
in the origin NE quadrant and crosses
the NE diagonal ray. The distant-side
L,D crossings follow from the
existing h>17/24 transverse lane theorem.

If both triple offsets h_R,h_U are
at least 13/60, the remaining two
single-side members are forced to
lie **wholly** in the origin SE
and NW quadrants. Thus all seven
exterior squares in that Type A
subcase now have compulsory angular
roles: one full NE unit, one full
SE unit, one full NW unit, and four
separate cardinal-ray-crossing units.
No own frame alignment was assumed.

HUMAN_CORNER_ONLY_DOUBLE_RAY_BOUND.md
gives a complementary necessary
curved central-position constraint:
if an own-axis corner-separated
square assigned to a central corner
whose outward side offsets are A,B>0
crosses **both corresponding positive
origin rays through its open interior**,
then sqrt(A)+sqrt(B)<sqrt(2). For example
a central square centered in the
nonnegative NE quadrant has no
NE corner-only square wrapping both
positive coordinate rays. This is
a restriction on *ray placement*,
not a ban on every NE corner-only
status.

These results **do not decrease**
the purely symbolic total of
3,995,040 12-status assignments:
they add mandatory, exact continuous
geometric constraints to the surviving
triple, Type A, and corner-only branches.

Important guard: the ray witness in a
three-square cap has **not** been proved
unique. The triple-ray note contains
an exact rational two-square cap pair
where both squares' open interiors cross
the same cardinal ray within q_plus.
It would be invalid to use a purported
one-ray-crosser-per-cap rule without
a genuine three-square proof.


## New cross-class pruning: central statuses constrain k and center angles

**Outer-center counts are not independent of central-side statuses.**
HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md proves that the
saturated Type C status vector
`RU,R,L,L,U,D,D` (all four central side
counts 2+2) requires **k>=5** outer centers.
The hand proof combines the strict central
corner inequality `a+b<-1/5`, the
two opposite 2+2 center offsets
`|a|,|b|<5/24`, and elementary
cap-center estimates. Thus the
intersection of Type C with k=3 or k=4
is **completely impossible**, regardless
of the contact graph or rotations.

HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md
adds a general cap-angle theorem: three
full squares in any nonnegative cap
cannot all have center norms <1.
Three such center directions would lie
in an angular sector shorter than
120 degrees, while the inscribed
radius-1/2 disks require every
two inner-center rays to differ
by more than 60 degrees.
The same file gives these further
genuine center-position exclusions:

| Exclusive single-side type | Ruled-out k/offset subcase |
| --- | --- |
| S2=(3+0,2+2) | k=3 whenever |t_(2+2)|<=1/14 |
| S3=(3+1,2+1) | k=3 whenever the double-populated side of its 2+1 axis has h>=2/5 |
| S4=(2+1,2+2), containing equality | k=3 whenever the double-populated side of 2+1 has h>=2/5 |
| Same S4 | k=4 when also |t_(2+2)|<=1/14 |

Here `t_(2+2)` is the signed central-center
coordinate along that opposite-side axis,
not the five-corner tilt parameter.
All populations count **entire squares**
past central-owned separating sides.

HUMAN_TWO_CAP_CENTER_SIGN_SPLIT.md independently
proves that two whole squares in a cap
with h>=3/7 must have transverse center
coordinates of strictly opposite signs.
At h>=1/2 each sign has magnitude >1/10,
and both centers are outer. A farther
side of any opposite 2+2 pair always
satisfies this stronger condition.
A far side of a 3+1 pair
(h>17/24) serves only one square,
whose own open interior necessarily
crosses the outward origin diameter.

These eliminate **continuous k/location
subcases** rather than deleting
their parent 12-status multiplicity
vectors. The certified total of
3,995,040 symbolic labeled words
must therefore remain unchanged
unless an additional pure status
incompatibility is proved.


## New full-frame eliminations via two outer centers in a moderate triple cap

HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md proves, by one
common disk slice and exact chord inequalities, that
**three** complete squares beyond a line of radial
offset h>=7/50 at R<=99/50 contain **two distinct
center-norm->1 squares**. The highest and lowest
slice squares have

    p_top.x+p_top.y>1421/1000>sqrt(2),
    p_bottom.x-p_bottom.y>1421/1000>sqrt(2).

This is a hand theorem for **every square frame and
position** in the cap, not a grid or a choice of
contact normal between the three squares. It
strictly strengthens the earlier single-outer-center
triple lemma on this positive-offset region.

HUMAN_PERPENDICULAR_TRIPLES_SHARP_LANE.md then
sharpens the perpendicular-triple obstruction:
a triple cap with h>=7/50 has an outer-center
extreme in the exact angular lane

    alpha<phi<pi/2-alpha,
    alpha=atan(9/20).

Two perpendicular triple caps meeting that
offset threshold supply their respective
outer-center extreme **in the same lane**.
The lane has width
`pi/2-2alpha<pi/4-1/100`, whereas two
different outer square centers require
angular gap `>pi/4-1/500`.
They must therefore be **one common actual
square label**, served by both perpendicular
central sides. This conclusion uses no
parallel-frame, actual-contact, or
stress assumption.

In particular, all-single-side **S1** with
two perpendicular triples is impossible
throughout the whole central-center rectangle

    h_triple1>=7/50 AND h_triple2>=7/50.

Every S1 packing must have
`min(h_triple1,h_triple2)<7/50`, or,
after normalizing its triples to R,U,
`min(a,b)<-9/25`.
This improves the older `13/60` and
`11/50` thresholds, and it excludes this
continuous region **for all k=3,...,7**.
If the tiny-offset triple also has an
opposite singleton, the latter's center
transverse coordinate must satisfy
`|z|<9/50`.

Further exact macro-class intersections now
ruled out:

* **S2/k=3** if the triple offset is
  >=7/50, *or* if the 2+2 central coordinate
  has `|t|<=1/10`; the latter improves
  the former `1/14` strip.
* **S2/k=4** if the triple offset
  is >=7/50 and `|t|<=1/10`.
* **S3/k=3** unless **both**
  its triple offset is <7/50 **and**
  its 2+1 two-square side offset is <2/5.
* **S1/k=3,4** requires a tiny triple
  offset <7/50 (already true of S1 for all k).
* **Saturated Type A/k=3,4** when both
  of its perpendicular triple offsets
  are >=7/50 (its one shared RU square
  is counted only once, alongside two
  distinct opposite far-side singletons).

These are **provably excluded continuous
status/outer-center/offset subregions**, not
new integer-status assignment counts. The
31 coarse count profiles and 3,995,040
fine symbolic labeled assignments are
bookkeeping upper bounds; the above geometry
restricts their *real coordinates* further.
The exact sharp S4 candidate remains a
genuine equality branch and is not eliminated.


## New 2026-10-12 exact center-count cross-class exclusions

The independent whole-frame
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
proves that **two** whole squares whose center norms are
strictly below one cannot lie together in a nonnegative
cap of offset \(h\ge(\sqrt3-1)/2\).
The threshold is sharp already for two axis-parallel squares
within the search disk; if two such inner centers exist,
their transverse center-coordinate signs are opposite.

The independent
[HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md](HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md)
adds a strict quarter-circle bound on the two offsets
for two distinct inner squares per perpendicular whole cap:
\((h_x+1/2)^2+(h_y+1/2)^2<1\).
Its low-k consequences include angular-lane descriptions in
[HUMAN_S1_K3_FOUR_INNER_LANES.md](HUMAN_S1_K3_FOUR_INNER_LANES.md)
and [HUMAN_S2_K3_INNER_FAN.md](HUMAN_S2_K3_INNER_FAN.md).

**Stronger final result:**
[HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md)
uses the **two outer centers on the far side of a 2+2
axis** and their rigorous angular separation to
eliminate the *entire* S2/k=3 and S4/k=3 cases.
The proof is a forbidden six-square combination,
not a sampled optimization or a contact-graph assumption.

| Exclusive all-single-side case | Outer count \(k\) still open |
| --- | --- |
| S1=(3+0,3+1) | **3,4,5,6** |
| S2=(3+0,2+2) | **4,5,6** |
| S3=(3+1,2+1) | **3,4,5,6,7** |
| S4=(2+1,2+2) | **4,5,6,7** |

The outer count is **separate** from the old
3,995,040 twelve-status assignment count, which was
computed without classifying individual center norms.
It must not be silently decreased by counting these joint
macro-cell exclusions as rejected twelve-status words.
The S4/k=7 sharp equality cycle remains valid.

[verify_far_two_cap_angular_margins.py](verify_far_two_cap_angular_margins.py)
checks the rational sign margins in the new proof, not the
continuous geometric reasoning itself. No general
\(R_8\ge\widehat R\) theorem follows from the k=3 cell
eliminations; outer paths/attachments and surviving D1/D2
branches still require sharp inequalities.


### New S2 inner-pair and S3 low-k center-position strata

The current **exclusive S2=(3+0,2+2)** case has a particularly
sharp joint classification when the nearer two-member
2+2 cap has **both** square centers inner:
[HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md](HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md)
forces its perpendicular right triple to have exactly
two outer-center members (necessarily above/below
the outward origin ray) and one inner-center member.
The two far-side 2+2 cap squares are outer, so
**k=4 exactly**. It excludes the entire S2/k=5
subcase with both near-side centers inner.
[HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md](HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md)
then proves the right triple-cap outward offset
**must be strictly below 1/10**. At or above
1/10 the remaining inner R center has no angular
gap between the four ordered outer centers that is
large enough to permit unit-center distance, and
cannot lie above both R outers without approaching
the positive-x inner U center within 60 degrees.

For **S3=(3+1,2+1), k=3**,
[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
eliminates the entire two-member U offset strip
h_U>=21/100. The remaining exact strict offset
rectangle is
\(17/200<h_R<13/100\),
\(17/200<h_U<21/100\), and the outer R
center ray belongs to one of only two
nonadjacent angular intervals specified in
[HUMAN_S3_K3_REMAINING_TWO_LANES.md](HUMAN_S3_K3_REMAINING_TWO_LANES.md).
The distant L/D singleton center transverse bounds
in that note are \(|p_L.y|<3/20\) and
\(|p_D.x|<11/32\).

These are **strictly necessary continuous conditions**
under **inner/outer** hypotheses, not claims
that a residual case is realizable, nor any
change to the 12-status combinatorial labels.
Outer-center paths and the seven-outer S4
candidate contact cycle remain part of the
unrestricted case queue. The sharp reverse
radius bound \(R_8\ge\widehat R\) is still OPEN.


## 2026-10-12 exact global-pruning progress in the exclusive D0/S=7 classes

The latest **full-center-domain hand proofs** supersede
older S2 near-inner and S3/k3 residual strips:

* [HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md):
  **the entire S3/k=3 joint status/outer-count cell is impossible**.
  The last positive outer-R ray from the previous angular
  analysis forces a center-distance contradiction with
  the positive-y inner R center. This uses the
  **R-only, not RU** whole-side status condition
  essentially.
* [HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md):
  **the entire S2 subbranch where both nearer 2+2
  whole-cap centers are inner is impossible**, for every
  outer-center count. The final geometric obstruction
  is \(|q_{\mathrm{outer\,R+}}-p_{\mathrm{inner\,U+}}|^2
  <4923651/5000000<1\), proved by strict angle bounds,
  independent frames and four hand convexity endpoints.

The current necessary exclusive-one-side queue is:

| Status type | k not yet globally excluded | Additional necessary restriction |
| --- | --- | --- |
| S1=(3+0,3+1) | 3,4,5,6 | Exceptional small perpendicular-triple offset regions remain |
| S2=(3+0,2+2) | 4,5,6 | **At least one nearer 2+2 cap center is outer** |
| S3=(3+1,2+1) | 4,5,6,7 | k=3 fully impossible |
| S4=(2+1,2+2) | 4,5,6,7 | Includes actual k=7 sharp equality |

In particular S2/k=4 now necessarily has
*exactly one* nearer-cap outer and *exactly one*
perpendicular triple outer, besides its two
far-cap outer centers; k=5/6 still permits
several outer allocations that need new sharp
geometry. The candidate's S4/k=7 ring is
unchanged.

**These are joint center/status restrictions,
not new reductions of the 3,995,040 purely
symbolic twelve-status word count**. The
theorem \(R_8\ge\widehat R\) remains OPEN,
as do D0 corner-only exceptions, D1/D2 and
outer-contact graph branches.
