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
