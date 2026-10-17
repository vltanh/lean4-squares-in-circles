# A rational 12-cone DAG constraint on EVERY genuine eight-square SAT-owner word

**2026-10-13. Exact whole-configuration COMBINATORIAL
ORIENTATION REDUCTION**, valid for all independent true square frames
and all centers in the global search disk \(R^2\le9789/2500\).
It strengthens [HUMAN_GLOBAL_SAT_OWNER_CYCLE_CONE_EXCLUSION.md]
(HUMAN_GLOBAL_SAT_OWNER_CYCLE_CONE_EXCLUSION.md)
by converting its general directed-cycle inequality into
**twelve fixed rational, graph-theoretically acyclic
owner classes**.

This is not a complete SAT-owner enumeration or the
unrestricted sharp radius theorem.

## Theorem (12 rational direction sectors must each induce a DAG)

Let \(S_1,\ldots,S_8\) be eight genuine unit squares with arbitrary
independent frames, fitting with disjoint open interiors in the
disk of squared radius \(q\le9789/2500\).

For every unordered pair \(\{i,j\}\), choose **any one**
actual signed square SAT-owner separator: a unit vector n that
is a signed side normal of square i or j and satisfies
\[
n\cdot(p_j-p_i)\ge H_i(n)+H_j(n)\ge1.
\]
The equivalent REVERSED directed separator
\(j\to i\) is obtained with signed vector \(-n\);
it satisfies the identical genuine support inequality.

Construct **12 fixed rational sector boundary rays** as follows.
In the first quadrant take the three true rational unit vectors
\[
v_0=(1,0),\quad
v_1=(15/17,8/17),\quad
v_2=(3/5,4/5),
\]
followed by \(v_3=(0,1)=Jv_0\).
Rotate the ordered triple \((v_0,v_1,v_2)\)
by successive multiples of \(\pi/2\), obtaining
12 rays \(r_0,\ldots,r_{11}\) ordered counterclockwise.
Write \(K_k\) for the **closed positive angular sector**
between \(r_k,r_{k+1}\), with cyclic indices modulo 12.

For each k, form a directed graph \(G_k\) on the eight
square labels: include the oriented edge \(i\to j\) if
the genuine chosen signed separator n for the pair,
viewed in that direction, belongs to \(K_k\).
For the reverse orientation \(j\to i\), the genuine normal
is \(-n\), assigned to the sector containing it.
If a normal lies exactly on a sector boundary, it may
appear in both adjacent sector graphs.

Then **EACH of these twelve directed graphs is acyclic**:
\[
\boxed{\forall k=0,\dots,11,\quad G_k\text{ is a DAG}.}
\tag{1}
\]
Equivalently, every sector admits a topological ordering
of the eight square labels, consistent with all chosen
genuine separators in that direction.

This is a **global, CENTER-FREE** necessary condition on
the entire 28-pair signed owner word. It does not
depend on center-ray order, contact existence, or any
candidate frame cluster.

## Proof: exact rational angular width and cycle contradiction

First, in the first quadrant, the three successive
angular gaps have exact tangent ratios
\[
\tan\angle(v_0,v_1)=8/15,\quad
\tan\angle(v_1,v_2)=36/77,\quad
\tan\angle(v_2,v_3)=3/4.
\]
These follow from the exact rational dot/cross identities
\(\tan\angle(a,b)=(a\times b)/(a\cdot b)\)
for rays in a quadrant and angles below \(\pi/2\).
Every ratio is at most 3/4.

The elementary inequality
\(\tan x\ge x+x^3/3\) for \(0\le x<\pi/2\)
follows by differentiation:
the derivative of \(\tan x-x-x^3/3\) is
\(\tan^2x-x^2\ge0\) since \(\tan x\ge x\).
At x=2/3 it gives the STRICT rational comparison
\[
\tan(2/3)\ge 2/3+8/81
=62/81>3/4,
\quad 62/81-3/4=5/324>0.
\]
As tangent is increasing on \([0,\pi/2)\),
all three first-quadrant angular sector widths
are strictly **below 2/3 radians**.
Rotation by \(\pi/2\) preserves the widths;
therefore
\[
\boxed{\text{every rational fan sector }K_k
       \text{ has angular width }<2/3.}       \tag{2}
\]

Now suppose a directed graph \(G_k\) contained
a directed simple cycle. Every one of its genuine
directed SAT normals lies in the SAME fixed sector
\(K_k\), hence in an angular arc narrower than 2/3.
But the **all-cycle** part of
[HUMAN_GLOBAL_SAT_OWNER_CYCLE_CONE_EXCLUSION.md]
(HUMAN_GLOBAL_SAT_OWNER_CYCLE_CONE_EXCLUSION.md)
already proved that no true unit-square packing
in the disk ceiling can realize a directed
separator cycle with all normals in ANY cone
of angular width ≤2/3: the summed true square
supports are at least the cycle length k,
whereas the disk-bound center positions force
them below \((283/300)k<k\).
Contradiction. Therefore \(G_k\) is acyclic
for every k, proving (1). QED.

## Exact arithmetic sector ownership predicate

**No atan2 or trigonometric approximation is needed
to test this condition for RATIONAL frames.**
For any rational signed unit normal n and the
two rational boundary rays \(r_k,r_{k+1}\), n belongs to
their positive closed sector (whose width <π/2)
exactly when
\[
\boxed{
r_k\times n\ge0
\quad\text{and}\quad
n\times r_{k+1}\ge0.}
\tag{3}
\]
All signs are exact rational determinants.

Thus a program can **soundly reject** any raw signed
SAT-owner word when either:
* three of its owner edges yield the already proved
  directed \(60^\circ\) triangle cone contradiction,
  checked using exact cross products and
  unit-vector dot products ≥1/2; or
* one of its 12 rational sectors contains a
  directed graph cycle, detected by ordinary DFS.

The independent checker
[verify_rational_fan_sat_owner_word.py]
(verify_rational_fan_sat_owner_word.py)
implements both checks using Python Fractions only.

**Negative regression:** the exact rational nonparallel
three-square cycle in
[global_sat_triangle_fan_cycle_example.json]
(global_sat_triangle_fan_cycle_example.json)
is correctly rejected by its 60-degree triangle
test (its three owner normals span about 53 degrees).

**Positive regression:** the full
[rational_eight_feasible_owner_word.json]
(rational_eight_feasible_owner_word.json)
selects a genuine SAT owner for **all 28 pairs**
of the previously proved
[ANALYTIC_RATIONAL_CONSTRUCTION.md]
(ANALYTIC_RATIONAL_CONSTRUCTION.md)
eight-square packing, with six standard frames
and two rational tilted frames
\(e=(255/257,32/257)\).
The checker correctly does **NOT** reject this word.
Every selected owner is separately proven feasible
by the construction's exact true disk/SAT
inequalities. This is important: the new cycle
rules do not spuriously eliminate the known
near-sharp packing.

An exploratory random-owner sample of 2,000
words per frame scenario found that the 60-degree
triangle check alone ruled out approximately
96.75% of aligned/candidate-like raw assignments
and 98.8% for independently random frame angles.
**These percentages have NO worst-case or
global completeness implication**; even 1%
of \(8^{28}\) is far too large to enumerate
naively. The script is explicitly labeled
noncertifying.

## Connection to the decisive global proof

The structural gain is an exact rational
**DAG constraint for each of 12 directions**.
A future complete eight-square owner-angle
certificate can reject whole SAT-owner branches
using merely finite graph cycles and rational
cross-product interval signs, BEFORE solving
any center-fiber SOCP or branching on center
coordinates. This combines naturally with the
exact center-eliminating positive dual in
[GLOBAL_SAT_ANGLE_FIBER_DUALITY.md]
(GLOBAL_SAT_ANGLE_FIBER_DUALITY.md).

It remains necessary to establish a FULL,
finite terminating cover of the eight-angle
space and of all owner words surviving this
DAG filter and the existing disk marker
constraints. No such complete cover is
claimed here, and the unrestricted sharp
bound \(R_8\ge\widehat R\), equality and
Lean formalization remain OPEN.


## Later strengthening: a fixed rational projection margin, plus cross-sector Farkas

The previous twelve-cone DAG theorem has been **strictly
strengthened** by
[HUMAN_RATIONAL_SECTOR_PROJECTION_FARKAS.md](HUMAN_RATIONAL_SECTOR_PROJECTION_FARKAS.md).

If any genuine directed square SAT-owner normal
n lies in the k-th rational cone, its center pair
obeys the **explicit projection inequality**
\[
\boxed{(r_k+r_{k+1})\cdot(p_j-p_i)>289/2700.}
\]
This holds for **all independent square frames**,
not merely at rational points. The hand proof uses
the center radius \(<283/200\), true SAT support
sum >=1, sector width <2/3 radians, and the
unit bisector's angular distance <1/3 from n.

Thus every sector graph is not only a DAG but a
set of **strictly ordered rational linear projections**.
More importantly, owner edges belonging to DIFFERENT
sectors may themselves be incompatible. If positive
integer/rational coefficients on selected sector edges
make the coefficient of **every center p_i vanish
exactly**, their summed positive projection
inequalities would say 0>positive, a pure Farkas
contradiction.

A fully exact example with **eight real rational
square frames and 28 selected signed true SAT owners**
passes ALL previous 60-degree-triangle and
12-sector DAG tests but is ruled out by just
**eight selected cross-sector inequalities**
with exact integer weights 44,51,28:
\[
0>327(289/2700)=31501/900>35.
\]
The file
[global_sat_balanced_sector_farkas_certificate.json](global_sat_balanced_sector_farkas_certificate.json)
and checker
[verify_rational_sector_farkas.py](verify_rational_sector_farkas.py)
verify every rational sector assignment, the
28-edge old-screen pass, and all 16 EXACT center
force cancellations. The new test is therefore
**genuinely stronger than the preceding DAG filter**.

The further
[verify_interval_rational_sector_farkas.py](verify_interval_rational_sector_farkas.py)
checks the same positive integer Farkas balance
over a FULL, strictly positive-width,
**eight-dimensional rational frame half-angle
box**, from
[global_sat_balanced_sector_eight_angle_box_certificate.json](global_sat_balanced_sector_eight_angle_box_certificate.json).
All selected true normals remain inside their
certified rational cones throughout the box
with exact positive cross-product margins, and
every possible center arrangement would again
yield the impossible 0>31501/900.
No sampled orientations or numerical solver
output enter this conclusion.

The global unrestricted optimal radius remains
OPEN: these are *whole owner/angle-class
exclusions* and do not prove that every
other owner class has been covered.
