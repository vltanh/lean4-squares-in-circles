# Global stress-root proof architecture for all eight-square minimizers

**Research continuation, 2026-10-12. Status: an exact all-frame structural
case reduction, not the unrestricted radius lower bound.**

This note reorganizes the open global eight-square proof by *actual
contacts and normalized physical stress*, rather than by millions
of symbolic central separator assignments or a shrinking local
cap-offset threshold. It combines established contact/cycle
theorems with the new
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md).

## Theorem: four exhaustive structural roots

Let an eight-square packing **attain the least possible radius**
\(R_8\), and assume the rigorously constructed candidate gives
\(R_8^2\le9789/2500\). Let C denote the unique square whose
open interior contains the disk origin. Let k be the number
of **exterior** square centers with norm \(\ge1\) (0<=k<=7).

Choose an arbitrary normalized physical contact/circle stress
from HUMAN_CONTACT_EQUILIBRIUM.md. Its nontrivial positive-contact
component is unique by HUMAN_CONTACT_COMPONENTS.md.

Every such minimizer belongs to **one of four mutually exclusive
roots**, by following the conditions in this order:

| Root | Exact condition | Structural consequence |
| --- | --- | --- |
| **A. Actual seven-outer ring** | The actual-contact graph induced by the seven outer squares is the full seven-cycle | k=7; the only inner square is C with center radius <1/2; the real equality construction belongs here |
| **B2. Centrally stressed, degree two** | Not A; C has exactly two neighbors of positive contact stress | Two opposite central contact normals; if k=7, the whole positive-stress component is one C-rooted cycle with m=3..7 consecutive outer labels (35 cyclic supports) |
| **B3. Centrally stressed, branching** | Not A; C has positive stress degree at least three | Central force vectors surround zero in convex hull; no two-spoke/cycle normal form may be assumed |
| **X. Exterior stressed cycle** | Not A; C has no positive contact stress | A nontrivial positive-stress component avoids C and contains a directed nonzero-moment exterior cycle of length 5, 6 or 7 with **at least one noncentral inner-center square** (norm <1); consequently k<=6 |

These cases **exhaust all attained minimizers** at the search radius
ceiling. They do not assert feasibility of every root, forbid the
real equality construction, or prove \(R_8\ge\widehat R\).

## Proof of exhaustiveness and the difficult exterior-root assertion

First the central-square theorem
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md gives
exactly one square C containing zero in its
open interior. Its own center satisfies
\(|p_C|<1/\sqrt2<1\). Thus k<=7.

The angular visibility / radial escape theorem
HUMAN_OUTER_GRAPH_REDUCTION.md proves that the
outer-induced actual-contact graph is either a
forest of paths and isolates or the *full*
seven-outer actual-contact cycle (which can
occur only for k=7). The latter is root A,
including the sharp candidate's genuine
seven-outer actual ring.

Exclude A in the rest of the proof. Then
**no actual cycle contains outer squares only**,
at any outer count k; the outer-induced
actual graph is a forest.

A normalized physical stress exists at an
attained radius minimizer. Its positive
contact graph has a **unique nontrivial
component J** and J contains a directed
nonzero signed contact-moment cycle, by
HUMAN_CONTACT_COMPONENTS.md and the
nonradial contact-moment theorem.
The central square C has no circle
contacts because it contains zero in its
open interior and each vertex has norm
strictly less than sqrt(2)<R.

If C belongs to J, its circle force
sum is zero, so its positive contact
forces sum to zero. Thus its positive
degree is **at least two**. If it is
exactly two, the opposite central
normal theorem and seven-outer
C-rooted cycle normal form apply:
root B2. If its positive degree is
at least three, this is root B3.
The vector-equilibrium equation
\(\sum_j\lambda_j n_j=0\) with all
\(\lambda_j>0\) shows that zero belongs
to the convex hull of its actual
outward contact normals; this is
a **necessary force constraint**,
not a conclusion of tangent-square
alignment or a prescribed contact
graph.

If C does **not** belong to J, it has
zero positive contact degree. The
nonzero-moment cycle in J consists
entirely of *exterior* square labels.
The all-orientation cycle theorem in
HUMAN_CONTACT_COMPONENTS.md section 2
excludes 3-cycles directly and 4-cycles
by its cross-occupancy theorem for n=8.
Thus a simple directed exterior
moment cycle in J uses at least **five**
distinct exterior squares and at most
seven (because only seven are exterior).

Since the outer-induced actual-contact
graph is a forest, this exterior
cycle **cannot** have all its center
norms \(\ge1\): that would be an
outer-only actual-contact cycle,
contradicting the preceding outer graph
theorem. At least one vertex of this
exterior moment cycle has center norm
\(<1\). Since it is exterior, it
is a **different inner-center square
from C**. Thus k<=6.
This is exactly root X.

The four roots are mutually exclusive
by their ordered conditions and cover
every minimizer. QED.

## Further exact reduction inside B2 when k=7

For k=7 and no actual outer full-cycle,
the new
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
proves:

* C is necessarily in the unique nontrivial
  positive-stress component.
* If C's positive degree is two, its normal
  contact forces are opposite and equal, and
  the two outer neighbor squares **cannot**
  touch one another.
* Every positive outer-outer edge has nonzero
  signed contact moment and hence lies in
  a directed circulation cycle through C.
  Therefore the positive component is exactly
  **one** simple C-rooted cycle, with no
  positive-stress outer tails.
* It uses m=3..7 consecutive outer labels.
  There are **seven labeled placements for
  each m**, so 35 combinatorial supports.
  Other exterior squares have zero positive
  contact/circle multipliers in the chosen
  stress, but **their physical area, vertices,
  and zero-weight actual contacts remain**.

This is a *stronger geometry-relevant
normal form than the bare outer-path statement*.
It does not assign the square orientations,
physical circle vertices, true pair SAT axes
or spectator positions.

## Structural proof tasks (replace small numerical-gap work)

The sharp construction already proves
\(R_8\le\widehat R\). The missing direction
must be proved in **each root**, allowing
equality in the real candidate.

**A: seven-outer actual ring.**
Determine the exact seven-square contact-cycle
radial/angle inequality **including the
central unit square's actual pocket**.
An outer ring alone can pack in a smaller disk,
so ignoring the central unit is invalid.
The known sharp candidate belongs here,
and its equality frame/slider families
must survive.

**B2: two-force central core.**
For k=7, study the five outer-path
sizes m=3,4,5,6,7 from the exact
cycle normal form. Prove the sharp
five-corner inequality or a valid
alternative for the **stressed path
plus its 7-m spectators**, rather
than assuming the C-rooted support cycle
uses every square. For k<=6 retain
the extra noncentral inner labels;
do not incorrectly import the k7
cycle normal form.

**B3: three-or-more-force central core.**
Use the true force normals' positive
balance at C to force either a sharp
five-corner scaffold or a separate
radius bound. The sharp candidate may
have *more* than two **actual** C
contacts, so distinguish **positive
stress degree** from actual contact
degree. Do not exclude B3 solely by
counting actual central neighbors.

**X: exterior cycle with an inner witness.**
A directed positive-moment cycle on
5..7 exterior squares contains at least
one exterior center of norm <1 and
leaves C outside the stressed core.
Exploit that inner-center witness,
the angular/winding structure from
HUMAN_GLOBAL_CYCLE_CLOSURE.md, and
the placement of all unused exterior
units to force \(R\ge\widehat R\).
No whole-square central side separator
may be inferred from center radius alone.

The full status taxonomy D0/D1/D2 and
S1..S4 remains an auxiliary geometric
filter **within these four roots**,
not a second incompatible exhaustive
list and not 3,995,040 independent
claims of feasibility.

## Honest status

The reduction is purely structural:
no lower bound \(R_8\ge\widehat R\),
complete equality classification,
or production Lean 4 proof is
claimed. The next meaningful success
must close an entire root or derive a
universal sharp inequality spanning
multiple roots, not merely lower a
local cap offset from one rational
number to another.


## Completed root-B2 full-path case

An entire global contact/stress macro-case
is **now rigorously excluded**, improving
the initial conditional 35-support count:
[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md).

In root B2 with **k=7 outer centers** and
no full actual outer contact cycle,
the central square's two stressed
neighbor forces are opposite.
[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md)
proves their true center-ray angle satisfies
\(\Delta>\pi/2+1/13\).

If the stressed cycle contained all seven
outer squares (m=7), the other six
**true consecutive outer contacts**
would each have angular gap
\(>\pi/4-1/500\) and leave a
missing seventh gap
\(\Delta<\pi/2+3/250\).
These strict exact inequalities are
incompatible (\(211/3250>0\)).
Consequently \(\boxed{m\ne7}\) in
this particular structural root.

The **currently unexcluded seven-outer,
actual-path, central-positive-degree-two**
stressed cycles are only
\[
\boxed{m=3,4,5,6},
\]
or 28 labeled cyclic positive-stress
supports. All zero-stress spectators
remain real space-occupying squares.
The fully actual seven-outer **cycle**
equality construction stays in root A;
central degree>=3 stays in root B3.

This is a meaningful **whole structural
macro-branch closure**, not a complete
global packing bound. k<=6,
root X, and the equality-preserving
A root remain unresolved.


## Further exact refinements within B2 (true actual contacts, not cap-offset cases)

[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md)
sharpens B2 in **every k root**:
its two opposite positive C normals
are constrained by C torque equilibrium
to the **four central side/diagonal
unoriented axes**, with contact-point
chord either across opposite C side
faces (same tangential coordinate)
or across the two opposite C vertices.

In a representative chosen with
the **fewest actual square contacts**,
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
further eliminates the bare diagonal
two-spoke case: diagonal B2 must have
at least **four actual C neighbors**,
with two additional zero-stress
contact normals of strictly opposite
tangential projections.

For k7/B2 with an outer actual-path
graph, the positive stressed cycle
sizes m3..6 are treated by
[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md).
Every two adjacent *internal*
stressed-path members must include
a true disk-circle contact or a
true zero-stress C chord. The
minimum number of anchored internal
labels is 0/1/1/2 for m3/m4/m5/m6.

The most constrained m6 root has
an exhaustive **P/S/K actual contact**
classification:
P = just two actual C contacts,
S = C additionally contacts only
its sole outer spectator T,
K = at least one additional actual
C-to-internal-path square contact.
Modes P and S each force **at
least three distinct true circle-
contact exterior squares**, and
mode K forces **at least two**
internal boundary-or-C-chord labels.
Any diagonal C-positive mode is K.

The mode-S spectator leaf is forced
onto one of the **perpendicular**
central side normals, genuinely
radial, C-parallel, and circle-contacting
at two vertices, by the exact
leaf-capacity and leaf rigidity
theorem. The whole S mode, the
other P/K subcases, the outer
full contact ring A, B3, X and
k<=6 remain unresolved. No
unrestricted sharp radius bound is
claimed.
