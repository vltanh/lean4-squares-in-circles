# In the pure m=3 stressed cycle, ALL three outer squares require positive physical circle multipliers

**2026-10-13. Complete force-support exclusion of the zero-multiplier
internal stressed square.** This strictly strengthens
[HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md](HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md):
the internal square T is forced not merely to touch
the containing circle, but to have a **strictly positive
physical circle-vertex multiplier** in every normalized
simple-cycle physical stress under the stated hypotheses.

The result uses true square contact supports, an exact
distance-one neighbor theorem, force/torque equilibrium and
area. It does **not** assume a common parallel frame and
does not tune any cap-offset constant.

## Theorem

Let eight genuine unit squares attain the least
containing disk radius \(R<2\), and choose among
such minimizers one with the fewest **actual
square-square contacting pairs**.

Suppose C is the unique origin-containing unit square,
all seven exterior center norms are at least one,
the outer-induced actual contact graph is a **proper
subgraph of the seven-ray neighbor cycle**,
and the simple positive-stress component is
exactly
\[
C-A-T-B-C
\]
with C having **exactly two actual square contacts**,
namely A and B.

Let \(m_X\ge0\) denote the sum of the
nonnegative physical circle-vertex
multipliers on square X in an
**arbitrary normalized physical stress**
with that positive cycle support.

Then
\[
\boxed{m_A>0,\quad m_T>0,\quad m_B>0.}          \tag{1}
\]

The two endpoint inequalities already follow from
[HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md](HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md);
the **new assertion is \(m_T>0\)**.

Consequently, the *entire positive
circle-multiplier support*, among the
eight square labels, is **exactly**
\(\{A,T,B\}\): C is strictly
circle-free and the four spectator
squares belong to no positive
stress component and thus have
zero circle multipliers.

Every one of the three stressed
exterior squares therefore has
**a true vertex on the containing
circle with positive stress weight**.
The four actually isolated spectators
remain real whole squares; their
disk occupancy constraints are not
removed.

## Proof

### 1. C is a true unit-width transmitter and forces dist(A,B)=1

Because C contains zero in its open
interior and \(R>\sqrt2\),
it is strictly circle-free.
It has **exactly two actual contact
neighbors** A and B.

The minimum-actual-contact interior
transmitter theorem in
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md),
sections 8--9, therefore gives a
**unique contact normal direction**
n from A across C toward B,
aligned with a true side normal of C.
Its two opposite C contacts are
genuinely tight full unit-width
support separators, and the exact
closed-set distance of its two
other neighbor squares is
\[
\boxed{\operatorname{dist}(A,B)=1.}             \tag{2}
\]

Section 9 also proves that n is
the **unique unit direction**
maximizing the directed projection
gap
\[
g(v)=v\cdot(p_B-p_A)-H_A(v)-H_B(v)
\]
over unit vectors v, with
\[
\boxed{g(n)=\operatorname{dist}(A,B)=1.}         \tag{3}
\]

Here H_X(v) is the centered square's
true supporting half-width, and
\(2H_X(v)\ge1\) for any unit-square
frame and unit v.

### 2. If T had zero circle multipliers, its positive contacts would propagate one normal

Assume toward contradiction \(m_T=0\).
There are exactly **two positive
stress contact pairs** incident
to T: A--T and T--B, because the
given positive graph is precisely
the four-cycle and other actual
contacts (if any) have zero weight.

The physical force equation
\(F_T=2\sum_\alpha\mu_{T,\alpha}
x_{T,\alpha}=0\) then implies the
two nonzero positive pair contact
forces cancel. If \(v\) is the unit
separating normal directed A→T
and \(w\) the unit separating normal
directed T→B, with strictly positive
force weights \(\lambda_1,\lambda_2\),
we have
\[
\lambda_1v=\lambda_2w,
\]
so
\[
\boxed{\lambda_1=\lambda_2,\quad v=w.}         \tag{4}
\]

Both *actual full-square contact
separator equalities* are therefore
tight in the same directed unit
normal v:
\[
\begin{aligned}
v\cdot(p_T-p_A)&=H_A(v)+H_T(v),\\
v\cdot(p_B-p_T)&=H_T(v)+H_B(v).
\end{aligned}
\]
Adding gives the exact neighbor
projection gap
\[
g(v)=2H_T(v)\ge1.                               \tag{5}
\]
But \(g(v)\le\operatorname{dist}(A,B)=1\)
for **every unit direction v**,
by (2)--(3) and the elementary
true-square closest-points theorem.
Thus equality holds throughout (5):
\[
\boxed{g(v)=1,\qquad 2H_T(v)=1.}                \tag{6}
\]

The **minimum projected width of a
unit square equals one**, and equality
holds only for a true square side
normal. Thus \(v\) is a **side normal
of the actual square T**. The
uniqueness of the maximizer of
g at (3) also forces
\[
\boxed{v=n.}                                   \tag{7}
\]

This is **stronger** than merely
applying torque equilibrium to T,
which would have permitted a
diagonal normal. The shared
neighbor distance-one theorem
itself rules out the diagonal
transmission width \(\sqrt2>1\).

### 3. Two side-aligned transmitters sharing A,B force four genuine parallel frames

C already has side frame normal n
and tight opposite A/B support
contacts. The preceding step shows
T also has side frame normal n and
tight opposite A/B contacts.

Both C and T therefore have
their normal center coordinate
equal to the midpoint of the
same A and B support lines;
hence
\[
n\cdot p_C=n\cdot p_T.
\]
Their true square frames are
parallel (both have side normal n).

Because C's **actual** contact
degree is exactly two, C and T do
**not** actually contact one another.
At the common normal center
coordinate, two parallel unit
squares with disjoint closed sets
must have strictly separated
transverse center coordinates,
by more than one unit:
\[
\big|(Jn)\cdot(p_C-p_T)\big|>1.                 \tag{8}
\]

Each of A and B must have a true
support face perpendicular to n
meeting the facing side of **both**
C and T. If either outer neighbor
had no side normal aligned to n,
its exposed support face would be
a *single point*. A single point
cannot meet the two disjoint
transverse side intervals of
C and T, whose center separation
exceeds one. Therefore both A
and B also have true support **edges**
perpendicular to n, which makes
**their square frames parallel**
to C and T.

Thus the **genuine four-square
parallel scaffold** is forced:
\[
\boxed{\text{frames}(C,A,T,B)
       \text{ all parallel}.}                  \tag{9}
\]
This derivation does **not**
assume T is circle-free. It uses
its *zero physical circle force*,
the exact neighbor gap of width
one, and the fact C and T
do not touch.

### 4. Physical circle force then forces R^2=5/2

The positive-cycle vertex cover
already proves \(m_A,m_B>0\).
The true parallel scaffold and
horizontal-directed contact normals
force the total physical contact
force at A and B to be strictly
horizontal and nonzero, with
only A--C and A--T positive at A,
and B--C and B--T positive at B.

Orient the shared side normal n
horizontally, with A left, B
right. Since C contains origin
and its own center is \((c,d)\)
with \(|c|,|d|<1/2\), its
opposite actual side contacts
give the normal center
coordinates
\[
p_A.x=c-1<0,\qquad p_B.x=c+1>0.
\]

For an axis-parallel unit square
with strictly negative or positive
center x and nonzero center y,
every vertex of **maximum
Euclidean norm** lies strictly on
the same y side of the origin
(the positive side if center y>0,
negative if center y<0).
Therefore a nonzero **horizontal**
contact resultant cannot equal
the positive combination of
its true circle vertices unless
the center y is zero.
The physical stationarity equations
and \(m_A,m_B>0\) hence force
\[
p_A.y=p_B.y=0.
\]

Both outer squares have positively
weighted **true disk-circle vertices**.
Their farthest squared vertex norms
must each equal \(R^2\), giving
\[
R^2=(c-3/2)^2+1/4
   =(c+3/2)^2+1/4.
\]
Therefore c=0 and
\[
\boxed{R^2=5/2.}                               \tag{10}
\]

But eight interior-disjoint unit
squares have total area eight
inside a disk of area \(\pi R^2\).
Thus \(R^2\ge8/\pi>28/11>5/2\),
using \(\pi<22/7\).
This contradiction shows the
assumption \(m_T=0\) was impossible,
proving \(m_T>0\).

Combined with the already
proved positive endpoint weights,
(1) follows. QED.

## Status and next genuine sharp proof obligation

This **strictly improves** the
earlier m=3 result which merely
excluded a *circle-free* internal T.
Now **even a T that happens to
touch the circle cannot have
zero circle multiplier** in the
pure C-two-actual-contact root.

Every stressed outer square in
the remaining m3 positive cycle
must contribute real physical
disk-circle force. The four
exterior spectator squares are
actually isolated and may be
chosen strictly circle-free,
but they remain present as
true unit squares in the disk.

Thus the unresolved pure m3
case has an exact full geometric
pattern:

* C circle-free and touching A,B
  on opposite actual side faces;
* A,T,B all **positively**
  circle-stressed;
* four completely isolated
  exterior outer squares with
  strict pairwise clearance,
  which may all be selected
  strictly circle-free.

This does **not** eliminate
the full pure m3 case, nor
the S4/k7 equality-bearing
full outer ring A, B3,
exterior stress root X,
higher m B2, or k<=6.
The unrestricted optimality
inequality \(R_8\ge\widehat R\)
and Lean 4 proof remain OPEN.

[verify_B2_m3_parallel_scaffold_exclusion.py](verify_B2_m3_parallel_scaffold_exclusion.py)
checks the exact final circle/area
contradiction. The new reduction
(5)--(9) is a complete hand
force and true-square support
argument, not a numerical
relaxation.
