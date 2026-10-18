# The m=3 shared parallel-transmitter scaffold is incompatible with positive physical stress

**2026-10-13. Complete structural elimination of one of the two
remaining k=7/B2/m=3 pure-central-contact alternatives.**
This is an *all-frame global n=8 force/support contradiction*, not
a local cap-constant optimization. The actual seven-outer full
contact-ring equality case is preserved.

## Theorem

Consider an attained least-radius packing of eight pairwise
interior-disjoint genuine unit squares in \(D_R\), with the
fewest actual square-square contacts among all least-radius
packings and with \(R<2\).
Let C be its unique open origin-containing square.

Assume:

1. The seven exterior square centers have norm at least one,
   and the outer-induced *actual* contact graph is **not**
   the full seven-square cycle.
2. A normalized physical stress has exactly two positive
   C-contact neighbors and is the simple cycle
   \[
   C-A-T-B-C
   \]
   with three **consecutive outer-ray** labels A,T,B.
3. C has **exactly two actual square contacts**, namely A and B.
4. The *internal stressed path square* T has **no true
   disk-circle contact** (all its vertices are strictly
   inside \(D_R\)).

Then such a packing **cannot exist**.

Equivalently, every still-unexcluded k=7,
C-positive-degree-two, C-actual-degree-two,
stressed outer path of size m=3 has
\[
\boxed{\text{the internal outer square }T
       \text{ touching the containing circle}.}      \tag{1}
\]
Both outer endpoints A and B also have positive
circle-vertex multipliers by the general
positive-cycle vertex-cover theorem. Hence
**all three stressed outer squares have actual
circle contact**, with the endpoint contacts
positively weighted by the physical stress.

This excludes **the entire circle-free m3
four-square parallel scaffold subbranch**;
it does not eliminate the m3 branch
with a circle-contacting T.

## 1. True square contacts force four common parallel frames

Since C contains zero and \(R>\sqrt2\),
it is strictly circle-free. With exactly
two *actual* neighbors A and B in a
contact-minimal minimizer, the exact
interior transmitter theorem in
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md),
section 8, forces C's two opposite
actual separators to be **parallel
to one of C's true side normals**.

The internal square T has positive-stress
actual contacts with A and B and no
contact with C because C has only
the actual neighbors A,B. Since k=7,
the outer-center visibility theorem
prohibits any additional exterior
contact of T outside A,B.
Thus T has **exactly two actual
square-square neighbors**, A and B.
By hypothesis T is strictly circle-free,
so the same interior transmitter
theorem forces its two opposite
contact normals to align with T's
true square side.

C and T are therefore two different,
strictly circle-free, actual-degree-two
transmitters with the **same pair of
actual neighbor squares A,B**.

The established exact
**shared-transmitter theorem**
in HUMAN_CYCLE_ANALYSIS.md section 9
proves that all four genuine frames
\[
\boxed{C,\ A,\ T,\ B
       \text{ are parallel},}                      \tag{2}
\]
and A,B have an exact common-normal
surface-to-surface separation of one,
with C and T between them.

Rotate/reflect so their common
frame axes are horizontal and
vertical, with A to the left,
B to the right. Write
\[
p_C=(c,d),\quad |c|,|d|<1/2.
\]
Because the three actual contact
edges A--C--B have common horizontal
normal and all three squares are
unit axis-parallel, their centers
satisfy exactly
\[
\boxed{p_A=(c-1,a),\qquad
       p_B=(c+1,b)}.                          \tag{3}
\]
In particular \(c-1<-1/2\) and
\(c+1>1/2\). The alternative
transmitter T shares this same
normal gap but has a different
vertical center coordinate.

## 2. The two exterior endpoints have positively weighted true circle vertices

The new general
[HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md](HUMAN_STRESS_CYCLE_POSITIVE_CIRCLE_COVER.md)
theorem applies to the positive
four-cycle C-A-T-B-C:
it proves that **no two adjacent
positive cycle squares can both
have zero total circle multiplier**.
Because C is circle-free and hence
has total circle multiplier zero,
\[
\boxed{m_A>0,\qquad m_B>0.}                    \tag{4}
\]

Thus A,B each have at least one
**genuinely positively weighted**
vertex on the containing circle.
No assumption that T itself has
positive circle weights is made.

The **only two positive pair-contact
forces acting on A** are from
C and T, both located to its right.
Since the square frames are all
parallel by (2), the pair-contact
separating normals are horizontally
directed. Thus the total positive
pair-contact resultant force
\[
F_A=\lambda_{AC}(-1,0)
   +\lambda_{AT}(-1,0)
\]
is strictly horizontal and nonzero.
The corresponding F_B is horizontal
and nonzero in the positive direction.

By the exact physical circle-force
equilibrium from
[HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md)
section 4,
\[
F_A=2\sum_{\alpha}\mu_{A,\alpha}
       x_{A,\alpha},
\quad
F_B=2\sum_{\alpha}\mu_{B,\alpha}
       x_{B,\alpha},
\]
with **nonnegative** vertex multipliers,
some positive on A and B.

We show that this forces
\[
\boxed{a=b=0.}                                  \tag{5}
\]
Consider axis-parallel A, whose center
is \((c-1,a)\), with \(c-1<0\).
Among its four vertices, the vertices
of maximal Euclidean norm have
leftmost x-coordinate \(c-3/2<0\)
and, when \(a\ne0\), the **unique**
furthest y-coordinate
\(a+\operatorname{sgn}(a)/2\).
Thus if \(a>0\), every vertex
of A on \(|x|=R\) has strictly
**positive y**, and if \(a<0\),
every such vertex has strictly
**negative y**. No nonnegative
positive combination of such
circle vertices can have **zero
vertical coordinate**, contrary
to the horizontal nonzero force
\(F_A\) and \(m_A>0\).
Therefore \(a=0\).
The same argument at B, using
its strictly positive center x
and horizontal force, gives \(b=0\).

This conclusion uses the **physical
stress sign** of circle multipliers:
a mere declaration that A and B
both touch the circle would not
force their vertical centers to
be zero.

## 3. True circle vertices now fix R^2=5/2, impossible for eight squares

With a=b=0 and the exact horizontal
center coordinates (3), A and B
have two furthest vertices each:
\[
\big(c-\tfrac32,\ \pm\tfrac12\big)
\quad\text{for A},\qquad
\big(c+\tfrac32,\ \pm\tfrac12\big)
\quad\text{for B}.
\]
Since A and B have **positive
circle multipliers**, the norm
of a furthest true vertex
must equal R for each square.
Consequently
\[
R^2=(c-3/2)^2+1/4
    =(c+3/2)^2+1/4.
\]
Subtracting gives c=0, and
thus
\[
\boxed{R^2=5/2.}                              \tag{6}
\]

But **eight interior-disjoint
unit squares have total area eight**.
The containing disk has area
\(\pi R^2\), so
\[
8\le\pi R^2,\qquad
R^2\ge8/\pi>8/(22/7)=28/11>5/2,
\]
using the elementary strict
inequality \(\pi<22/7\) and
\(28/11-5/2=1/22>0\).

This contradicts (6).
Therefore T must actually
touch the disk circle and the
circle-free parallel-scaffold
case is **entirely impossible**.
QED.

## Sharpened global m=3 pure-C contact consequences

[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
already proves that the four
nonstressed exterior spectator
squares of this m=3/B2/pure root
are actually isolated, and can
be chosen strictly circle-free
without affecting minimum radius
or contact graph.

The previous theorem allowed two
alternatives for its sole internal
outer square T: either circle
contact or a rigid four-parallel
scaffold. The present theorem
**rules out the second alternative
completely** at the physical
stress/radius level. Hence the
current pure m3 root necessarily
has **ALL THREE** stressed outer
labels A,T,B truly touching
the containing circle, and A,B
with strictly positive circle
multipliers.

The root with such a boundary-
anchored T remains open. Other
B2 stressed path sizes m4,5,6,
the central branching and
exterior stressed-cycle roots,
and the genuine sharp
outer seven-contact equality
ring are not excluded.

This is a hand proof using
true square orientations,
positive physical forces,
actual contacts, and elementary
area. It is not a numerical
optimizer result, radius
interval tune-up, or Lean 4
formalization. The unrestricted
\(R_8\ge\widehat R\)
remains OPEN.
