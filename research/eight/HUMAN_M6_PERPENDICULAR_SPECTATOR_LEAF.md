# The spectator leaf in the k=7, m=6 two-force root is perpendicular to the stressed central axis

**2026-10-12. Exact global structural hand theorem, not an n=8
radius optimality proof.** This strengthens **mode S** from
[HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md](HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md)
when the sole outer spectator T has exactly one actual
square contact, with the central square C.

## Theorem (orthogonal spectator leaf)

Assume an eight-unit-square *contact-minimal radius
minimizer* at squared disk radius
\[
R^2\le q_+:=9789/2500,
\]
whose seven noncentral square centers are outer.
Assume the outer actual-contact graph is a
**proper** subgraph of the seven-ray neighbor cycle,
and the physical stress has exactly two positive
C-contact neighbors at *opposite C side normals*
\(\pm n\). Its stressed six-outer path is
\(C-S_1-\cdots-S_6-C\), with seventh
outer spectator T.

Suppose C actually touches **exactly**
S1, S6 and T, while T has no actual
square contact other than its C contact
(i.e. T is an **actual leaf**).

Then T's unique actual contact normal
\(m\) directed from C toward T is one of the
two **perpendicular** C side normals:
\[
\boxed{m=\pm Jn.}                                \tag{1}
\]
In particular:

* T's unit-square frame is **parallel to C's frame**;
* T's center is **radial along the perpendicular
  side normal** \(m\);
* T has **two true vertices on the
  containing circle**, as required by
  the exact actual-leaf theorem;
* no leaf spectator can occupy either of
  C's two positively stressed side directions
  \(\pm n\).

This is a genuine **finite contact-orientation
reduction** in one of the remaining global B2
stress roots. It does not assert that the
resulting perpendicular scaffold is impossible,
nor does it eliminate the actual seven-outer
equality contact ring.

## 1. A two-square capacity fact at the leaf's actual side offset

We need only the following already justified
arbitrary-frame cap geometry:

**Lemma.** Under \(R^2\le9789/2500\),
a whole cap with outward offset
\[
h\ge4/5
\]
can contain **at most one** unit square.

**Proof.** Assume two distinct whole unit
squares P,Q lie beyond that line,
which by rotation may be \(y\ge h\).
The true projected half-width of every
unit-square frame is at least 1/2, so
their center y coordinates each satisfy
\[
13/10\le p_y,q_y<r_0:=283/200.
\]
The universal upper center norm \(r_0\)
holds by the exact farthest-vertex
inequality for every frame.

The separately proved **sharp full-frame
one-square cap envelope**
HUMAN_ONE_SQUARE_CAP_ENVELOPE.md is
valid at \(h\ge4/5>2/5\), and yields
\[
(|p_x|+1/2)^2
\le q_+-(1+h)^2
\le q_+-(9/5)^2
< (5/6)^2.
\]
The last strict exact squared margin is
\[
(5/6)^2-[q_+-(9/5)^2]
=\frac{106}{5625}>0.
\]
Thus both centers satisfy
\[
|p_x|,|q_x|<1/3.
\]
Their center-coordinate differences
therefore obey
\[
|p_x-q_x|<2/3,\qquad
|p_y-q_y|<r_0-13/10=23/200.
\]
Their squared distance is consequently
\[
|p-q|^2<
(2/3)^2+(23/200)^2
=\frac{164761}{360000}<1,
\]
with strict reserve \(195239/360000>0\).
But any two disjoint-interior unit squares
must have center distance at least one,
by their open inscribed radius-1/2 disks.
Contradiction. QED.

## 2. The leaf side offset exceeds 4/5

The true contact-minimal **actual-leaf theorem**
[HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md),
section 1, applies to the spectator T,
which has exactly one actual neighbor C.
Write
\[
\rho=\sqrt{R^2-1/4},\qquad b=\rho-1.
\]
The leaf theorem states that T's contact
normal m is a side normal of **both** T
and C, the actual common C support line
is \(m\cdot x=b\), the T center is radial
\(p_T=(\rho-1/2)m\), and its two exterior
vertices touch the containing circle.

For an eight-square radius minimizer,
the established lower radius bound is
\[
R>\sqrt2+1/2.
\]
Consequently
\[
\rho^2=R^2-1/4>2+\sqrt2
>2+31/25=(9/5)^2,
\]
because \(\sqrt2>31/25\) is an elementary
positive rational square comparison.
Thus
\[
\boxed{b=\rho-1>4/5.}                          \tag{2}
\]

The **entire real unit square T** therefore
lies beyond the central-owned side line
\(m\cdot x=b>4/5\). By the cap lemma,
**no different unit square** can also lie
wholly beyond that *same* line in the
current search disk.

## 3. The stressed opposite side normals cannot coincide with the leaf direction

The two positive C-force neighbors
S1 and S6 have opposite unit normal
directions \(+n\) and \(-n\).
By the central two-force normal theorem
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md),
and because mode S has only three
**actual** C neighbors,
the diagonal mode is impossible by
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md).
Hence n is a **true C side normal**.

T's leaf normal m is another true
C side normal by the leaf theorem.
Therefore \(m\) must be one of the
four signed central side normals
\[
m\in\{+n,-n,+Jn,-Jn\}.
\]

Suppose \(m=+n\).
The positive-stress neighbor of C in
direction +n, say S1, lies **wholly**
beyond C's same outward support line
\(n\cdot x=b\), because the C--S1
contact uses n as its true separating
normal. T is also wholly beyond this
line by section 2. They are distinct
interior-disjoint true unit squares
inside the same disk, contradicting
the cap-capacity lemma at \(b>4/5\).

If \(m=-n\), the identical argument
applies to the other positive-stress
neighbor S6 in direction -n:
the C-support side line is at the
same leaf offset b, so T and S6 would
violate the same cap-capacity lemma.

Thus \(m\ne\pm n\). The only remaining
true C side normals are
\[
m=\pm Jn,
\]
proving (1). The leaf's parallel frame,
radial center and disk-vertex contacts
are already consequences of the actual
leaf theorem. QED.

## Further global structural implications

This narrows **mode S** of the surviving
k=7/B2/m=6 root to two possibilities:

* **S0: spectator T is an actual leaf.**
  Its square frame is parallel to C;
  its radial center direction is
  one of the **two perpendicular central
  side normals** ±Jn, and two of its
  true vertices lie on the disk circle.
* **S1: spectator T additionally touches
  one endpoint S1 or S6 of the outer
  stressed path.** By
  HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md
  it still has a genuine true disk-circle
  vertex, but no parallelism or
  perpendicular leaf-normal conclusion
  may be imposed without further proof.

Mode P requires a stressed endpoint
on the disk circle; mode K has a
central-to-internal stressed-path
**zero-positive-weight actual chord**.
The complete k=7/B2/m=6 root still
needs a **sharp whole-packing radius
inequality** in these three modes.
The correct equality-bearing outer
full-contact ring remains separate
and untouched.

[verify_m6_perpendicular_leaf.py](verify_m6_perpendicular_leaf.py)
audits the finite exact rational
cap-capacity and radius-gap identities;
the orientation conclusion follows
from the full hand proof, not from
a floating-point graph optimizer.
