# n=9: complete table-free theorem for stratified, independently rotating squares

**Status:** complete hand proof for the explicitly stated stratified
class. **Unrestricted nine-square optimality remains OPEN.**
This extends the earlier stratified result in
[HAND_PROOF.md](HAND_PROOF.md) from *one common square orientation*
to **all nine independently oriented squares**.

The only analytic input is the new universal sharp cap-row bound
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md),
Theorem 3.1 and Corollary 3.2. No numerical case table is used.

## Definition

An **orientation-free horizontal stratification** of a finite
packing in the disk centered at zero consists of nonempty layers
\(L_1,\ldots,L_k\), partitioning its squares, with:

1. Each layer's squares have pairwise disjoint *horizontal
   projection interiors*, regardless of their own orientations.
2. Every square of layer \(L_{i+1}\) lies entirely on or above
   every square of layer \(L_i\).

All square orientations may differ. Each square's horizontal and
vertical half-projection widths equal
\(h_i=(|\cos\theta_i|+|\sin\theta_i|)/2\ge1/2\).

In particular, if squares belong to layers \(i<j\), then the
vertical centers satisfy
\[
             y_j-y_i\ge j-i. \tag{1}
\]
This follows by chaining complete support separation and using
two halfwidths, each at least 1/2. No row is assumed to
have a common center height or common orientation.

## 1. Three elementary global witnesses

Write \(q_*=1105/256\) and assume a packing lies in a disk
of squared radius \(q\le q_*\).

For a square with center \(c=(x,y)\) and unit orthogonal
side axes \(u,v\), disk containment entails
\[
 q\ge |c|^2+\frac12+|c\cdot u|+|c\cdot v|
       \ge |c|^2+\frac12+|c|. \tag{2}
\]
The last step is the \(\ell^1\)-to-\(\ell^2\)
comparison in the square's orthonormal frame.

**Lemma 1.1 (center bound).** Every square center has
\[
                        |y|<25/16. \tag{3}
\]
Indeed, if \(|c|\ge25/16\), (2) would give
\(q\ge625/256+1/2+25/16=1153/256>q_*\).

A horizontally separated layer of \(m\) squares has centers
ordered by \(x\), with successive gaps at least 1.
Therefore an endpoint center satisfies
\[
                       |x|\ge(m-1)/2. \tag{4}
\]

**Lemma 1.2 (two-square witness).** Any horizontally
separated layer with at least two squares contains a center
with \(|y|<23/16\).

*Proof.* For the extremal witness from (4), \(|x|\ge1/2\).
If \(|y|\ge23/16\), then
\[
 |c|^2\ge 1/4+(23/16)^2=593/256>9/4,
\]
so \(|c|>3/2\). Formula (2) gives the **strict** bound
\[
 q>593/256+1/2+3/2=1105/256=q_*,
\]
a contradiction. \(\square\)

**Lemma 1.3 (four-square witness and maximum layer size).**
Any horizontally separated layer of four squares contains
a center with \(|y|<7/16\). No horizontally separated
layer can have five squares.

*Proof.* The four-square witness from (4) has \(|x|\ge3/2\).
If also \(|y|\ge7/16\), (2) yields
\[
 q\ge9/4+(7/16)^2+1/2+3/2
   =1137/256>q_*.
\]
For five squares (4) gives \(|x|\ge2\), so
\(q\ge4+1/2+2=13/2>q_*\). \(\square\)

All three lemmas hold for arbitrary orientations.

## 2. Cap restrictions for groups of three and four

Let \(b(L)\) denote the *minimum* vertical coordinate among
all points of all squares in a layer, and \(t(L)\)
the *maximum*.

By the sharp independently rotated cap-row lemma, every
horizontally separated layer of at least three squares
in this disk satisfies
\[
                b(L)\le7/16,\qquad t(L)\ge-7/16.
                \tag{5}
\]
And every layer of four squares satisfies the stronger
\[
                b(L)\le-7/16,\qquad t(L)\ge7/16.
                \tag{6}
\]

*Proof.* For a three-square layer, suppose
\(b(L)>7/16\). If \(b(L)\ge1/2\), use floor
\(s=1/2\) in the m=3 cap-row theorem, giving
\(q\ge9/4+(3/2)^2=9/2>q_*\).
If \(7/16<b(L)<1/2\), the same theorem at
\(s=b(L)\) gives
\(q\ge9/4+(s+1)^2>9/4+(23/16)^2=q_*\).
Therefore \(b(L)\le7/16\).
Reflecting y gives \(t(L)\ge-7/16\).

For a four-square layer, if \(b(L)>-7/16\),
use the m=4 cap-row theorem at floor \(s=b(L)\)
when \(s<1\), or floor \(s=1\) otherwise.
In either case
\(q>4+(9/16)^2=q_*\).
Reflecting yields \(t(L)\ge7/16\). \(\square\)

We will use (5)--(6) only as **necessary support heights**,
not as a conjectured grid normalization.

## 3. The full stratified nine-square theorem

**Theorem 3.1 (independently rotated stratified n=9).**
If nine independently oriented unit squares fit in a
circle and have an orientation-free horizontal stratification,
then their containing radius satisfies
\[
                       R^2\ge q_*=\frac{1105}{256}. \tag{7}
\]
If equality holds, every stratification has exactly three
layers, and from bottom to top the layer cardinalities are
\[
                       (3,4,2)\quad\text{or}\quad(2,4,3).
                       \tag{8}
\]
In either equality case the three-square and four-square
layers must align with the chosen horizontal frame and
have the seven-anchor rigidity specified in
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md),
Corollary 4.2. The two-square layer may contain
rotated squares.

*Proof.* It suffices to assume \(q\le q_*\).
Let \(k\) denote the number of nonempty layers and
\(m_i=|L_i|\). By Lemma 1.3, every \(m_i\le4\).

**Case k≤2:** The total number of squares is at most 8.

**Case k≥5:** By (1), a center in the last layer
is at least 4 units above a center in the first.
By (3), the difference between any two center
heights is strictly below \(50/16<4\). Contradiction.

**Case k=4:** By (1) and (3), all centers in
the first layer have
\(y<25/16-3=-23/16\); all centers in the last
have \(y>-25/16+3=23/16\).
By Lemma 1.2, neither extreme layer can contain
two squares. So \(m_1=m_4=1\).

All centers in the second layer have
\(y<25/16-2=-7/16\), and all centers in
the third layer have
\(y>-25/16+2=7/16\).
By Lemma 1.3, neither intermediate layer
can contain four squares. Hence the total is
at most \(1+3+3+1=8\), impossible.

**Case k=3 and no layer has four squares:**
All layers must have size 3.
By (5), the first layer has
\(t(L_1)\ge-7/16\) and the last has
\(b(L_3)\le7/16\).
Since a square in the intermediate layer has
vertical projection width at least 1, complete
vertical separation yields
\[
              b(L_3)-t(L_1)\ge1.
\]
But the necessary support bounds give
\(b(L_3)-t(L_1)\le14/16<1\).
Contradiction.

**Case k=3 and a four-square layer is extreme:**
If \(m_1=4\), (6) gives \(t(L_1)\ge7/16\).
An intermediate square has vertical width at
least 1. Complete support separation then
forces every point of the last layer to have
\(y\ge7/16+1=23/16\).
Consequently every last-layer center has
\(y\ge23/16+1/2=31/16\), contradicting (3).
Reflection gives the same contradiction if
\(m_3=4\).

**Case k=3 and the middle layer has four:**
The extreme layers contain five squares together,
each at most three, so their sizes must be
\((m_1,m_3)=(3,2)\) or \((2,3)\).
The four middle squares and the three squares in
the appropriate extreme layer satisfy all the
hypotheses of the **independently rotated**
seven-anchor obstruction, Theorem 4.1 in
ORIENTATION_STABLE_SEVEN_ANCHOR.md. Thus
\(q\ge q_*\).

Every case is covered; there are no positional
or angle-grid subcases. At \(q=q_*\), all
contradictions except the last remain strict.
In that last case equality in G1 supplies
the seven-anchor alignment and rigidity.
\(\square\)

## 4. Attainment and rotations at equality

The exact model in [HAND_PROOF.md](HAND_PROOF.md),
Section 1, attains \(q=q_*\) with layers (3,4,2).

The more flexible exact model in
[NONRIGID_WITNESS.md](NONRIGID_WITNESS.md)
also has a stratification in the same frame:
the two upper squares have disjoint horizontal
projections by its equation (1), and the
rotated upper square has strictly positive
vertical clearance above the four-square
middle layer by its equation (2).
Thus it is an exact rotated equality example.

This proves the theorem's equality structure
cannot require all nine square frames to agree.

## 5. Dependency boundary and next step

Theorem 3.1 is **unconditional inside the
orientation-free stratified class**, but
stratifiability itself is an explicit extra
hypothesis; G2 has not shown that an arbitrary
nine-square packing can be organized into
these layers, or that all nonstratified
packings are impossible below \(q_*\).

This theorem closes the **stratified terminal
branch of G3**. The missing task is an
exhaustive *global* structural theorem
from the original Packing predicate.
If G2 produces a genuinely nonstratified
branch, it requires a separate analytic
obstruction; this document does not
classify or discard it.

No Lean compilation, CI or kernel audit was run.
