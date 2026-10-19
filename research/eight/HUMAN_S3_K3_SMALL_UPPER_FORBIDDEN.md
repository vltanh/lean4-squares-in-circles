# S3/k=3: a small upper-cap offset forces a forbidden RU overlap

Research continuation, 2026-10-12. This is a **new exact continuous
subregion exclusion** in the surviving positive-ray S3/k=3 branch.
It does not close the entire S3/k=3 case and does not assign any
parallel square frames or inter-exterior contact graph.

## Theorem

Let eight pairwise interior-disjoint unit squares of arbitrary
orientations lie inside a disk with
\[
R^2\le q_+=9789/2500.
\]
Let C be the unique open origin-containing unit square. Suppose
all seven exterior squares have *exclusive* exactly-one-central-side
whole-square statuses, with populations
\[
R:3,\quad L:1,\quad U:2,\quad D:1
\]
(the S3=(3+1,2+1) branch), and exactly **k=3** exterior
centers have norm at least one. Write \(h_R,h_U\) for the
outward R/U central-side offsets.

Then the **upper two-square cap offset must satisfy**
\[
\boxed{h_U>23/200.}                                  \tag{1}
\]

Combined with the existing
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md),
the remaining S3/k=3 offset rectangle is thus
\[
\boxed{
17/200<h_R<13/100,\qquad 23/200<h_U<1/5.
}                                                        \tag{2}
\]
The full remaining positive-ray S3/k=3 configuration has
*not* been proved impossible.

## 1. Elementary two-square obstruction

We first prove a standalone lemma using only necessary
square-center geometry in the n=8 radius ceiling.

**Lemma.** Let P and Q be two distinct unit squares in the disk,
with pairwise disjoint open interiors. Assume P's center
\(p=(p_x,p_y)\) satisfies
\[
|p|<1,\quad p_x>117/200,\quad p_y>0.               \tag{3}
\]
Assume Q's center \(q=(q_x,q_y)\) has
\[
|q|\ge1,\quad
311/500<\psi:=\arg(q)<8959/10500.                \tag{4}
\]
If Q is **not** wholly contained in the half-plane
\(\{y\ge h\}\) for some \(h\le23/200\), then
the two centers have distance **strictly less than one**,
contradicting their disjoint half-unit inscribed disks.

**Proof.** For an arbitrarily rotated unit square,
the half-width in the vertical direction is at most
\[
\frac{\sqrt2}{2}<177/250,
\]
the final rational inequality following by squaring
\((177/250)^2>1/2\).

Because Q is **not** wholly in \(y\ge h\), its
minimum vertex y-coordinate is less than h. Hence
\[
q_y<h+h_Q(e_y)
\le23/200+\sqrt2/2
<23/200+177/250
=823/1000=:Y.                                       \tag{5}
\]

From (4), \(\psi>\pi/6\) and \(\psi<\pi/3\).
Indeed \(\pi/6<11/21<311/500\) uses
\(\pi<22/7\), whereas \(8959/10500<1<\pi/3\).
Since \(|q|\ge1\), this gives
\[
q_y=|q|\sin\psi>1/2,\qquad
q_x=|q|\cos\psi>1/2.                               \tag{6}
\]
We next give a hand-checkable lower bound for
\(\tan\psi\). On \((0,\pi/2)\), the identity
\((\tan x)'=1+\tan^2x\), together with \(\tan x>x\),
implies successively
\[
\tan x>x+x^3/3
\quad\text{and}\quad
\tan x>x+x^3/3+2x^5/15.
\]
For the second inequality, insert the first into
\(\tan'=1+\tan^2\) and integrate:
\(\tan' >1+x^2+(2/3)x^4\).
At \(x=311/500\), the polynomial lower bound
has the strictly positive exact margin
\[
\left[x+x^3/3+2x^5/15\right]_{x=311/500}
-\frac{357}{500}
=\frac{147034397551}{234375000000000}>0.
\]
Thus
\[
\tan\psi>\tan(311/500)>357/500.                    \tag{7}
\]
Equations (5) and (7) show
\[
q_x=\frac{q_y}{\tan\psi}
<\frac{823/1000}{357/500}
=\frac{823}{714}.                                 \tag{8}
\]

For the inner center p, (3) gives
\(117/200<p_x<1\) and \(0<p_y<1\).
From (6),(8), the **absolute coordinate gaps** satisfy
\[
|q_x-p_x|<
\max\left\{\frac{823}{714}-\frac{117}{200},
                    1-\frac12\right\}
=\frac{40531}{71400},
\]
\[
|q_y-p_y|<
\max\left\{\frac{823}{1000},1-\frac12\right\}
=\frac{823}{1000}.
\]
Therefore
\[
|p-q|^2
<\left(\frac{40531}{71400}\right)^2
 +\left(\frac{823}{1000}\right)^2
=1-\frac{27523627}{63724500000}<1.                \tag{9}
\]
But two interior-disjoint unit squares contain
disjoint open inscribed disks of radius \(1/2\),
and hence their centers must be distance at least
one. This contradiction proves the lemma. QED.

## 2. Apply to the exclusive S3/k=3 branch

For exclusive S3/k=3, the L and D far-side
singletons have **outer** centers, and the R triple
has exactly one outer and two inner centers.
The two U side squares are inner. The
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
two-inner-center cap theorem implies the
two inner R centers lie on *opposite sides of the
horizontal diameter*. In particular, there is
a distinct **positive-y inner R center** P.
Its whole right-cap membership and the previously
proved strict lower bound \(h_R>17/200\) give
\[
p_x\ge h_R+1/2>117/200,\quad p_y>0,\quad |p|<1.
\]

Let Q be the **sole outer R** square.
The proved
[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md)
eliminates the negative angular alternative; the
positive one is strictly
\[
311/500<\arg(q)<8959/10500.
\]
Crucially, Q is a **single R-side status** square.
It does **not** have a U-side whole-square
separator, so Q is **not** wholly contained
in \(\{y\ge h_U\}\). This is why the lemma's
nonmembership hypothesis holds; merely being an
R-cap square would not be sufficient.

If \(h_U\le23/200\), P and Q satisfy every
hypothesis of the two-square lemma, contradicting
center separation. Hence \(h_U>23/200\).
Combining with the existing strict upper bound
\(h_U<1/5\) proves (1)–(2). QED.

## Exact status and next step

The newly excluded **entire continuous strip**
is \(h_U\le23/200\) within the exclusive
S3/k=3 branch. The only still-possible
offset interval is \(23/200<h_U<1/5\).
The R-outer center's positive angular lane, the
far L/D singleton center strips, and the
four-inner-center angular fan must still be
coupled to the actual square frames and
mutual separating axes to obtain a sharp bound.

No unrestricted theorem \(R_8\ge\widehat R\),
global equality classification, or Lean handoff
is claimed. The exact S4/k=7 equality packing
is untouched.

[verify_s3_k3_small_upper_gate.py](verify_s3_k3_small_upper_gate.py)
audits the rational margins, not the continuous
proof argument or a generated classifier.
