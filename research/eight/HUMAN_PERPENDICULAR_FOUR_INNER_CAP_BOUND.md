# A sharp angular sum bound for four inner-center squares in perpendicular whole caps

Research continuation, 2026-10-12. This is a **general full-orientation
four-square lemma** and a strong *conditional* geometric reduction in the
remaining exclusive-single-side low-k cases. It is not a proof of the
unrestricted eight-square optimum.

## Theorem (two disjoint inner-center pairs)

Let four **distinct** unit squares with pairwise disjoint open
interiors have centers of Euclidean norm **strictly less than one**.
Suppose two of the squares are wholly in the outward cap
\(x\ge h_x\ge0\), and the other two are wholly in the
**perpendicular** outward cap \(y\ge h_y\ge0\).

Then the positive normal offsets obey the **strict quarter-circle
inequality**
\[
\boxed{(h_x+1/2)^2+(h_y+1/2)^2<1.}              \tag{1}
\]

No disk-containment ceiling beyond the stipulated center norms
is used. The four square frames may be completely unrelated;
the claim depends on actual whole-square cap membership,
not just positive center-coordinate signs.

## Proof

Put \(a=h_x+1/2\), \(b=h_y+1/2\), so \(a,b\ge1/2\).
Every square has half-width at least \(1/2\) in every unit
normal direction, so each x-cap center has
\(x\ge a\), and each y-cap center has \(y\ge b\).
Since all four center norms are \(<1\), necessarily
\(a,b<1\).

As in
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md),
any two distinct centers of norm \(<1\) with mutual
distance \(\ge1\) have smaller angular separation
**strictly greater than \(\pi/3\)**.

Apply the same note's transverse-sign theorem to the
two x-cap centers: one has negative y and one positive y,
so write their signed polar angles as \(X_-,X_+\), with
\[
-\arccos a<\theta_{X_-}<0<
\theta_{X_+}<\arccos a\le\pi/3.                  \tag{2}
\]
The two y-cap centers similarly have opposite x signs,
so write their angles as \(Y_+,Y_-\):
\[
\arcsin b<\theta_{Y_+}<\pi/2<
\theta_{Y_-}<\pi-\arcsin b.                      \tag{3}
\]

We must establish the **correct four-ray order**. Both
\(X_+\) and \(Y_+\) are in the NE quadrant, and belong to
different actual squares. If \(\theta_{X_+}\ge\theta_{Y_+}\),
their angular difference would be less than
\(\pi/3-\pi/6=\pi/6\), contradicting the inner-center
\(>\pi/3\) angular separation (use \(a,b\ge1/2\)
in (2)–(3)). Therefore the order is
\[
\theta_{X_-}<\theta_{X_+}<
\theta_{Y_+}<\theta_{Y_-}.                        \tag{4}
\]

Each of the **three successive center pairs** in (4)
is a distinct inner-center pair, hence has an
ordinary angular gap \(>\pi/3\) (the full span
is less than \(4\pi/3\), but each adjacent
gap is \(<\pi\), so the ordinary gap equals
the smaller center-ray separation).
Adding the three strict gaps gives
\[
\theta_{Y_-}-\theta_{X_-}>\pi.
\]
But the bounds (2)–(3) imply
\[
\theta_{Y_-}-\theta_{X_-}
<\pi-\arcsin b+\arccos a.
\]
Consequently
\[
\arccos a>\arcsin b.
\]
Both angles lie in \((0,\pi/2)\); cosine is
strictly decreasing, so
\(a<\cos(\arcsin b)=\sqrt{1-b^2}\), i.e.
\(a^2+b^2<1\). This is (1). QED.

## Immediate general corollary

If two disjoint whole-square cap populations of
size at least two are perpendicular, and **all four
selected centers are inner**, their radial side offsets
cannot lie in the closed region
\[
(h_x+1/2)^2+(h_y+1/2)^2\ge1.
\]
The conclusion is purely a necessary obstruction to that
*four-inner-center subcase*: the same cap counts are allowed
if one or more centers are **outer**.

## Consequences for exact low-k D0 classes

Let \(k\) denote the number of **exterior** centers with
norm \(\ge1\), and maintain *exclusive* one-side statuses.

**S1/k=3.** The three exterior outer labels are the D singleton
and one member from each of its perpendicular R/U triples.
The other four labels are two inner R and two inner U squares;
therefore
\[
(h_{30}+1/2)^2+(h_{31}+1/2)^2<1.
\]
This is a new strict *curved* necessary region, complementary
to the existing low-offset pierced rectangles.

**S2/k=3.** Normalize R=3,L=0,U=2,D=2 and choose U as
the *nearer* two-square cap. The two far D centers are outer,
and one R triple center is outer. The remaining two R and
two U members are inner, so
\[
(h_R+1/2)^2+(h_U+1/2)^2<1,\qquad h_U>7/24.
\]
It follows that
\[
h_R<\sqrt{1-(19/24)^2}-1/2
=\frac{\sqrt{215}-12}{24}<13/100.
\]
This is the four-ray mechanism of
[HUMAN_S2_K3_INNER_FAN.md](HUMAN_S2_K3_INNER_FAN.md).

**S3/k=3.** Normalize the 3+1 axis to R=3,L=1,
and the other axis to U=2,D=1.
The L singleton is outer. If the U two-member cap had
offset \(\ge1/2\), its two members would both be outer,
giving at least four outer labels together with L and
one member of R. Hence its offset \(h_U<1/2\), and
the opposite D singleton is outer. Exactly two R and
two U labels are therefore inner. By the distant L
singleton's one-square cap envelope,
\(h_R>17/200\), and (1) gives
\[
\boxed{
h_U<\sqrt{1-(117/200)^2}-1/2
=\frac{\sqrt{26311}-100}{200}
\approx0.311.
}                                                 \tag{5}
\]
This improves the earlier necessary \(h_U<H_*\approx0.366\)
for S3/k=3. The separate triple theorem still
forces \(h_R<13/100\).

**S4/k=3 (equality-bearing *status* family).**
Normalize its opposite-pair populations to
a 2+1 axis (two side offset \(h_A\), opposite singleton)
and a perpendicular 2+2 axis (near two side offset \(h_B\),
far two side). The far two members are always outer.
If \(h_A\ge1/2\), its two members are also outer,
contradicting k=3. Thus \(h_A<1/2\) and the
opposite singleton has offset \(1-h_A>1/2\)
and is outer. Since k=3 exactly, the two A cap
members and the two **near** B cap members are all
inner, with disjoint labels.

The 2+2 offset bound gives
\(h_B>7/24\), so (1) forces
\[
h_A<\frac{\sqrt{215}-12}{24}.
\]
The opposite A singleton's arbitrary-frame cap-envelope
bound forces \(h_A>17/200\).
Moreover two inner B cap members require
\(h_B<H_*=(\sqrt3-1)/2\). Therefore the entire
still-possible S4/k=3 subcase is confined to
\[
\boxed{
17/200<h_A<(\sqrt{215}-12)/24,\quad
7/24<h_B<(\sqrt3-1)/2,\quad
(h_A+1/2)^2+(h_B+1/2)^2<1.
}                                                 \tag{6}
\]
This is a **much narrower continuous necessary region**
than the previous \(h_A<H_*\) and central offset strip.
It **does not reject S4 as a whole**: in particular,
its real \(k=7\) equality realization is unaffected.

## What is still open

The four-inner-center lemma does not prove that any of
the displayed residual low-k regions is realizable.
It does not cover D1/D2 in which cap labels overlap or
corner-only members are present without first verifying
four genuinely distinct inner centers. It supplies no
unrestricted radius lower bound \(R_8\ge\widehat R\).
