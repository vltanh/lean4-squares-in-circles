# Narrower exact outer-R angular sectors in the remaining S3/k=3 branch

Research continuation, 2026-10-12. This strengthens the two
outer-R center-ray sectors in
[HUMAN_S3_K3_REMAINING_TWO_LANES.md](HUMAN_S3_K3_REMAINING_TWO_LANES.md)
without claiming the remaining branch is realizable or closed.

## Theorem

Let eight pairwise interior-disjoint unit squares fit in the
disk \(R^2\le9789/2500\), with the unique open central
square C. Suppose all seven exterior squares have
**exclusive** central-owned whole-square side status
S3=(3+1,2+1), normalized as
\[
R:3,\ L:1,\ U:2,\ D:1,
\]
and exactly \(k=3\) exterior square centers have norm \(\ge1\).

The previously proved offset restrictions, including
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md),
are
\[
17/200<h_R<13/100,\qquad
17/200<h_U<1/5.
\]
There is one **outer** R-square center and two **inner**
R-square centers; both U centers are inner, and the
L,D far singletons are outer.

Write \(\psi\in(-\pi,\pi]\) for the sole outer R-center
ray angle measured from +x. It necessarily satisfies
the much narrower, **strict** alternative
\[
\boxed{-\pi/9<\psi<-2041/10500}
\quad\text{or}\quad
\boxed{311/500<\psi<8959/10500}.                 \tag{1}
\]
Numerically these correspond to approximately
\(-20^\circ\) to \(-11.1^\circ\), or
\(35.6^\circ\) to \(48.9^\circ\).

The bounds are center-ray angular constraints,
**not** square-frame alignments or whole-quadrant
memberships.

## 1. A rational lower bound on the U-cap ray elevation

Put \(\alpha=\arcsin(h_U+1/2)\).
The far D singleton's whole-cap envelope implies
\(h_U>17/200\), so \(h_U+1/2>117/200\).
We prove
\[
\boxed{\alpha>31/50}.                             \tag{2}
\]
At \(z=31/50\), the alternating sine Taylor
upper bound gives
\[
\sin z\le z-z^3/6+z^5/120<117/200.
\]
The last strict rational difference is exactly
\[
117/200-[z-z^3/6+z^5/120]
=148420849/37500000000>0.
\]
Because \(z\in(0,\pi/2)\), monotonicity of sine
gives \(z<\arcsin(117/200)<\alpha\).

## 2. Exact mixed-center angular requirements

The refined five-square theorem
HUMAN_FIVE_SQUARE_FAN_REFINED.md proves the following
under the present disk ceiling, by an exact
cosine-law rectangle-bound computation:

* an inner center radius \(>117/200\) and an
  outer center radius \(\ge1\) have smaller
  angular gap **strictly greater than
  \(311/500\) radians**;
* the older independent mixed-radius theorem
  in HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md proves
  an angular gap **strictly greater than
  \(2\pi/9\)** when the inner center radius is
  \(>7/10\).

Write the four inner-center angular rays in their
forced order as \(R_-,R_+,U_+,U_-\).
The four-inner angular fan gives
\[
-\pi/3<\theta_{R_-}<-\alpha,\quad
0<\theta_{R_+}<\pi/3-\alpha,\quad
\pi/3<\theta_{U_+}<2\pi/3-\alpha.              \tag{3}
\]
All four actual square labels are distinct.

The R-minus center has x projection
\(>h_R+1/2>117/200\) and angle below \(-\alpha\).
Consequently its radius obeys
\[
|p_{R_-}|>\frac{117/200}{\cos\alpha}
>\frac{117}{\sqrt{26311}}>\frac7{10}.
\]
The last positive square margin is the integer
identity
\[
100\cdot117^2-49\cdot26311=79661>0.
\]
The R-plus and U-plus inner centers each have radial
norm \(>117/200\) from their **whole cap**
normal center projections. Thus the stronger
\(2\pi/9\) mixed angular gap applies to R-minus,
and the \(311/500\) mixed gap applies to
R-plus and U-plus.

## 3. The outer R ray must lie between R-minus and U-plus

Its right cap x projection exceeds \(117/200\),
and its norm is below \(283/200\), so
\[
\cos\psi>117/283>2/5>\cos(3\pi/8).
\]
Hence
\[
-3\pi/8<\psi<3\pi/8.                            \tag{4}
\]

The outer ray cannot lie **below** R-minus:
that would yield angular gap
\(<3\pi/8-\alpha<5\pi/24<2\pi/9\),
contrary to R-minus's mixed gap.
It cannot lie **above** U-plus either:
that would yield angular gap
\(<3\pi/8-\pi/3=\pi/24<311/500\).
Therefore the ray lies strictly between
R-minus and U-plus, and their mixed gaps imply
\[
-\pi/3+2\pi/9=-\pi/9<\psi,
\]
\[
\psi<\theta_{U_+}-311/500
<2\pi/3-\alpha-311/500.                          \tag{5}
\]

## 4. Exclude the broad middle angular region

The R-plus inner center lies strictly at
\(0<\theta_{R_+}<\pi/3-\alpha\) and
has mixed angular gap \(>311/500\) from
the outer R center. Hence exactly one of
the following holds:

* If \(\psi<\theta_{R_+}\), the mixed gap forces
  \[
  \psi<\theta_{R_+}-311/500
  <\pi/3-\alpha-311/500.
  \]
* If \(\psi>\theta_{R_+}\), it forces
  \[
  \psi>\theta_{R_+}+311/500>311/500,
  \]
  while the upper inequality (5) remains.

Now use (2), \(\alpha>31/50\), and
\(\pi<22/7\):
\[
\pi/3-\alpha-311/500
<22/21-31/50-311/500
=-2041/10500,
\]
\[
2\pi/3-\alpha-311/500
<44/21-31/50-311/500
=8959/10500.
\]
Together with (5), these are precisely
the two open angular lanes (1). QED.

## Consequences and limits

This is a **strictly narrower continuous center-angle
classification** for the sole R-outer label in S3/k3.
The residual allowed offset rectangle remains
\(17/200<h_R<13/100\),
\(17/200<h_U<1/5\); the L,D far-singleton
transverse bounds from the refined five-square
theorem and earlier S3 note remain in force.
No discrete S3/k3 macro-cell is wholly excluded by
these angle refinements alone.

The actual eight-square sharp lower bound
\(R_8\ge\widehat R\) and the full D0/D1/D2
global case queue remain OPEN. The S4/k=7
candidate equality configuration is unaffected.

[verify_s3_k3_sharper_rays.py](verify_s3_k3_sharper_rays.py)
audits the rational comparisons, not the
continuous angular argument or a Lean proof.
