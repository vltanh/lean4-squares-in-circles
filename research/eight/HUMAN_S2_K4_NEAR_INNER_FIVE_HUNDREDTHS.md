# The S2 near-inner triple offset is less than 1/20

Research continuation, 2026-10-12. This is a further, strictly stronger
**arbitrary-frame continuous-region exclusion** within exclusive
S2=(3+0,2+2). It refines
[HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md](HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md),
which established the earlier necessary offset \(h_R<1/10\).

## Theorem

Let eight pairwise interior-disjoint unit squares of independent
orientations fit in a disk of squared radius
\(R^2\le9789/2500\). Let C denote their unique open
origin-containing square, and suppose the seven exterior squares
have **exclusive single-side statuses**, normalized as
\[
R:3,\quad L:0,\quad U:2,\quad D:2,
\]
where U is the *nearer* two-member cap of the 2+2 axis.
Suppose **both** U-square centers have norm strictly below one.

Then the three-member R whole-cap offset satisfies
\[
\boxed{0<h_R<1/20.}                                \tag{1}
\]
The same hypotheses already force exactly two outer R centers,
one inner R center, two inner U centers and two outer D centers:
in particular \(k=4\), by the prior
[HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md](HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md)
and six-square forbidden-cap theorem.

No actual contacts, selected pair separators, or square-frame
alignment are assumed.

## 1. A new far-cap elevation of more than 60 degrees

First isolate an arbitrary-frame lemma, valid independently
of the S2 status details.

**Lemma.** A whole unit square in a disk of squared radius
\(\le9789/2500\), lying beyond a half-plane
\(y\le-h\) with \(h\ge5/8\), has a center \(p=(x,y)\)
with
\[
\boxed{|x|<(-y)/\sqrt3.}                          \tag{2}
\]
Consequently its polar center ray has elevation strictly
greater than \(\pi/3\) from either horizontal half-axis.

**Proof.** The whole-cap center projection gives
\(-y\ge h+1/2\ge9/8\). The arbitrary-frame
one-square cap-envelope theorem
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md)
applies because \(h>2/5\), and gives
\[
(1+h)^2+(|x|+1/2)^2\le R^2\le9789/2500.         \tag{3}
\]
If \(|x|\ge(-y)/\sqrt3\), then, since
\(\sqrt3<7/4\),
\[
|x|+1/2 \ge (9/8)/\sqrt3+1/2
>(9/8)(4/7)+1/2=8/7.
\]
Also \(1+h\ge13/8\), so (3) would imply
\[
9789/2500>(13/8)^2+(8/7)^2
=9789/2500+61049/1960000,
\]
a contradiction. Hence (2). QED.

In our S2 hypotheses, two **inner** U centers require
\(h_U<(\sqrt3-1)/2<3/8\), by the sharp
two-inner-cap theorem. Therefore the far D cap offset
\(h_D=1-h_U>5/8\), and both D centers satisfy (2).
Write their actual ray angles, ordered from lower
(leftward) to upper (rightward), as \(\phi_1<\phi_2\)
in the interval \((-\pi,0)\). They obey
\[
-2\pi/3<\phi_1<\phi_2<-\pi/3.                   \tag{4}
\]
Both are outer centers, because their whole-cap offset
exceeds \(1/2\).

## 2. Four outer rays have shorter adjacent gaps

The rigorous independent outer-pair angular theorem
[HUMAN_STABLE_OUTER_ANGLE.md](HUMAN_STABLE_OUTER_ANGLE.md)
says any two distinct outer-center rays in this disk
have smaller angular separation strictly greater than
\[
\delta_0:=\pi/4-1/500.                          \tag{5}
\]

Let the two outer R center-ray angles be
\(\psi_1<\psi_2\). The previous
HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md argument
establishes all outer R rays are **strictly above**
the upper D ray \(\phi_2\), and
\[
\psi_2<7\pi/36.                                 \tag{6}
\]
In particular their chronological order on the
ordinary nonwrapping negative-to-positive arc is
\[
\phi_1<\phi_2<\psi_1<\psi_2.
\]
Successive D/D, D/R and R/R center rays have
gaps \(>\delta_0\). Thus (4) gives
\[
\phi_2>\phi_1+\delta_0>-2\pi/3+\delta_0,
\]
\[
\psi_1>\phi_2+\delta_0
>-2\pi/3+2\delta_0
=-\pi/6-1/250.                                  \tag{7}
\]

Consequently **both** intervals in which the
remaining inner R center might lie between
consecutive outer rays satisfy
\[
\psi_1-\phi_2<M,\qquad
\psi_2-\psi_1<M,                                \tag{8}
\]
where
\[
M=13\pi/36+1/250.
\]
Indeed, for the first interval combine
\(\psi_1<\psi_2-\delta_0<7\pi/36-\delta_0\)
and \(\phi_2>-2\pi/3+\delta_0\).
For the second combine (6),(7).
The standard strict rational bound \(\pi<22/7\)
gives
\[
M<13(22/7)/36+1/250
=8969/7875
<57/50=2(57/100),                               \tag{9}
\]
the latter exact rational difference being
\(17/15750>0\).

There is also a strictly **positive** lower
angle bound for the upper R outer ray:
by (7) and \(\psi_2>\psi_1+\delta_0\),
\[
\boxed{\psi_2>\pi/12-3/500.}                    \tag{10}
\]

## 3. Mixed inner/outer centers need an angular gap >57/100 radians

We prove a standalone distance consequence.

**Lemma.** In the present disk ceiling, if one packed
square center has norm \(r\in[11/20,1)\) and another
has norm \(s\in[1,283/200)\), then their smaller
polar angular separation is **strictly greater**
than \(57/100\) radians.

**Proof.** For \(x=57/100\), the alternating
Taylor inequalities give
\[
\cos x\ge 1-x^2/2+x^4/24-x^6/720
>21/25,
\]
where the exact final rational margin equals
\[
152055983639/80000000000000>0.
\]
If the angular separation were at most \(x\),
the cosine law would imply
\[
|p-q|^2<r^2+s^2-\frac{42}{25}rs.
\]
The last quadratic is convex separately in
\(r,s\); hence its maximum over the closed
rectangle \([11/20,1]\times[1,283/200]\)
is at a corner. The four exact values are
\[
757/2000,\quad 199453/200000,\quad
8/25,\quad25001/40000,
\]
all **strictly below one**. Distinct unit squares
contain inscribed open disks of radius \(1/2\),
so their center distance is at least one,
a contradiction. QED.

The angular lemma requires only genuine center norms,
not any whole-side cap assignment.

## 4. The remaining inner R center has nowhere to go

Suppose contrary to (1) that \(h_R\ge1/20\).
By the previous S2/k4 near-inner classification,
there is exactly one **inner** R-square center Q.
Its R whole-cap membership forces
\[
p_Q.x\ge h_R+1/2\ge11/20,
\]
so its norm belongs to \([11/20,1)\).
Its polar ray angle \(\theta\) satisfies
\[
-\arccos(11/20)<\theta<\arccos(11/20).
\]
Since \(\arccos(11/20)<\pi/3\) and (4) gives
\(\phi_2<-\pi/3\), necessarily
\[
\theta>\phi_2.                                    \tag{11}
\]

Apply the mixed-center lemma to Q and the
three distinct outer squares at angles
\(\phi_2,\psi_1,\psi_2\).
Because all relevant ordinary differences
are less than \(\pi\), each must exceed
\(57/100\) in absolute value.

* If \(\phi_2<\theta<\psi_1\), their span
  would exceed \(2(57/100)\), contradicting
  (8)–(9).
* If \(\psi_1<\theta<\psi_2\), the same contradiction
  holds for the second span.
* If \(\theta>\psi_2\), then (10) and the
  mixed-center lemma give
  \[
  \theta>\pi/12-3/500+57/100>\pi/4.              \tag{12}
  \]
  The last comparison follows from
  \(57/100> \pi/6+3/500\), using
  \(\pi<22/7\).
  But \(\theta<\pi/2\).

  The **positive-x inner U center** \(U_+\)
  exists by the two-inner U cap theorem and has
  polar angle \(\vartheta\) in
  \((\pi/4,5\pi/12)\), as proved by the
  U-inner angular fan used in
  HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md.
  Thus both \(\theta,\vartheta\) lie in
  \((\pi/4,\pi/2)\), an interval of width
  \(\pi/4<\pi/3\).
  But these are distinct **inner-center** square
  labels at mutual center distance at least one,
  so their angular gap must exceed \(\pi/3\).
  Contradiction.

There are no remaining positions relative
to the ordered outer rays in (11), and equality
with an outer ray is likewise excluded by the
positive mixed angular bound. Therefore
\(h_R<1/20\), proving the theorem. QED.

## Correct remaining status

For the exclusive S2 branch whose nearer 2+2
U cap has **two inner-center squares**:
\[
\boxed{k=4,\quad0<h_R<1/20,}
\]
with the opposite-sign outer R ray lanes
from HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md.
This **strictly** strengthens the previous
\(h_R<1/10\) restriction and removes
the whole continuous interval \([1/20,1/10)\).

The near-U branch with one or two **outer** U centers,
other D0 cases, D1/D2, and the actual S4/k=7
equality construction remain untouched.
No unrestricted \(R_8\ge\widehat R\) claim is made.

## Audit

[verify_s2_k4_five_hundredths_margins.py](verify_s2_k4_five_hundredths_margins.py)
contains a short exact-fraction check of the two tight
rational margins (9) and the mixed-center cosine bound.
It does not prove any continuous case in place of this
written geometric argument, and there is no Lean handoff.
