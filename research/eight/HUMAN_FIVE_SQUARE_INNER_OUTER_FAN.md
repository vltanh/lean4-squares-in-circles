# A five-square angular fan obstruction at upper-cap offset 21/100

Research continuation, 2026-10-12. This is a **whole continuous-region
exclusion**, not a numerical sampling claim. It strengthens the
low-outer-count S3 branch and certain conditional S1/Type A subcases
without imposing any square-frame or contact-graph hypothesis.

## Theorem (four distinct inner centers and one right-cap outer center)

Suppose five **distinct** pairwise interior-disjoint unit squares
fit in a disk of squared radius
\[
R^2\le q_+=9789/2500.
\]
Two squares \(R_-,R_+\) lie **wholly** in the right cap
\(x\ge h_R\) and have center norms **strictly less than one**.
A third square \(R_o\), also wholly in that cap, has
center norm **at least one**. Suppose
\[
h_R>17/200.                                         \tag{1}
\]
Two further squares \(U_+,U_-\) lie **wholly** in the
perpendicular upper cap \(y\ge h_U\), have center norms
strictly less than one, and satisfy
\[
h_U\ge21/100.                                       \tag{2}
\]
Then **no such five-square configuration exists**.

In particular the five actual square labels must be
distinct: no right-cap square is also being counted as
one of the two upper-cap inner squares.
All square orientations are arbitrary.

## 1. Standard center-distance and radial bounds

Distinct disjoint unit squares contain disjoint
open disks of radius \(1/2\), so their centers
are distance at least one apart.
As in HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md, **any two**
centers with norms strictly less than one
must have smaller angular separation strictly
greater than \(\pi/3\).

For every square center \(p\), the true
farthest-vertex bound implies
\[
|p|^2+|p|+1/2\le q_+,
\qquad |p|<r_0:=283/200,                            \tag{3}
\]
the last inequality following from the exact
margin \(65/40000>0\) at \(r_0\).

### A quantitative mixed inner/outer angular lemma

If an inner center has radial norm
\(7/10<r<1\) and another center has radial
norm \(1\le s<283/200\), their angular gap
must be **strictly greater** than \(2\pi/9\).

Indeed suppose \(\delta\le2\pi/9\).
Since \(\pi<22/7\) and
\(\cos x\ge1-x^2/2\) for \(x\ge0\),
\[
\cos\delta>
1-\frac12(44/63)^2
=\frac{3001}{3969}.                               \tag{4}
\]
The cosine law then gives
\[
|p-q|^2
<r^2+s^2-\frac{6002}{3969}rs.
\]
This quadratic is convex separately in r and s,
so the maximum on
\([7/10,1]\times[1,283/200]\)
occurs at a corner. The four **exact**
corner values, in the order
\((7/10,1),(7/10,283/200),(1,1),(1,283/200)\),
are
\[
24463/56700,\quad
22552343/22680000,\quad
1936/3969,\quad
136920041/158760000.
\]
Every value is strictly below one; the largest
is \(22552343/22680000=1-127657/22680000\).
This contradicts center distance \(\ge1\).

Similarly, if the inner center has radial norm
\(117/200<r<1\), then its angular gap to any
outer center is **strictly greater** than \(7\pi/36\).
If \(\delta\le7\pi/36\), then
\[
7\pi/36<11/18,\quad
\cos\delta>1-\frac12(11/18)^2
=527/648>13/16,                                    \tag{5}
\]
the last exact margin being \(1/1296>0\).
The four corner values of
\[
r^2+s^2-\frac{13}{8}rs
\]
on
\([117/200,1]\times[1,283/200]\)
are
\[
979/2500,\quad319781/320000,\quad
3/8,\quad14057/20000.
\]
Each is strictly below one; their greatest
is \(319781/320000=1-219/320000\).
Hence separation by at least one forces
\(\delta>7\pi/36\). Neither mixed lemma
uses a square-frame assumption.

## 2. Four inner center rays have a compulsory fan

Let
\[
\alpha=\arcsin(h_U+1/2)
\ge\arcsin(71/100)>\pi/4,                           \tag{6}
\]
where \((71/100)^2>1/2\).
The two R inner-center rays lie in
\((-\pi/3,\pi/3)\), on opposite sides of the x
axis. Likewise the two U inner-center rays
lie in \((\alpha,\pi-\alpha)\), on opposite
sides of the y axis, because an inner
pair in a nonnegative whole cap must have
opposite transverse signs.

Denote the four signed ray angles by
\[
\theta_{R_-}<0<\theta_{R_+},\qquad
\theta_{U_+}<\pi/2<\theta_{U_-}.
\]
The \(>\pi/3\) angular gaps among the four
distinct inner centers, as derived in
HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md, give
\[
-\pi/3<\theta_{R_-}<-\alpha<-\pi/4,                  \tag{7}
\]
\[
0<\theta_{R_+}<\pi/3-\alpha<\pi/12,                 \tag{8}
\]
\[
\pi/3<\theta_{U_+}<2\pi/3-\alpha<5\pi/12.          \tag{9}
\]
For completeness: \(U_+\) is more than \(\pi/3\)
below \(U_-\); distinct \(R_+,U_+\) cannot occur
in the reverse order and are more than \(\pi/3\)
apart; then \(R_-\) is more than \(\pi/3\)
below \(R_+\). This yields (7)–(9).

The inner R_- center has x projection
\(p_x\ge h_R+1/2>1/2\), so (7) gives
\[
|p_{R_-}|>\frac{1/2}{\cos\alpha}>
\frac1{\sqrt2}>\frac7{10}.                        \tag{10}
\]
The U_+ center has
\[
|p_{U_+}|\ge p_{U_+}.y\ge h_U+1/2\ge71/100>7/10.
                                                               \tag{11}
\]
The R_+ center obeys
\[
|p_{R_+}|\ge p_{R_+}.x\ge h_R+1/2>117/200.         \tag{12}
\]

## 3. There is no angular room for the outer right-cap square

Write \(\psi\) for the polar angle of the outer
right-cap center \(p_{R_o}\).
Its x projection and (1),(3) imply
\[
\cos\psi>\frac{117/200}{283/200}
=\frac{117}{283}>\frac25.
\]
Since
\[
\cos(3\pi/8)=\frac{\sqrt{2-\sqrt2}}2<\frac25
\]
(the last comparison follows from
\(\sqrt2>34/25\)), we have
\[
-3\pi/8<\psi<3\pi/8.                             \tag{13}
\]

The first mixed inner/outer angular lemma,
(10)–(11), now says that \(\psi\) differs
by **more than** \(2\pi/9\) from **each**
of \(\theta_{R_-}\) and \(\theta_{U_+}\).

The outer ray **cannot lie below** \(R_-\):
otherwise, by (7),(13), the gap would be
less than \(3\pi/8-\pi/4=\pi/8<2\pi/9\).
It therefore lies above R_-, with
\[
\psi>\theta_{R_-}+2\pi/9
>-\pi/3+2\pi/9=-\pi/9.                            \tag{14}
\]

Likewise the outer ray **cannot lie above**
\(U_+\): by (9),(13), that gap would be
less than \(3\pi/8-\pi/3=\pi/24<2\pi/9\).
It therefore lies below U_+, with
\[
\psi<\theta_{U_+}-2\pi/9
<5\pi/12-2\pi/9=7\pi/36.                         \tag{15}
\]

Finally (8), (14), and (15) imply
\[
|\psi-\theta_{R_+}|<7\pi/36.                     \tag{16}
\]
Indeed if \(\psi\ge\theta_{R_+}>0\),
use (15); if \(\psi<\theta_{R_+}<\pi/12\),
use (14) and
\(\pi/12+\pi/9=7\pi/36\).

But the second mixed inner/outer angular
lemma together with (12) says
\[
|\psi-\theta_{R_+}|>7\pi/36,
\]
a contradiction. There cannot be five squares
satisfying the theorem's hypotheses. QED.

## Case-pruning consequences and equality guard

**S3/k=3:** For exclusive whole-side populations
R=3,L=1,U=2,D=1, the far L singleton is outer,
and the R triple contributes at least one
distinct outer. A cap U with offset
\(h_U\ge1/2\) would add two outer and force
\(k\ge4\). Thus the far D singleton is
also outer and, with exactly k=3, the R triple
contains one outer and two inner labels,
while both U labels are inner. By the far L
singleton's one-square cap envelope,
\[
h_R>17/200.
\]
The five-square theorem now proves
\[
\boxed{\text{S3/k=3 requires }h_U<21/100.}
\]
This is a **complete continuous-region elimination**
of all S3/k=3 configurations with \(h_U\ge21/100\),
stronger than the earlier \(h_U<(\sqrt{26311}-100)/200\).

**S1/k=3:** If its U=3,D=1 axis has
\(h_U\ge21/100\) and its perpendicular
R=3,L=0 triple has offset \(h_R>17/200\),
the five-square theorem also applies,
because each triple has exactly two inner
and one outer center. Thus the surviving
S1/k=3 subcase with such a large U offset
requires
\[
\boxed{h_R\le17/200.}
\]
This is a *necessary* position restriction,
not a complete S1 elimination.

The same five-square obstruction may be used
in saturated D1 Type A **only after verifying
all five selected labels are distinct**;
a shared RU member cannot be silently counted twice.

No S4 equality packing is rejected:
the real candidate has S4/k=7 and does
not meet the theorem's four-inner-plus-one-outer
hypotheses. The unrestricted sharp radius
\(R_8\ge\widehat R\) remains OPEN.
