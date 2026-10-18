# Strengthened five-square R-only obstruction: perpendicular offset >=1/16 is impossible

2026-10-12 research continuation. This is a **strict improvement** of
[HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md](HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md):
its earlier perpendicular offset requirement \(h_U>17/200\) is
replaced by the weaker \(h_U\ge1/16\). The right triple still needs
\(h_R>17/200\). The proof is **analytic for every square frame and
every position**, not a computer-generated interval cover.

## Theorem: exact five distinct unit-square obstruction

Let five distinct unit squares with disjoint open interiors lie
inside a disk of squared radius
\[
R^2\le9789/2500.
\]
Assume the following actual *whole-square* cap data:

* Three squares \(A_-,A_+,A_o\) lie beyond \(x=h_R\)
  for \(h_R>17/200\). Their center classes are
  **inner, inner, outer** respectively
  (\(|p_{A_\pm}|<1,\ |p_{A_o}|\ge1\)).
* Two **additional** distinct squares \(B_+,B_-\)
  lie beyond \(y=h_U\) with **both** center norms
  \(<1\), for
  \[
  \boxed{h_U\ge1/16}.
  \]
* The outer R square has **no whole upper cap membership**:
  \[
  A_o\not\subseteq\{y\ge h_U\}.                \tag{R-only}
  \]

Then the five distinct square labels **cannot coexist**.

There is no parallel-frame, actual contact, stress,
or other packed-square hypothesis.

## 1. Reduce to 1/16 <= h_U < 1/5

If \(h_U\ge1/5\), the already proved full-frame
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
directly excludes the five-square pattern, without even
using R-only. We may henceforth assume
\[
1/16\le h_U<1/5.
\]
Let
\[
\alpha=\arcsin(h_U+1/2)\ge\arcsin(9/16).
\]
A strict alternating-sine Taylor upper comparison proves
\[
\sin(297/500)
\le297/500-(297/500)^3/6+(297/500)^5/120
<9/16,
\]
with exact positive margin
\[
\frac9{16}
-\left[\frac{297}{500}-\frac{(297/500)^3}{6}
+\frac{(297/500)^5}{120}\right]
=\frac{3518153059581}{1250000000000000}>0.
\]
Thus
\[
\boxed{\alpha>297/500}.                        \tag{1}
\]

The standard inscribed half-unit center disks force
mutual center distance at least one, and hence
**every two inner-center rays have smaller angular
gap strictly greater than \(\pi/3\)**.
The two R-inner centers therefore have opposite
signed y, and the two U-inner centers have opposite
signed x, by
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md).
Write their polar angles as
\(\theta_{R-}<0<\theta_{R+}\) and
\(\theta_{U+}<\pi/2<\theta_{U-}\).
The distinct inner-center gap condition forces
the **ordered four-ray fan**:
\[
-\pi/3<\theta_{R-}<-\alpha,\qquad
0<\theta_{R+}<\pi/3-\alpha,
\]
\[
\pi/3<\theta_{U+}<2\pi/3-\alpha,\qquad
\theta_{U-}>\theta_{U+}+\pi/3.
\]
In particular \(R+\) and \(U+\) are different actual labels.

## 2. Three exact mixed inner/outer angular gaps

The true farthest-vertex square formula yields the
universal center radius
\[
|p|<r_0:=283/200
\quad\text{when}\quad R^2\le9789/2500.
\]
The *existing* center-angle lemmas proved in
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
and its predecessors say:

* For inner radius \(r>7/10\) and outer radius
  \(1\le s<r_0\), their angular gap is **\(>2\pi/9\)**.
* For inner radius \(r>117/200\) and
  outer radius \(1\le s<r_0\), their angular gap
  is **\(>311/500\)** radians.

We prove one **new** exact lower-radius endpoint, needed
because \(h_U\) is now allowed below \(17/200\).

**Mixed gap lemma.** For inner radius
\(r>9/16\) and outer radius \(1\le s<r_0\),
two distinct packed square centers must have
angular gap **\(>59/100\) radians**.

Indeed, the alternating cosine Taylor bound gives
\[
\cos(59/100)\ge
1-(59/100)^2/2+(59/100)^4/24-(59/100)^6/720
>83/100.
\]
The strict rational margin is
\[
677027766359/720000000000000>0.
\]
If the gap were at most \(59/100\), the cosine law
would imply
\[
|p-q|^2<r^2+s^2-(83/50)rs.
\]
The latter separately convex quadratic over
\([9/16,1]\times[1,283/200]\) has four exact
corner values
\[
2449/6400,\quad7979/8000,\quad
17/50,\quad26133/40000,
\]
all strictly below one. This contradicts the
disjoint inscribed half-unit disks of the two
squares. QED for the new mixed lemma.

These lemmas apply to our four inner labels:
\[
r_{R-}>\frac{117/200}{\cos\alpha}>7/10.
\]
The last comparison follows from
\(\cos\alpha\le\sqrt{1-(9/16)^2}
=\sqrt{175}/16\), since
\[
(117/140)^2-175/256
=\frac{4649}{313600}>0.
\]
Also \(r_{R+}>117/200\), and
\(r_{U+}>9/16\) from its positive x and
whole upper cap y projection.

Thus the **outer R** center has gap \(>2\pi/9\)
from R-, \(>311/500\) from R+, and
\(>59/100\) from U+.

## 3. The outer R ray has only a negative or a positive interval

Write \(\psi\) for the polar angle of the
outer R square \(A_o\). Its cap center
projection \(p_x>117/200\) and radius
\(<283/200\) give
\[
-3\pi/8<\psi<3\pi/8;
\]
the strict comparison follows from
\(117/283>2/5>\cos(3\pi/8)\).

The outer ray cannot lie below R-:
there the gap would be
\(<3\pi/8-\alpha
<3\pi/8-297/500<2\pi/9\).
It cannot lie above U+ either:
there the gap is
\(<3\pi/8-\pi/3=\pi/24<59/100\).
Therefore it lies **between** the R- and
U+ rays.

The mixed angular gap from R+ is \(>311/500\).
Consequently either
\[
\psi<\theta_{R+}-311/500
<\pi/3-\alpha-311/500
<-\frac{442}{2625},                              \tag{2-}
\]
or
\[
\psi>\theta_{R+}+311/500>311/500.                \tag{2+}
\]
For (2-), use (1) and \(\pi<22/7\):
\[
\pi/3-297/500-311/500
<22/21-608/500=-442/2625.
\]

The U+ mixed angular gap gives an *upper*
bound for **both** alternatives:
\[
\psi<\theta_{U+}-59/100
<2\pi/3-\alpha-59/100
<\frac{2392}{2625}<\frac{\pi}{3}.
                                                               \tag{3}
\]
The last inequality uses \(\pi<22/7\),
\(\pi>157/50\) and (1), with strict
rational comparisons.

## 4. The negative alternative is impossible

Suppose the outer angle satisfies (2-):
\(\psi<-442/2625\).

The mandatory mixed gap \(>2\pi/9\)
from the inner R- center, with R- below
the outer ray, forces
\[
\theta_{R-}<\psi-2\pi/9
<-\frac{6821}{7875}<-\frac{433}{500}.            \tag{4}
\]
Here \(\pi>157/50\); the final positive
rational margin is \(1/6300\).

Since the R- center has x projection
strictly greater than \(117/200\),
the exact Taylor upper inequality
\[
\cos(433/500)
\le1-(433/500)^2/2+(433/500)^4/24
<13/20,
\]
with strict rational margin
\(2314874879/1500000000000>0\),
forces its *inner radius* \(r>9/10\).

**Sharper mixed radius lemma at \(r>9/10\).**
The polar gap from any distinct outer center
of radius \(s<283/200\) is **greater than
\(779/1000\)** radians. Indeed
\[
\cos(779/1000)>
1779/2500
\]
by the alternating cosine Taylor lower
bound; the exact positive margin is
\[
9447139570318679/720000000000000000000>0.
\]
If the gap were smaller, the center distance
squared would be less than
\(r^2+s^2-(1779/1250)rs\).
Its separately convex radial endpoint
max over \([9/10,1]\times[1,283/200]\)
is **\(4998899/5000000<1\)**.
This contradicts the required unit center separation.

Applying this stronger gap to R- and the
outer R center gives
\[
\theta_{R-}<\psi-779/1000
<-\frac{3979}{4200}.                              \tag{5}
\]
But another exact cosine Taylor upper comparison
gives
\[
\cos(3979/4200)
\le1-(3979/4200)^2/2+(3979/4200)^4/24
<117/200
\]
with positive margin
\(1495706861519/7468070400000000>0\).
Since R- has *inner radius* \(r<1\),
its x projection obeys
\[
p_{R-}.x=r\cos|\theta_{R-}|
<117/200,
\]
contrary to its actual whole-R cap projection
\(p_{R-}.x>h_R+1/2>117/200\).
Thus the **entire negative outer-ray
alternative (2-) is impossible**.

## 5. The positive alternative also forces two centers to overlap

We are left with (2+) and (3):
\[
311/500<\psi<2392/2625<\pi/3.
\]
Because the outer R radius is \(\ge1\)
and \(\psi>\pi/6\), its center has
\[
q_x>1/2,\qquad q_y>1/2.
\]
The strict cosine Taylor bound at the
lower angle \(311/500\) gives
\[
q_x<(283/200)(813/1000)
=230079/200000.
\]

The two **inner** R-square centers
have opposite signed y, both x
projections \(>117/200\), and radii
\(<1\). As in the completely explicit
proof of
[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md),
the inner R+ center satisfies
\[
117/200<p_x<1,\qquad
49/500<p_y<1.                                   \tag{6}
\]
The transverse \(49/500\) reserve
follows only from these two distinct
inner R centers and their required
mutual center distance \(\ge1\);
no S3-only singleton is used.

Crucially, the outer R square is **R-only**:
its lowest actual vertex is below \(h_U\),
because the *whole unit* is not contained
in \(y\ge h_U\).
Every square's vertical half-width is at
most \(\sqrt2/2<177/250\). Since we are
in case \(h_U<1/5\), this implies
\[
q_y<h_U+\sqrt2/2<227/250.
\]

Comparing its center with the **different**
inner R+ center in (6) gives
\[
|q_x-p_x|<113079/200000,\qquad
|q_y-p_y|<81/100,
\]
and hence the exact contradiction
\[
|q-p|^2<
(113079/200000)^2+(81/100)^2
=1-\frac{969139759}{40000000000}<1.
\]
The distinct unit squares require
center distance at least one.
This excludes the positive alternative
and completes the **new five-square theorem**.

## New strictly stronger exclusive S1/k3 conclusion

In exclusive S1=(3+0,3+1), k=3,
normalize the triple with its opposite far
singleton along R/L and its perpendicular
3+0 triple along U/D. The far L singleton
is outer, and each triple contributes one
**distinct outer** center. With total
k=3, both triples have two inner and
one outer labels. The 3+1 R offset obeys
\(h_{31}>17/200\) from the sharp far-singleton
envelope.

Select R's three actual labels and the
**two inner** labels of U's triple.
All five are distinct in this exclusive
one-side status branch, and the R outer
square is genuinely **R-only**.
Therefore the present theorem excludes
every \(h_{30}=h_U\ge1/16\).

Thus the surviving entire S1/k3
**3+0 triple cap** must satisfy
\[
\boxed{0<h_{30}<1/16.}                           \tag{7}
\]
This **strictly improves** the previous
\(h_{30}\le17/200\) and extends the
earlier conditional \(h_{30}<1/16\)
bound (which had required \(h_{31}\le1/10\))
to **every** allowed 3+1 triple offset.

It does **not** eliminate S1/k3 completely.
It does not apply where the five selected
labels overlap via a double-side status or
where the outer R square actually has a
whole U separator. The exact S4/k7 equality
packing is unaffected; the unrestricted
sharp lower bound \(R_8\ge\widehat R\)
and Lean handoff remain OPEN.

[verify_five_square_ru_one_sixteenth.py](verify_five_square_ru_one_sixteenth.py)
audits the newly displayed rational
angular and cosine-law endpoint margins.
