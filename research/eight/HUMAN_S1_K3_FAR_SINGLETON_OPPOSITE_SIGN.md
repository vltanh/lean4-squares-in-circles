# S1/k=3: the far opposite singleton must be transversely opposite the 3+0 triple

2026-10-12 research continuation. This is a **new full-frame,
continuous sign-subcase exclusion** within the still-open
exclusive S1=(3+0,3+1), k=3 class.
It does not claim S1/k3 is globally impossible.

## Theorem (exact signed far-singleton polarization)

Suppose eight pairwise interior-disjoint unit squares of
arbitrary orientations fit inside a disk centered at the origin
with \(R^2\le9789/2500\), with C the unique square
whose open interior contains the origin.

Suppose all seven noncentral squares have **exactly one
central-owned whole-square side status** of type
S1=(3+0,3+1), and exactly \(k=3\) exterior centers
have norm \(\ge1\).

Rotate/reflect so the 3+1 axis is R/L:
\[
R:3,\quad L:1,\quad U:3,\quad D:0.
\]
Write \(h_R=h_{31}\) and \(h_U=h_{30}\)
for the R and U outward offsets, and let
\(p_L=(x_L,y_L)\) be the center of the
**one whole far-L singleton**.

Then its true center obeys the strict signed restriction
\[
\boxed{y_L<0.}                                      \tag{1}
\]
That is, it lies on the **opposite transverse
side of the horizontal origin diameter** from
the perpendicular U triple's outward normal.

This is a restriction on the *center*, not a claim
that the whole singleton is in an origin quadrant.

The other currently known necessary S1/k3 bounds remain:
\[
h_R>17/200,\quad h_R<13/100,\quad
0<h_U<1/16.
\]
The proof below in fact uses only \(h_U<13/100\),
and does not require the sharper last inequality.

## 1. Center labels and four-inner ray ordering

The far L singleton has outward cap offset
\(h_L=1-h_R>1/2\) and thus an **outer** center.
Both R and U triple caps have at least one
outer center by the orientation-free three-inner
cap exclusion, and because the seven side statuses
are exclusive, these are different actual labels.
With \(k=3\), each triple has exactly
**two inner centers** and **one outer center**.
The R outer is genuinely **R-only**.

The perpendicular four distinct inner-center
rays can be written in strict increasing polar order
\[
-\pi/3<\theta_{R-}<0<\theta_{R+}
<\theta_{U+}<\pi/2<\theta_{U-}<5\pi/6.
\]
Any two distinct inner centers of norm <1
with mutual distance \(\ge1\) have angular gap
**strictly greater than \(\pi/3\)**.
In particular
\[
\theta_{U-}-\theta_{U+}>\pi/3,\quad
\theta_{U+}-\theta_{R+}>\pi/3,\quad
\theta_{R+}-\theta_{R-}>\pi/3.                  \tag{2}
\]
The opposite transverse center signs within
each same-cap inner pair follow from
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md).

The 3+1 far singleton's cap bound forces
\(h_R>17/200\), so each R-inner center has
x projection \(>117/200\). In particular
its positive-y member \(R+\) has radius
\(>117/200\), and any *outer* R member has
x projection \(>117/200\).
Every center radius in the q_+ disk is
\(<283/200\).

## 2. Assume the far L center is on or above the horizontal diameter

Suppose contrary to (1) that \(y_L\ge0\).
Since the L singleton lies wholly beyond
the left central side, its center has
\(x_L<0\). Its polar ray \(\phi_L\) then
belongs to the upper-left quadrant:
\[
\pi/2<\phi_L\le\pi.
\]
The square L is a **distinct outer-center**
unit square.

We first prove that the northwest U-inner
center ray must obey
\[
\boxed{\theta_{U-}<7\pi/9.}                        \tag{3}
\]
If \(\theta_{U-}\ge7\pi/9\), then since
its positive y normal center projection
exceeds \(h_U+1/2>1/2\), its inner radial
norm r satisfies
\[
r>\frac{1/2}{\sin\theta_{U-}}
\ge\frac{1/2}{\sin(2\pi/9)}
>7/10.
\]
Here \(\sin(2\pi/9)<2\pi/9<5/7\)
follows from \(\pi<22/7\).

The already hand-proved mixed inner/outer
angular theorem in
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
states that an inner center of radius \(>7/10\)
and an outer center of radius \(<283/200\)
must have angular gap **\(>2\pi/9\)**.
But \(L\)'s polar angle is at most \(\pi\);
therefore the angular gap between
\(U-\) and L would satisfy
\[
0<\phi_L-\theta_{U-}
\le\pi-7\pi/9=2\pi/9,
\]
contradiction. Hence (3).

By the three strict inner-ray gaps (2), it follows that
\[
\boxed{
\theta_{U+}<4\pi/9,\quad
\theta_{R+}<\pi/9,\quad
\theta_{R-}<-2\pi/9.
}                                                      \tag{4}
\]
These stronger ray bounds use the actual
**far singleton's signed center location**,
not an assumed common frame.

The lower R-inner center then has radial norm
**strictly greater than \(7/10\)**.
Indeed \(p_{R-}.x>117/200\) and
\(|\theta_{R-}|>2\pi/9\), so
\[
r_{R-}>\frac{117/200}{\cos(2\pi/9)}
>\frac{117/200}{4/5}>7/10.
\]
The exact trigonometric comparison
\(\cos(2\pi/9)<4/5\) follows from
\(\pi>157/50\) and the Taylor upper estimate
at \(157/225\):
\[
1-(157/225)^2/2+(157/225)^4/24
<4/5,
\]
with exact positive margin
\[
2064819299/61509375000>0.
\]

## 3. Neither angular placement of the outer R square is possible

Let \(\psi\) be the center ray of the
**outer R** member. Its actual whole
right-cap x projection \(>117/200\)
and radius \(<283/200\) give
\[
-3\pi/8<\psi<3\pi/8.
\]

Two already proven mixed center-angle gaps apply:
* \(>2\pi/9\) from the lower R inner center
  (its radius is \(>7/10\));
* \(>311/500\) from the upper R inner center
  (its radius is \(>117/200\)).

The U+ inner center has radius \(>1/2\)
and is a distinct label. The exact
universal mixed center-angle lemma
in [HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
requires its gap from the outer R center to be
**\(>12/25\) radians**.

The outer R ray cannot be **below** R-:
by (4), that gap would be
\[
<3\pi/8-2\pi/9=11\pi/72<2\pi/9.
\]
It cannot be **above** U+ either:
the gap would be
\[
<3\pi/8-\pi/3=\pi/24<12/25.
\]
Therefore its angle is strictly between R-
and U+.

Using the R+ mixed gap, there are two
alternatives:

**Negative alternative.** If \(\psi<\theta_{R+}\),
then
\[
\psi<\theta_{R+}-311/500
<\pi/9-311/500.
\]
The R- mixed gap gives
\[
\theta_{R-}<\psi-2\pi/9
<-\pi/9-311/500<-24/25,
\]
because \(\pi>157/50\) implies
\[
\pi/9+311/500-24/25>49/4500>0.
\]
But \(\cos(24/25)<117/200\) by the
exact cosine Taylor bound in
[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md).
Since R- is inner (\(r<1\)), its x
projection would be
\[
p_{R-}.x=r\cos|\theta_{R-}|<117/200,
\]
contradicting its whole R-side projection
\(p_{R-}.x>117/200\). This alternative
is impossible.

**Positive alternative.** Thus the outer R
ray satisfies
\[
\psi>\theta_{R+}+311/500>311/500.
\]
Its U+ mixed gap and (4) give
\[
\psi<\theta_{U+}-12/25
<4\pi/9-12/25<\pi/3.
\]
The last strict inequality reduces to
\(\pi/9<12/25\), which follows from
\(\pi<22/7\) with rational margin
\(206/1575>0\).

We have therefore forced the **same
strict positive R-outer ray lane**
\[
\boxed{311/500<\psi<\pi/3.}                    \tag{5}
\]

## 4. R-only gives a concrete center-distance contradiction

The whole three-square R cap has exactly
two inner centers \(R-,R+\), with
\(p_x>117/200\). Their mutual distance
\(\ge1\), both norms \(<1\), and their
opposite y signs yield the exact
positive-y reserve from
[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md):
\[
117/200<p_{R+}.x<1,\qquad
49/500<p_{R+}.y<1.
\]

The outer R center q has
\(\psi\in(311/500,\pi/3)\)
and radius \(1\le|q|<283/200\).
Thus \(q_x,q_y>1/2\).
The exact cosine bound at \(311/500\)
gives
\[
q_x<(283/200)(813/1000)
=230079/200000.
\]

Because the R outer square is
**single-side R-only**, it is **not**
wholly beyond the U cap line \(y=h_U\).
Its actual vertical half-width is at
most \(\sqrt2/2<177/250\), so
\[
q_y<h_U+\sqrt2/2.
\]
The U triple has exactly one outer center,
so the proved three-square cap
two-outer theorem forces \(h_U<13/100<1/5\).
Therefore
\[
q_y<227/250.
\]

The two different centers q and \(p_{R+}\)
must satisfy
\[
|q_x-p_{R+}.x|<113079/200000,\qquad
|q_y-p_{R+}.y|<81/100.
\]
Their squared center distance is hence
strictly less than
\[
(113079/200000)^2+(81/100)^2
=1-\frac{969139759}{40000000000}<1,
\]
contradicting the two unit squares'
disjoint inscribed half-unit disks.

We have proved that \(y_L\ge0\) is
impossible. Therefore the far L
singleton's actual center satisfies
\(\boxed{y_L<0}\), as claimed. QED.

## Remaining S1/k3 case and guards

The strict \(y_L<0\) conclusion combines with
[HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md](HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md):
\[
0<h_{30}<1/16,\qquad
17/200<h_{31}<13/100,\qquad
\text{far-L singleton }y_L<0.
\]
This is still a **continuous, not yet excluded**
S1/k3 subbranch. In particular, this proof
does not show that the far-L singleton is
a whole lower origin-quadrant square:
its center-sign condition alone is weaker.

The far singleton's transverse sign
is defined **relative to the perpendicular
3+0 triple direction**. Under central-frame
reflections the equivalent assertion is that
the singleton center lies on the opposite
side of that axis's origin diameter.

Nothing here eliminates S1/k4..6 or the
actual S4/k7 equality construction.
The unrestricted \(R_8\ge\widehat R\),
global equality classification and Lean
handoff remain OPEN.

[verify_s1_k3_far_singleton_sign.py](verify_s1_k3_far_singleton_sign.py)
checks the new strict rational angle and
cosine comparisons; the proof is the
full-continuum analytic argument above.
