# Quantitative S1/k3 far-singleton transverse clearance: y_L < -1/75

2026-10-12 research continuation. This is a strict **quantitative
strengthening** of the already proved signed-center theorem
[HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md](HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md).
It removes an entire *open strip* of the last
tiny-offset S1/k3 continuous case without
assuming any common square frame or contact graph.

## Theorem

Assume an eight-square packing of arbitrary orientations
in the disk \(R^2\le9789/2500\), with unique open central
square C and **exclusive one-side** statuses
S1=(3+0,3+1). Suppose exactly **k=3**
exterior centers have norm at least one.

Normalize the 3+1 axis to
\[
R=3,\quad L=1
\]
and the perpendicular 3+0 axis to
\[
U=3,\quad D=0.
\]
Write \(p_L=(x_L,y_L)\) for the far L-singleton
square's actual center.

Then the transverse signed coordinate satisfies
the stronger strict bound
\[
\boxed{y_L<-\frac1{75}.}                        \tag{1}
\]
This supersedes the previous necessary
\(y_L<0\). Under rotations or reflections
the sign is to be interpreted **opposite
to the perpendicular 3+0 triple's outward
direction**.

The other known necessary strict offsets
remain \(17/200<h_R<13/100\) and
\(0<h_U<1/16\). The present proof only
needs \(h_U<13/100\), not its improved
\(1/16\) ceiling.

## 1. The far L ray is extremely close to the negative x direction

The completed sign theorem already proves
\(y_L<0\). Suppose toward contradiction
that \(y_L\ge-1/75\), i.e.
\[
-1/75\le y_L<0.
\]

Because the R triple contains **only one**
outer center (the other two are inner),
[HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md](HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md)
forces \(h_R<13/100\).
Thus the opposite whole L side offset
\(h_L=1-h_R>87/100\) forces
\[
-x_L\ge h_L+1/2>137/100.
\]

Choose the far L center's ordinary polar
angle \(\phi_L\in(\pi,3\pi/2)\), unwrapped
above \(\pi\). Its small deviation from
the negative x direction satisfies
\[
0<\phi_L-\pi
=\arctan\frac{-y_L}{-x_L}
<\frac{(1/75)}{137/100}
=\frac4{411}<\frac1{100},
\]
where the two final strict rational
margins are exact; arctan(t)<t for t>0.
Therefore
\[
\boxed{\pi<\phi_L<\pi+1/100.}                 \tag{2}
\]
The far L singleton has an outer center
because \(-x_L>137/100>1\).

## 2. Its mixed angular gap lowers the northwest U-inner ray

The k=3 counting gives two **inner-center**
R squares and two inner-center U squares,
plus their respective distinct outer square,
and the far L singleton as the third outer.
The four inner rays obey the already proved
strict ordered fan
\[
-\pi/3<\theta_{R-}<0<\theta_{R+}
<\theta_{U+}<\pi/2<\theta_{U-}<5\pi/6,
\]
with **all three consecutive inner-ray
gaps exceeding \(\pi/3\)**.

We prove
\[
\boxed{\theta_{U-}<7\pi/9+1/100.}             \tag{3}
\]
Otherwise, because the U-minus center has
whole upper-cap y projection \(>1/2\),
its radial norm r would obey
\[
r>\frac{1/2}{\sin\theta_{U-}}
\ge\frac{1/2}{\sin(7\pi/9+1/100)}
>\frac{1/2}{\sin(2\pi/9)}
>7/10.
\]
The last comparison follows from
\(\sin(2\pi/9)<2\pi/9<5/7\),
using \(\pi<22/7\).

The established all-frame mixed
inner/outer center theorem
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
then requires the U-minus and far-L
outer center rays to differ by
**more than \(2\pi/9\)**.
But (2) and the hypothetical
\(\theta_{U-}\ge7\pi/9+1/100\)
would give
\[
0<\phi_L-\theta_{U-}
<(\pi+1/100)-(7\pi/9+1/100)
=2\pi/9,
\]
contradiction. Therefore (3) holds.

The three strict inner-center angular gaps
then give
\[
\boxed{
\theta_{U+}<4\pi/9+1/100,\quad
\theta_{R+}<\pi/9+1/100,\quad
\theta_{R-}<-2\pi/9+1/100.
}                                                    \tag{4}
\]

In particular the R-minus inner center radius
is \(>7/10\). Indeed
\(|\theta_{R-}|>2\pi/9-1/100>2/3\),
where the last margin follows from
\(\pi>157/50\):
\[
2(157/50)/9-1/100-2/3=19/900>0.
\]
The alternating cosine Taylor upper bound
at \(2/3\) gives
\[
\cos(2/3)\le191/243<117/140.
\]
Since R-minus has whole-right-cap
x projection \(>117/200\),
its radius satisfies
\[
r>\frac{117/200}{\cos|\theta_{R-}|}
>\frac{117/200}{117/140}=7/10.
\]

## 3. The outer R center cannot fit either ray alternative

Let \(\psi\) be the outer R-square center ray.
Its positive whole-right-cap x projection
\(>117/200\) and radius \(<283/200\)
imply the exact interval
\[
-3\pi/8<\psi<3\pi/8.
\]

The mixed inner/outer center-gap lemmas
under the present radius ceiling give:
* gap \(>2\pi/9\) from R-minus (radius \(>7/10\));
* gap \(>311/500\) from R-plus (radius \(>117/200\));
* gap \(>12/25\) from U-plus (radius \(>1/2\)).

The outer R ray cannot be below R-minus:
by (4) its gap would be
\(<11\pi/72+1/100<2\pi/9\).
Nor can it be above U-plus, since
\(<3\pi/8-\pi/3=\pi/24<12/25\).
Thus it is strictly between R-minus
and U-plus.

If it lies below R-plus, its mixed
gap forces
\[
\psi<\theta_{R+}-311/500
<\pi/9+1/100-311/500.
\]
The R-minus mixed gap then gives
\[
\theta_{R-}<\psi-2\pi/9
<-\pi/9+1/100-311/500<-24/25.
\]
The last strict comparison is exact:
using \(\pi>157/50\),
\[
\frac{157}{450}+\frac{311}{500}
-\frac1{100}-\frac{24}{25}
=\frac1{1125}>0.
\]
But \(\cos(24/25)<117/200\),
by the separately proved exact Taylor
inequality in the S3/k3 negative-ray note.
Since R-minus is inner (radius \(<1\)),
its x projection would be
\(<117/200\), contradicting its mandatory
whole R-cap x projection \(>117/200\).
So this negative alternative is impossible.

The sole alternative is therefore
\[
\psi>\theta_{R+}+311/500>311/500,
\]
while its separation from U-plus and (4)
give
\[
\psi<\theta_{U+}-12/25
<4\pi/9+1/100-12/25<\pi/3.
\]
The final inequality follows from
\(\pi/9+1/100<12/25\) using
\(\pi<22/7\).
Thus
\[
\boxed{311/500<\psi<\pi/3.}                  \tag{5}
\]

## 4. The last positive alternative still overlaps R-plus

The positive-y inner R center has
the exact previously proved rectangle
\[
117/200<p_{R+}.x<1,\qquad
49/500<p_{R+}.y<1.
\]
Its height reserve comes from the
two distinct inner R centers'
mutual unit separation and their
positive whole-R cap x projections.

By (5), the outer R center has
\(q_x,q_y>1/2\) and
\[
q_x<(283/200)\cos(311/500)
<(283/200)(813/1000)
=230079/200000.
\]

Because this outer R square has **only
the R central-side status**, it is
**not** wholly beyond the U side line.
Its vertical center coordinate is
therefore
\[
q_y<h_U+\sqrt2/2
<13/100+177/250
<227/250.
\]
The upper offset bound \(h_U<13/100\)
follows from the triple cap containing
only one outer center.

The two different R-square centers
must hence have squared distance
\[
|q-p_{R+}|^2
<(113079/200000)^2+(81/100)^2
=1-\frac{969139759}{40000000000}<1,
\]
contradicting the disjoint inscribed
half-unit disks.

This rules out the assumption
\(y_L\ge-1/75\), so the far singleton
satisfies \(y_L<-1/75\). QED.

## Exact status and limitations

The still-open exclusive S1/k3 case now
requires all three strict conditions
\[
\boxed{0<h_{30}<1/16,\qquad
17/200<h_{31}<13/100,\qquad
y_L<-1/75}
\]
in the R=3+1, L=1, U=3+0 orientation.
The far L singleton's transverse center
is additionally bounded in absolute
value by the existing sharp one-square
far-cap envelope. This theorem gives a
**genuine open signed-center strip
exclusion**, not an S1/k3 nonexistence
proof or whole-quadrant classification.

The actual S4/k7 equality packing,
the other S1 outer-count cases,
D1/D2 and the unrestricted
\(R_8\ge\widehat R\) remain open.

[verify_s1_k3_far_singleton_clearance.py](verify_s1_k3_far_singleton_clearance.py)
audits the new rational comparisons.


## Combined exact far-singleton transverse lane

The existing arbitrary-orientation one-square
cap envelope also provides the **opposite**
strict transverse ceiling. Because the
R triple has exactly one outer center,
\(h_R<13/100\), so the whole far L offset
\(h_L=1-h_R>87/100\) implies
\[
(|y_L|+1/2)^2
\le q_+-(1+h_L)^2
<9789/2500-(187/100)^2
=4187/10000<(13/20)^2.
\]
Consequently \(|y_L|<3/20\).
Combining with the newly proved signed
negative clearance gives the explicit
**open interval**
\[
\boxed{-3/20<y_L<-1/75.}
\]
These are *actual center-coordinate* bounds,
not a requirement that L lie wholly in
the lower origin quadrant. The remaining
\(0<h_U<1/16\) S1/k3 case is still open.
