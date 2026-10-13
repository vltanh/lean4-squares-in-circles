# In the surviving S3/k=3 sector the distant D center is strictly left of the y axis

Research continuation, 2026-10-12. This further sharpens the
**last remaining outer-R positive sector** after
[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md).
It is a strict *center-position* exclusion, not a full S3/k3 proof.

## Theorem

Let eight arbitrary-frame, pairwise interior-disjoint unit squares
fit in \(R^2\le9789/2500\). Suppose the seven noncentral
squares have *exclusive* whole-central-side statuses
S3=(3+1,2+1), normalized to
\[
R:3,\quad L:1,\quad U:2,\quad D:1,
\]
with exactly \(k=3\) exterior centers of norm \(\ge1\).

Let \(D\) be the **far** whole lower-cap singleton,
and write its center as \(p_D=(x_D,y_D)\).
Then
\[
\boxed{x_D<0}.                                      \tag{1}
\]
No physical contact or square-frame orientation is assumed.

The known strict remaining geometry also includes
\[
17/200<h_R<13/100,\quad17/200<h_U<1/5,
\]
and the sole outer R center ray
\[
311/500<\psi<8959/10500.
\]

## 1. The lower inner R center has angle below -163/200

The four **distinct inner** R/U centers have forced
angular order \(R_-,R_+,U_+,U_-\), and the R
outer center is above R+ in the remaining positive
sector. The earlier exact mixed inner/outer bound
from HUMAN_FIVE_SQUARE_FAN_REFINED.md gives
\[
\psi-\theta_{R_+}>311/500.
\]
The two distinct inner R centers obey
\(\theta_{R_+}-\theta_{R_-}>\pi/3\).
Consequently the lower inner R ray \(\theta<0\)
satisfies
\[
\theta<\psi-311/500-\pi/3.
\]
With \(\psi<8959/10500\) and
the standard rational lower bound \(\pi>157/50\),
\[
\theta<8959/10500-311/500-157/150
=-1427/1750<-163/200,                            \tag{2}
\]
the last strict difference being \(3/7000>0\).

R-minus is a *whole right-cap* center, hence
\[
p_{R_-}.x\ge h_R+1/2>117/200.                     \tag{3}
\]
Its radius \(r<1\) must also satisfy \(r>17/20\):
since \(|\theta|>163/200\), the cosine
Taylor upper estimate is
\[
\cos|\theta|<\cos(163/200)
\le1-(163/200)^2/2+(163/200)^4/24
<117/170.
\]
The final strict rational difference equals
\[
117/170-[1-(163/200)^2/2+(163/200)^4/24]
=1282540063/652800000000>0.
\]
Using (3) gives
\[
117/200<r\cos|\theta|<(117/170)r,
\]
so
\[
\boxed{17/20<r<1}.                               \tag{4}
\]

## 2. A >77/100-radian mixed-center exclusion at radius >17/20

We prove an exact auxiliary center-distance lemma:
if two different packed unit-square centers have
\(17/20<r<1\) and \(1\le s<283/200\),
then their smaller center-ray angular gap must be
**strictly greater than \(77/100\) radians**.

For \(t=77/100\), the alternating cosine Taylor
lower bound gives
\[
\cos t\ge1-t^2/2+t^4/24-t^6/720>717/1000,
\]
with exact positive margin
\[
653489919911/720000000000000>0.
\]
If the gap were at most \(t\), the cosine law
would force
\[
|p-q|^2<r^2+s^2-(717/500)rs.
\]
The last quadratic is convex separately in r and s,
so its maximum on
\([17/20,1]\times[1,283/200]\) is at a corner.
The **four exact values** are
\[
1259/2500,\quad1999963/2000000,\quad
283/500,\quad194623/200000.
\]
All are strictly below one. But the inscribed open
radius-1/2 disks of two different disjoint-interior
unit squares require their centers to have distance
at least one. Contradiction. The auxiliary
mixed-center lemma follows.

## 3. The D center cannot have x >= 0

The far D whole-cap offset is \(1-h_U>4/5\).
Its center has \(y_D<-(3/2-h_U)<-13/10\)
and norm \(\ge1\). The general disk farthest-vertex
bound gives its radius \(<283/200\).

Suppose contrary to (1) that \(x_D\ge0\).
Then its ordinary center polar angle \(\phi_D\)
is in \([-\pi/2,0)\). The whole far-cap center
envelope actually places it below \(-\pi/3\):
as \(1-h_U>4/5\), that cap is a fortiori beyond
the offset \(5/8\), so the proven polar elevation
theorem in
HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md
applies.

The lower inner R center angle \(\theta\) lies
in \((-\pi/3,0)\), by its inner R-cap
center x projection. Therefore
\[
-\pi/2\le\phi_D<-\pi/3<\theta<-163/200.
\]
Their ordinary polar angular difference
is positive and satisfies
\[
0<\theta-\phi_D<\pi/2-163/200
<77/100,                                         \tag{5}
\]
the last inequality following from the standard
\(\pi<22/7\) and exact margin
\[
77/100+163/200-11/7=19/1400>0.
\]

But the two distinct centers \(R_-\) and D
have radial norms in (4) and \([1,283/200)\).
The mixed-center lemma in section 2 demands
an angular gap **strictly greater than \(77/100\)**,
contradicting (5). Hence \(x_D<0\). QED.

## Role in the remaining case queue

For S3/k=3, the whole remaining outer R center
sector is **positive**:
\(311/500<\psi<8959/10500\).
The far D singleton must now have center in the
**open southwest quadrant** (its y coordinate was
already negative), with
\[
-13/40<x_D<0.
\]
This **does not** assert that the entire rotated
square D lies in that quadrant or that it is
separated from other exterior squares on a
specific pair-owned axis.

The far L singleton, the four inner centers,
the outer R square and their actual support
conditions remain to be coupled for a sharp
radius obstruction. S3/k3 as a whole is **OPEN**,
as are the unrestricted \(R_8\ge\widehat R\)
and the eventual Lean proof. The valid S4/k7
candidate equality branch is untouched.

[verify_s3_k3_distant_d_sign.py](verify_s3_k3_distant_d_sign.py)
audits the exact rational Taylor and
mixed-center corner margins; it is not a
computational proof of global packing optimality.
