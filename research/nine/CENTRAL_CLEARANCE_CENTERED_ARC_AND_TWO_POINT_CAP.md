# Central clearance gives a centered arc and a two-point cap cover

Date: October 26, 2026.

**Status: complete hand geometric proof, pending independent review.**
All squares in this source are actual independently oriented unit
squares. No force equation, positive graph, normal selection, numerical
pose table, or computational sign certificate is a premise.

Put
\[
Q=\frac{1105}{256},\qquad
\rho=\frac{\sqrt{185}}{12},\qquad
\alpha=\arctan\frac13.
\tag{1}
\]

**Theorem 1 (centered arc from central clearance).** Let a closed unit
square \(S\) be contained in the origin-centered disk of squared
radius at most \(Q\), and suppose every point of \(S\) has norm
at least \(1/6\). If its center has polar direction \(\theta\),
then the entire closed arc
\[
\{\rho(\cos(\theta+\delta),\sin(\theta+\delta)):
                                      -\alpha\le\delta\le\alpha\}
\tag{2}
\]
lies in the open interior of \(S\).

The arc is centered at the actual center direction, not merely
somewhere in the square's angular shadow. This permits a fixed-point
consequence that does not require the square to touch the outer circle.

**Theorem 2 (two-point cover on each center side of a cap).** Every unit
square in
\[
D_{\sqrt Q}\cap\{Y\ge1/6\}
\]
whose center has \(X\ge0\) contains at least one of
\[
P_+=\left(\frac13,\frac{13}{12}\right),\qquad
Q_+=\left(\frac{11}{12},\frac23\right)
\tag{3}
\]
in its open interior. Reflection gives the corresponding statement for
\(X\le0\) and points \(P_-,Q_-\) obtained by reversing the first
coordinates.

**Corollary 3 (two obstacles leave cap capacity two).** Suppose two
fixed physical obstacles contain the respective points \(Q_+,Q_-\).
Then at most two pairwise interior-disjoint unit squares in this cap
can be interior-disjoint from those obstacles. It suffices that each
obstacle be a union of closed physical squares, with the corresponding
point in that union. Their loads, contacts and orientations are irrelevant.

All statements reflect or rotate with the entire actual configuration.
In particular the lower-cap version uses the points with negative
second coordinates.

## 1. Complete own-frame coordinates

Choose and sign the square's own perpendicular side axes so its center
is \((x,y)\), where
\[
x\ge y\ge0,\qquad
r=\sqrt{x^2+y^2},\qquad
k=x/r,\quad l=y/r.
\]
Then \(k,l\ge0\), \(k^2+l^2=1\), and the entire square is
\[
[x-1/2,x+1/2]\times[y-1/2,y+1/2].
\tag{4}
\]
Its exact farthest squared corner norm and exact distance from the
origin are
\[
r^2+x+y+\frac12\le Q,\qquad
\sqrt{(x-1/2)_+^2+(y-1/2)_+^2}\ge\frac16.
\tag{5}
\]
Here \(r>0\), so all displayed divisions are valid.

Write
\[
B=\rho\sin\alpha=\frac{\sqrt{74}}{24},\qquad
A=\rho\cos\alpha=3B=\frac{\sqrt{74}}8.
\tag{6}
\]
The two arc endpoints have own-frame coordinates
\[
(Ak-Bl,Al+Bk),\qquad (Ak+Bl,Al-Bk).
\]
Thus their largest absolute displacement on each side axis is
\[
E_1=|A-r|k+Bl,\qquad E_2=|A-r|l+Bk.
\tag{7}
\]
We prove both are strictly less than \(1/2\), over the complete range
in (5), and then check the intermediate arc points separately.

The exact rational estimates used below are
\[
\frac{43}{120}<B<\frac{13}{36},\qquad
\rho<\frac76,\qquad
r<\frac{91}{60}.
\tag{8}
\]
The first two follow by squaring positive quantities. For the last,
(5) gives \(r^2+r+1/2\le Q\), whereas
\[
\left(\frac{91}{60}\right)^2+\frac{91}{60}+\frac12-Q
  =\frac{31}{57600}>0.
\]

## 2. Low centers, with one own-coordinate no larger than one half

Suppose \(r\le A\) and \(y\le1/2\). The distance condition in
(5) gives \(x\ge2/3\). Consequently
\[
E_1=Ak+Bl-x\le\rho-\frac23<\frac12.
\tag{9}
\]
For the other coordinate put \(t=l/k\ge0\); here \(k>0\).
Because \(r\ge(2/3)/k\), (7) gives
\[
E_2\le\frac{B(1+3t)}{\sqrt{1+t^2}}-\frac23t.
\tag{10}
\]
The following exact identity proves that the right side is less than
\(1/2\), for every \(t\ge0\), without subdividing its interval:
\[
\begin{aligned}
&288\left[
 \left(\frac12+\frac23t\right)^2(1+t^2)
                          -B^2(1+3t)^2\right]\\
&\qquad=35-30t-133t^2+192t^3+128t^4\\
&\qquad=
123\left(t-\frac{13}{41}\right)^2+\frac{600}{41}
 +448t\left(t-\frac12\right)^2
 +128\left(t-\frac12\right)^4>0.
\end{aligned}
\tag{11}
\]
Both quantities being compared before squaring are positive. Therefore
(11) proves (10) is strictly less than \(1/2\). This treats \(y=0\)
and \(y=1/2\) as well as every intermediate own-frame angle.

## 3. Low centers with both own-coordinates at least one half

Suppose \(r\le A\) and \(y\ge1/2\). Both \(x-1/2\) and
\(y-1/2\) are nonnegative. If their Euclidean norm is \(D\), then
their sum is at least \(D\), and (5) gives \(D\ge1/6\). Thus
\[
r^2=\frac12+(x-1/2)+(y-1/2)+D^2
 \ge\frac12+\frac16+\frac1{36}=\frac{25}{36}.
\tag{12}
\]
Hence \(r\ge5/6\), and Cauchy's inequality in (7) gives
\[
E_i\le\sqrt{(A-5/6)^2+B^2}<\frac12,\qquad i=1,2.
\tag{13}
\]
For the strict last comparison, \(B^2=37/288\) and \(A=3B\)
give the exact squared reserve
\[
\frac14-\bigl((A-5/6)^2+B^2\bigr)
  =5B-\frac{83}{48}>\frac1{16}>0,
\tag{14}
\]
using \(B>43/120\). This case includes the common boundary
\(y=1/2\).

## 4. Every high center has a useful linear radius bound

Now suppose \(r\ge A\). Put \(w=k+l\in[1,\sqrt2]\) and
\(m=91/60\). The exact corner bound is
\[
r^2+rw+\frac12\le Q.
\tag{15}
\]
We claim
\[
r<m-\frac{w-1}{3}.
\tag{16}
\]
Indeed write \(z=w-1\in[0,\sqrt2-1]\) and \(L=m-z/3\).
The difference between the left side of (15), evaluated at \(L\),
and \(Q\) is
\[
\begin{aligned}
L^2+Lw+\frac12-Q
 &=m^2+m+\frac12-Q
   +\frac{z}{9}\bigl(3(m-1)-2z\bigr)>0.
\end{aligned}
\tag{17}
\]
The first term is \(31/57600>0\). The bracket is positive:
\(3(m-1)=31/20\) while \(2z<1\). Monotonicity of
\(r\mapsto r^2+rw\) on nonnegative radii proves (16).

For either ordered choice \((s,t)=(k,l)\) or \((l,k)\),
equations (7),(16) therefore give
\[
\begin{aligned}
(r-A)s+Bt
 &\le\left(\frac{37}{20}-3B\right)s+Bt
                         -\frac{s^2+st}{3}\\
 &<\frac79s+\frac{13}{36}t-\frac{s^2+st}{3}.
\end{aligned}
\tag{18}
\]
Here
\[
\frac{37}{20}-3B<\frac{31}{40}<\frac79,
\]
and \(B<13/36\). The variables satisfy \(s,t\ge0\) and
\(s^2+t^2=1\), with no ordering needed.

## 5. One whole-angle scalar proves the high-center bound

We show, for every such \(s,t\), that
\[
\frac79s+\frac{13}{36}t-\frac{s^2+st}{3}<\frac12.
\tag{19}
\]
After multiplication by 36, the needed positive difference is
\[
G=18-28s-13t+12s^2+12st=U(s)-V(s)t,
\]
where
\[
U(s)=12s^2-28s+18\ge2>0,\qquad
V(s)=13-12s\ge1>0
\tag{20}
\]
on \(0\le s\le1\). Squaring these positive quantities reduces
the claim to
\[
\begin{aligned}
U(s)^2-V(s)^2(1-s^2)
 &=288s^4-984s^3+1241s^2-696s+155>0.
\end{aligned}
\tag{21}
\]
Put \(z=1-s\in[0,1]\). The polynomial in (21) is exactly
\[
4+14z+17z^2-168z^3+288z^4.
\tag{22}
\]
The function \(168z^3-288z^4\), on all \(z\ge0\), increases
up to \(z=7/16\) and decreases thereafter: its derivative is
\(z^2(504-1152z)\). Its maximum is
\[
42(7/16)^3=\frac{7203}{2048}<4.
\]
Consequently (22) is at least
\[
\frac{989}{2048}+14z+17z^2>0.
\tag{23}
\]
This proves (21), then \(U(s)>V(s)t\), then (19).
Equations (18),(19) prove \(E_1,E_2<1/2\) throughout the
high-center range, including \(r=A\).

The identities (11) and (21)--(23) are displayed hand proofs over
their full intervals. No polynomial coefficient-sign packet is used.

## 6. The entire intermediate arc, not only its endpoints

Let \(\phi\in[0,\pi/4]\) be the own-frame angle of the actual
center. The arc angles range over
\([\phi-\alpha,\phi+\alpha]\subset(-\pi/2,\pi/2)\).
The second coordinate \(\rho\sin\theta-y\) is monotone there,
so its extreme values occur at the two endpoints and are strictly
between \(-1/2,1/2\) by (7).

The first coordinate \(\rho\cos\theta-x\) has its minimum at
an endpoint. Its maximum also occurs at an endpoint unless the
angle interval contains zero. In that remaining case
\(\phi\le\alpha\), so \(y/x\le1/3\).
If \(y\le1/2\), (5) gives \(x\ge2/3\). If \(y>1/2\),
then \(x\ge3y>3/2\), which gives the same weaker bound.
Thus its possible additional maximum satisfies
\[
\rho-x\le\rho-\frac23<\frac12.
\tag{24}
\]
The endpoint lower bound remains strict. Both square side-coordinate
inequalities hold strictly at every point of the whole closed arc.
This completes Theorem 1, including every aligned or equality
boundary feature allowed in its hypotheses.

## 7. Two fixed points cover each center side of a whole cap

Consider a unit in \(Y\ge1/6\), with center \((X,Y)\) and
\(X\ge0\). Its vertical halfwidth is at least \(1/2\), so
\[
Y\ge\frac23,\qquad |(X,Y)|<\frac{91}{60}.
\tag{25}
\]
It satisfies the central-clearance premise of Theorem 1.

Both points in (3) have squared norm \(185/144=\rho^2\).
Their dot and determinant give
\[
\cos(\arg P_+-\arg Q_+)=\frac45,\qquad
\sin(\arg P_+-\arg Q_+)=\frac35.
\]
Hence their angular separation is exactly \(2\alpha\).
Their common angular midpoint has direction \((5,7)\).
Rotating \(Q_+\)'s direction by \(-\alpha\) gives direction
\((41,13)\), while rotating \(P_+\)'s direction by
\(+\alpha\) gives direction \((-1,43)\).

If \(X>0\), (25) yields
\[
\frac YX>\frac{40}{91}>\frac{13}{41};
\tag{26}
\]
if \(X=0\), the center direction is \(\pi/2\).
Thus the actual center direction lies strictly above
\(\arg Q_+-\alpha\) and no higher than \(\pi/2\), which is
strictly below \(\arg P_++\alpha\). The two closed angle
intervals of radius \(\alpha\) about \(Q_+,P_+\) meet at
their midpoint and cover this entire center-direction range.
At least one of these fixed points is therefore on the centered
arc (2), and Theorem 1 puts it in the square's open interior.
This proves Theorem 2. Reflection proves its other center side.

## 8. Capacity with two genuine point obstacles

An extra unit's open interior cannot contain a point of a different
closed physical unit: an interior ball about that point would meet
the other unit's open interior, even when the point is on its boundary.
Hence the two fixed obstacles in Corollary 3 forbid \(Q_+\) and
\(Q_-\) as open-interior points of any extra.

Every extra whose center has \(X\ge0\) therefore contains \(P_+\)
in its open interior, by Theorem 2, so there is at most one such
extra. Every extra with \(X\le0\) similarly contains \(P_-\)
and there is at most one. A center on the axis satisfies both
statements and cannot create a third class. The total is at most two.

The whole-square cap routing and the physical occupation of \(Q_\pm\)
must be proved separately in each application; this theorem does not
replace either obligation by a center-only premise. The universal
centered-arc theorem itself needs no floor direction, only central
clearance and true circle containment. No original checklist gate is
reticked solely on the strength of this source.
