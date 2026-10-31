# A common point for upper-pocket squares whose centers have height at least one

Put
\[
D=\{x^2+y^2\le17/4\},\quad
E=[1,2]\times[-1/2,1/2],\quad W=-E,
\quad d=3/7,\quad z=5/4.
\]

**Theorem.** Let T be a physical unit square in D, wholly in \(y\ge0\),
avoiding the open interiors of E and W. If its center \((x,y)\) has
\(x\ge0\) and \(y\ge1\), then \((d,z)=(3/7,5/4)\) lies in the open
interior of T.

In particular T meets the open radius-1/2 disk about \(N_0=(0,3/2)\),
because
\[
|(3/7,5/4)-N_0|^2=\frac{193}{784}<\frac14.
\]

We use two established local facts. Every unit square in D has center
radius at most 3/2, by the exact corner formula. Also every square in D
avoiding W has all its points strictly to the right of x=-2, by the
radial-terminal outer-face screen (RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1). Finally HALF_CAP_CENTER_SEPARATION.md proves the stated
common-point conclusion when the whole square lies above y=1/2.

## 1. Reduce failure to a section endpoint below the cap floor

Since \(1\le y\le3/2\), we have \(|z-y|\le1/4\). The horizontal line
at height z crosses T's open interior. Its right endpoint r satisfies
\[
r\ge x+\sqrt{1/4-(z-y)^2}\ge\sqrt3/4>d,
\]
using T's radius-1/2 inscribed disk and the exact comparison 147>144.
Thus it remains to show that its left endpoint is strictly less than d.

If that failed, reflect T horizontally to obtain a square S with center
horizontal coordinate at most zero, center height at least one, avoiding
W, and with right section endpoint
\[
p=(x_0,z),\qquad x_0\le-d.
\]
If S lay wholly above y=1/2, the negative-sign version of
HALF_CAP_CENTER_SEPARATION.md would put \((-d,z)\) in its open interior,
contradicting this endpoint. Hence S has a point below y=1/2.

Choose an outward normal \(n=(u,v)\), \(u>0\), of a side containing p,
and put \(\tau=(-v,u)\). For some \(0\le\lambda\le1\), the vertices are
\[
P_0=p-\lambda\tau,\quad P_1=p+(1-\lambda)\tau,
\quad Q_0=P_0-n,\quad Q_1=P_1-n.                      \tag{1}
\]
This representation includes section endpoints that are square vertices.
We now exclude both signs of v.

## 2. Nonnegative vertical component

Suppose \(v\ge0\). The bottom vertex is Q_0, so \((Q_0)_y<1/2\).
The upper endpoint of the opposite side is Q_1. In terms of the center
height \(y_S\),
\[
(Q_1)_y=y_S+(u-v)/2>1/2,
\]
since \(y_S\ge1\), \(u>0\), and \(v\le1\). Thus the side Q_0Q_1
crosses y=1/2. Its x-coordinate there is
\[
x_*=x_0-\frac{1-3v/4}{u}.
\]
The exact identity
\[
(1-3v/4)^2-\frac7{16}u^2=(v-3/4)^2
\]
shows
\[
\frac{1-3v/4}{u}\ge\frac{\sqrt7}{4}>\frac47=1-d.
\]
Consequently \(x_*<-1\). The outer-face screen gives \(x_*>-2\),
and points of this side just below the crossing lie in the open interior
of W. This contradicts physical avoidance. The strict radical comparison
is \(343>256\).

## 3. Negative vertical component

Write \(v=-w\), \(w>0\), so \(u^2+w^2=1\). The lowest vertex in (1)
is now P_0, with
\[
(P_0)_y=z-\lambda u<1/2.
\]
Therefore
\[
\lambda u>3/4,\qquad u>3/4,\qquad 0<w<u.             \tag{2}
\]
Whole upper containment gives \((P_0)_y\ge0\). Its horizontal coordinate
is \(x_0-\lambda w\). By the outer-face screen and avoidance of W it is
at least -1. On the other hand
\[
(Q_0)_x=x_0-\lambda w-u\le-d-u<-1.
\]
The side P_0Q_0 therefore crosses x=-1. At that crossing its height is
\[
Y_*=z+\frac wu(x_0+1)-\frac\lambda u.
\]
Avoidance of W requires \(Y_*\ge1/2\): otherwise a nearby point of the
side on its left would lie inside W. Thus
\[
\lambda\le\frac34u+w(x_0+1)
\le\frac34u+\frac47w.                                \tag{3}
\]
Set \(r=1-\lambda\). Since
\[
\left(\frac34\right)^2+\left(\frac47\right)^2
=\frac{697}{784}<1,
\]
equation (3) gives the strictly positive bound
\[
r\ge r_0:=1-\frac34u-\frac47w>0.                     \tag{4}
\]

The opposite upper vertex is
\[
Q_1=(x_0-u+rw,\ z+w+ru).
\]
Its first coordinate is negative: by (2), \(r\le1\) and \(w<u\), so
it is at most \(-d-u+w<0\). For fixed r its squared norm is therefore
minimized over \(x_0\le-d\) at \(x_0=-d\). At that endpoint it equals
\[
F(r)=(d+u-rw)^2+(z+w+ru)^2.
\]
This function is increasing for \(r\ge0\), because
\[
F'(r)=2r+2(zu-dw)>0
\]
by \(z>d\) and \(u>w\). Hence (4) implies
\[
\begin{aligned}
|Q_1|^2\ge F(r_0)
&=\frac{477}{196}+\frac{13}{7}u+\frac12w
  +\frac{1669}{784}w^2+\frac1{14}uw.                 \tag{5}
\end{aligned}
\]
This exact identity follows by expansion and \(u^2=1-w^2\).
Since \(u-1=-w^2/(1+u)\ge-w^2\), (5) gives
\[
|Q_1|^2-\frac{17}{4}
\ge\frac2{49}+\frac12w+\frac{213}{784}w^2
   +\frac1{14}uw>0,
\]
contradicting \(Q_1\in D\).

Both normal signs are impossible. The left endpoint of the original T
must therefore be less than d, while its right endpoint is greater than d.
This proves strict interior containment of \((3/7,5/4)\), and hence the
claimed intersection with the open disk about \(N_0\).
