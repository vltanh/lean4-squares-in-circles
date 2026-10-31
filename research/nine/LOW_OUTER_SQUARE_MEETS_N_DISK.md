# Every low outer square meets the open inscribed disk of N

Let
\[
E=[1,2]\times[-1/2,1/2],\qquad N_0=(0,3/2),
\qquad K=\{p:|p-N_0|<1/2\}.
\]
Suppose T is a closed unit square, its open interior avoids that of E,
T lies wholly in \(y\ge0\), and its center \((x,y)\) satisfies
\[
\frac12<x<1,\qquad y<1.
\]
Then \(T\cap K\ne\varnothing\). Disk containment is not needed for this
lemma. The conclusion is strict.

## 1. The separating axis against E

Every square has vertical support halfwidth at least 1/2, so \(y\ge1/2\).
The E-coordinate axes cannot separate T and E. A horizontal separator
would require \(x\le1-H_T(e_x)\le1/2\), or x beyond E on the right;
a vertical separator would require \(y\ge1/2+H_T(e_y)\ge1\), or y below
E. All four possibilities are excluded.

Thus a separating normal m is an axis of T, directed from E toward T.
Its horizontal component is negative and its vertical component positive.
Indeed, if \(m_x\ge0\), then
\[
m\cdot((x,y)-(3/2,0))
<\max(m_y,0)\le1,
\]
and more precisely the necessary inequality
\[
m_xx+m_yy\ge 3m_x/2+(|m_x|+|m_y|)/2+1/2
\]
would imply \(-m_x+m_y/2>1/2\) when \(m_y\ge0\), or an even stronger
impossibility when \(m_y<0\). If \(m_x<0\) but \(m_y\le0\), writing
\(m_x=-s\) and \(m_y=-t\), the same inequality would imply
\[
s(1-x)\ge t(y+1/2)+1/2,
\]
whereas \(s(1-x)<1/2\). The zero component cases are already excluded
by the coordinate separators.

Consequently write
\[
m=(-s,t),\qquad u=(t,s),\qquad
s,t>0,\qquad s^2+t^2=1.
\]
These form an orthonormal frame of T. Let
\[
h=\frac{s+t}{2},\qquad q_0=\frac12+\frac t2-s.
\]
Avoidance of E in this frame and whole upper containment give
\[
-sx+ty\ge q_0,\qquad y\ge h.                         \tag{1}
\]

## 2. A finite polygon of possible centers

We enlarge the allowed center region to the closed convex polygon
\[
\mathcal C=\{(x,y):x\ge1/2,\ h\le y\le1,\ -sx+ty\ge q_0\}.
                                                               \tag{2}
\]
The bound x at most one follows automatically, since at y=1 its largest
possible value is
\[
x_1=\frac{t-q_0}{s}=1-\frac{s}{2(1+t)}<1.
\]
At x=1/2 the sloping boundary meets height
\[
y_0=\frac{q_0+s/2}{t}=
\frac12+\frac{1-s}{2t}.
\]
Since
\[
2t(y_0-h)=(1-s)(t-s),
\]
the polygon is a triangle when \(t\ge s\), with vertices
\[
(1/2,y_0),\quad(1/2,1),\quad(x_1,1).
\]
When \(t<s\), it is a quadrilateral with vertices
\[
(1/2,h),\quad(1/2,1),\quad(x_1,1),\quad(x_f,h),
\qquad x_f=\frac{th-q_0}{s}.
\]

For this fixed square orientation, the function
\[
c\longmapsto \operatorname{dist}(N_0,c+[-1/2,1/2]u+[-1/2,1/2]m)
\]
is convex: it is the distance of \(N_0-c\) to a fixed convex square.
It is therefore enough to prove that its value is strictly less than
1/2 at every vertex of (2).

For a center c put \(P=u\cdot c\), \(Q=m\cdot c\). The own coordinates
of \(N_0\) are \((3s/2,3t/2)\), so the exact squared distance is
\[
\bigl(|3s/2-P|-1/2\bigr)_+^2+
\bigl(|3t/2-Q|-1/2\bigr)_+^2.                         \tag{3}
\]

## 3. The upper E-contact vertex

At \((x_1,1)\), \(Q=q_0\). Set
\[
r=\frac{s}{1+t},\qquad w=s+t-1=s(1-r).
\]
The second excess in (3) is w. The first is \(X_+\), where
\[
X=tx_1-s/2-1/2=(1/2-s)(1+r).
\]
To see that the opposite signed excess cannot occur, note
\(3s/2-P=s/2-tx_1\le s/2\le1/2\).

If \(s\ge1/2\), then \(X\le0\) and
\(w\le\sqrt2-1<1/2\), so the distance is strictly less than 1/2.
If \(0<s\le1/2\), then \(0<r<1/3\) and direct substitution of
\(s=2r/(1+r^2)\) gives
\[
X^2+w^2-\frac14
=\frac{r(-6+17r-6r^2+r^3)}{4(1+r^2)}<0.             \tag{4}
\]
Indeed, for \(0\le r\le1/3\), the polynomial in parentheses is at most
\(-6+17/3+1/27=-8/27\).

## 4. The lower E-contact vertex

This vertex occurs only when \(t<s\). At \((x_f,h)\), again \(Q=q_0\),
so the second excess is w. A direct substitution gives
\[
3s/2-P=s-t-1/2+1/(2s)>0.
\]
Its first excess is therefore \(X_+\), where
\[
X=s-t-1+\frac1{2s}\le\frac12-t.
\]
The last inequality follows from
\[
s-\frac32+\frac1{2s}
=(1-s)\left(\frac1{2s}-1\right)<0,
\]
because \(1/\sqrt2<s<1\). Also \(w=s+t-1<t\).
If \(0<t\le1/2\), (3) is strictly less than
\[
(1/2-t)^2+t^2\le1/4.
\]
If \(t\ge1/2\), then X is negative and (3) is
\(w^2\le(\sqrt2-1)^2<1/4\).

## 5. The left vertices

The vertex \((1/2,1)\) is at distance \(1/\sqrt2<1\) from \(N_0\).
Its square's inscribed disk of radius 1/2 therefore intersects K.

If \(t\ge s\), then \(3t-s\ge2t\ge\sqrt2>1\), giving
\(y_0>2/3\). Thus the center \((1/2,y_0)\) is at squared distance at
most \(1/4+(5/6)^2=17/18<1\) from \(N_0\), and its inscribed disk also
intersects K.

It remains to treat \((1/2,h)\) when \(t<s\).
If \(t\ge1/2\), then
\[
st\ge\frac{\sqrt3}{4},\qquad
s+t\ge\frac{1+\sqrt3}{2}>\frac43,
\]
so h is greater than 2/3 and the same inscribed-disk argument applies.
The first inequality follows by writing \(v=t^2\in[1/4,1/2]\) and using
\(v(1-v)-3/16=(v-1/4)(3/4-v)\ge0\).

Finally, if \(0<t\le1/2\), the top vertex of this square is
\[
Z=\left(\frac{1+t-s}{2},\ s+t\right).
\]
Its squared distance satisfies the exact identity
\[
|Z-N_0|^2-\frac14
=\frac t2\left(\frac{7t}{1+s}+3s-5\right)<0.         \tag{5}
\]
Indeed, \(s\ge\sqrt3/2>3/4\), so \(7t/(1+s)<2\), whereas
\(3s-5\le-2\). Thus Z itself lies in K.

All vertices of (2) have distance strictly less than 1/2. Convexity now
proves the asserted strict intersection for every admissible center and
every square orientation.
