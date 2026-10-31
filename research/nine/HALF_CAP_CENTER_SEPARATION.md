# A two-point piercing theorem for the half-height cap

**Status:** complete hand proof, with arbitrary square orientations and
physical interior-disjointness. This is a local theorem at squared radius
17/4; it does not assert the unrestricted nine-square lower bound.
The endpoint calculation adapts the method in
[UNRESTRICTED_THREE_SQUARE_CAP.md](UNRESTRICTED_THREE_SQUARE_CAP.md),
with different constants. No Lean compilation or CI has been run.

Put
\[
 D=\{(x,y):x^2+y^2\le17/4\},\qquad
 p_+=(3/7,5/4),\qquad p_-=(-3/7,5/4).
\]

**Theorem 1.** Every closed unit square
\(T\subset D\cap\{y\ge1/2\}\) whose center has nonnegative horizontal
coordinate contains \(p_+\) in its open interior. A square in the same
cap whose center has nonpositive horizontal coordinate contains
\(p_-\) in its open interior.

**Corollary 2.** At most two physically interior-disjoint unit squares
fit in this cap. If there are two, their centers have strictly opposite
horizontal signs. In particular, a square with center on the vertical
axis excludes every other square in the cap.

Indeed, among three centers two have the same weak sign, so their
squares share one of the displayed interior points. Two centers with
the same weak sign give the same contradiction. Reflection gives the
corresponding statements for the cap \(y\le-1/2\).

## 1. Coordinates and the right endpoint

Let \(R=\sqrt{17}/2\), and set
\[
 s=1/2,\qquad z=5/4,\qquad C=\sqrt2,\qquad
 Y_0=s+1=3/2,\qquad K=Y_0/C=3/(2\sqrt2).
\]

The exact corner formula in
[DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md), Section 1,
gives \(|c|\le3/2\) for every unit-square center \(c\) in \(D\).
Choose axes for the square in either form
\[
 u=(a,b),\ v=(-b,a),\qquad\text{or}\qquad
 u=(a,-b),\ v=(b,a),
 \quad a\ge b\ge0,\quad a^2+b^2=1.
\]
Write the center as \((x,y)\), and put
\[
 h=(a+b)/2,\quad t=(a-b)/2,\quad
 w=a+b,\quad d=w-1,\quad\delta=z-y.
\]

The cap condition gives \(y\ge s+h\ge1\); the center bound gives
\(y\le3/2\). Consequently \(|\delta|\le1/4<h\), so the horizontal
line of height \(z\) passes strictly between the bottom and top of the
square. Let \([\ell,r]\) be its horizontal section.

The square contains the radius-\(1/2\) disk about its center. If
\(x\ge0\), its right section endpoint therefore satisfies
\[
 r\ge x+\sqrt{1/4-\delta^2}\ge\sqrt3/4>3/7.                 \tag{1}
\]
The last strict inequality follows from \(147>144\).
We will prove
\[
                         \ell\le C-1<3/7.                  \tag{2}
\]
The final inequality is \(\sqrt2<10/7\), equivalent to \(98<100\).
Together (1) and (2) put \(p_+\) strictly inside the section and hence
inside the square. Reflection in the vertical axis proves the other
half of Theorem 1.

## 2. The circle boundary estimates

For \(0\le Y\le R\), set \(g(Y)=\sqrt{R^2-Y^2}\).
Since \(g(Y_0)=C\), concavity gives
\[
 g(Y_0+d)\le C-Kd,\qquad
 g(Y_0-(1-a))\le C+K(1-a).                                 \tag{3}
\]
Every use below has an argument equal to a lower bound for the positive
height of an actual vertex, so the radicals are defined. We use only
the exact comparisons
\[
 R<25/12,\quad 1<K<9/8,\quad
 0\le b\le a\le1,\quad 1\le w\le\sqrt2.
\]

## 3. Positive tilt

Assume \(u=(a,b),v=(-b,a)\) and \(b>0\). The left endpoint is
\[
 \ell=\max(\ell_1,\ell_2),\qquad
 \ell_1=x-\frac{1/2+b\delta}{a},\qquad
 \ell_2=x+\frac{a\delta-1/2}{b}.                            \tag{4}
\]
The actual top vertex is \(P=(x+t,y+h)\), with
\(P_y\ge s+w=Y_0+d\).

For the first edge, \(a\ell_1=aP_x+bP_y-1-bz\).
The function \(a g(Y)+bY\) is decreasing above height \(Rb\), and
\[
 s+w-Rb=s+a-(R-1)b\ge s+(2-R)b>0.
\]
Thus (3) yields
\[
 a\ell_1\le aC-aKd+b(w-3/4)-1.                             \tag{5}
\]
The algebraic inequality
\[
 b(w-3/4)<1-a+\frac34a(w-1)                                 \tag{6}
\]
follows by writing the right side minus the left as \(E\):
\[
 4E=b(3-a)-7a(1-a)
    =\frac b{1+a}(3+2a-a^2-7ab)>0.
\]
Indeed \(2a-a^2\ge3/4\) for \(a\ge1/\sqrt2>1/2\), while
\(ab\le1/2\), so the last bracket is at least \(1/4\).
Combining (5), (6), and \(K\ge3/4\) proves \(\ell_1<C-1\).

The second edge needs consideration only when
\(\ell_2\ge\ell_1\), equivalently \(\delta\ge t\). Then
\[
 a=h+t\le z-s=3/4,\qquad
 w\ge(3+\sqrt7)/4>11/8.                                    \tag{7}
\]
The lower bound for \(w\) follows since
\(a+\sqrt{1-a^2}\) decreases on \([1/\sqrt2,1]\).
The strict comparison in (7) is \(\sqrt7>5/2\).
Using the same top vertex and the decreasing function \(b g(Y)-aY\),
\[
 b\ell_2=bP_x-aP_y+az
       \le b g(s+w)-a(w-3/4).
\]
Consequently
\[
 C-\ell_2\ge K(w-1)+\frac ab(w-3/4)
             >2w-7/4>1.                                  \tag{8}
\]
Here \(K>1\), \(a/b\ge1\), and \(w>1\). Equations (5)--(8)
prove \(\ell<C-1\) for positive tilt.

## 4. Negative tilt

Assume \(u=(a,-b),v=(b,a)\) and \(b>0\). Now
\[
 \ell=\max(m_1,m_2),\qquad
 m_1=x+\frac{b\delta-1/2}{a},\qquad
 m_2=x+\frac{-a\delta-1/2}{b}.                              \tag{9}
\]
For the actual rightmost vertex \(P=(x+h,y+t)\) we have
\(P_y\ge s+a\) and
\[
 a m_1=aP_x-bP_y+bz-1
       \le a g(s+a)+b(3/4-a)-1.
\]
The second bound in (3) therefore gives
\[
 a(m_1-(C-1))\le b[3/4-F(a)],\qquad
 F(a)=a+\frac b{1+a}(1-Ka).                                \tag{10}
\]
Put \(k=b/(1+a)\). Then
\(0<k\le\sqrt2-1<5/12\) and \(a=(1-k^2)/(1+k^2)\).
Since \(K<9/8\), direct expansion gives
\[
 F(a)-3/4>
 \frac{2-k-14k^2+17k^3}{8(1+k^2)}>0.                        \tag{11}
\]
For completeness, the numerator has derivative
\(-1+k(51k-28)<0\) on \([0,5/12]\), and at \(5/12\) its value
is \(661/1728>0\). Thus (10) proves \(m_1<C-1\).

For the actual top vertex \(P=(x-t,y+h)\), the full-circle support
bound gives
\[
 b m_2=bP_x+aP_y-az-1\le R-az-1.
\]
The concave function \(za+(C-1)\sqrt{1-a^2}\) on
\([1/\sqrt2,1]\) is bounded below by the smaller endpoint value:
\[
 za+(C-1)b
 \ge\min\{5/4,\ 1+1/(4\sqrt2)\}>9/8>R-1.                   \tag{12}
\]
The first strict comparison uses \(\sqrt2<2\); the second follows
from \(R<25/12\). Thus \(b m_2<b(C-1)\), proving the remaining
edge bound.

## 5. Axis-aligned squares and conclusion

If \(b=0\), then \(a=1\), \(y\ge1\), and the farthest-corner
condition gives
\[
 (|x|+1/2)^2+(y+1/2)^2\le17/4.
\]
Hence \(|x|+1/2\le\sqrt2=C\), so
\(\ell=x-1/2\le C-1\). This completes (2) in every orientation.
The strict comparisons with \(3/7\), rather than equality in the
endpoint estimate, ensure that all asserted common points lie in open
interiors. Boundary contact between otherwise disjoint squares is
therefore fully allowed throughout. \(\square\)
