# A descending stair pocket contains no additional unit square

Date: October 26, 2026.

**Status: complete hand geometric theorem, awaiting independent full-source
review.** The theorem is independent of a containing circle, forces,
contact graphs, and the orientation of the additional square. It supplies
a coupled central/exterior restriction for the original S-leaf C5 family.

Let
\[
 A=[-1,0]\times[L-1,L],\qquad 0<L\le1,
\]
and let
\[
 N=(\beta,\alpha),\qquad
 \alpha\ge\beta>0,\qquad \alpha^2+\beta^2=1.
\tag{1}
\]

**Theorem.** Every physical unit square E with
\[
 E\subseteq[-1,1]\times[0,\infty),\qquad
 \operatorname{int}E\cap\operatorname{int}A=\varnothing
\tag{2}
\]
satisfies
\[
                         \max_{z\in E}N\cdot z\ge\beta+\alpha L.
\tag{3}
\]
Consequently, if \(0\le\ell<L\), the region
\[
 \{(X,Y):-1\le X\le1,\ Y\ge0,\
                    \beta X+\alpha Y\le\beta+\alpha\ell\}
\tag{4}
\]
contains no such additional square.

All containments and separations in this statement are closed. No
strict generic-position convention is needed.

## 1. One support inequality for a square in a quadrant

If a unit square Q is contained in the first quadrant, then
\[
                           \max_Q N\cdot z\ge\alpha+\beta.
\tag{5}
\]
Here and below Q need not be aligned.

To prove this, choose an actual side angle \(0\le\phi\le\pi/2\),
write \(c=\cos\phi,\ s=\sin\phi\), and put \(h=(c+s)/2\).
The two coordinate halfwidths are both h. If the center is \((X,Y)\),
whole-quadrant containment gives \(X,Y\ge h\). Its centered
support in direction N is
\[
 H_N=\frac{\beta c+\alpha s+|\alpha c-\beta s|}{2}.
\]
Thus it suffices to prove
\[
                         (\alpha+\beta)h+H_N\ge\alpha+\beta.
\tag{6}
\]
On either side of \(\tan\phi=\alpha/\beta\), the left side is
a positive linear combination of cosine and sine. Its second
derivative is its negative, so it is concave on each full interval.
At the two outer endpoints its value is \(\alpha+\beta\); at
the intervening endpoint its value is \(1+\alpha\beta\).
The latter is at least \(\alpha+\beta\), since
\((1-\alpha)(1-\beta)\ge0\). This proves (5).

Two immediate consequences handle simple separations from A.
If E is wholly to its right, E lies in the first quadrant, and
(5) implies (3), since \(L\le1\).
If E is wholly above A, translate E by \((1,-L)\). The translated
unit is in the first quadrant by (2), so
\[
 \max_E N\cdot z\ge-\beta+\alpha L+\alpha+\beta
                         =\alpha(L+1)\ge\beta+\alpha L.
\tag{7}
\]

## 2. Exhaust the actual separating axes

For two unit squares with disjoint open interiors, one of their
side-normal directions weakly separates them. This is the elementary
separating-axis property: their Minkowski difference is a convex
polygon whose edge normals are side normals of the original squares;
if zero is not in its open interior, one of those supporting
inequalities separates the two open interiors.

Orient the separating normal n from A toward E:
\[
                         \min_E n\cdot z\ge\max_A n\cdot z.
\tag{8}
\]
The two axes of A give the right or above alternatives already
proved. The left alternative is impossible because E has positive
width and is contained in \(X\ge-1\). The below alternative is
impossible because E has positive height and is contained in \(Y\ge0\),
whereas \(L-1\le0\).

It remains to consider a normal which is an actual side axis of E.
Its centered support in that direction is exactly \(1/2\).
Write the center of E as \((X,Y)\). If the absolute components
of that axis are c,s, then both coordinate halfwidths are
\[
                           h=(c+s)/2.
\]
Equation (2) gives
\[
                        h-1\le X\le1-h,\qquad Y\ge h.
\tag{9}
\]

A southwest normal is impossible. Indeed, if
\(n=(-c,-s)\), its maximum on E is at most c by (2), so its
minimum is at most \(c-1\). Its maximum on A is
\(c+s(1-L)\ge c\), contradicting (8).

A northwest normal \(n=(-s,c)\), with c,s positive, forces
\[
 -sX+cY-\frac12\ge s+cL.
\]
Using \(X\ge h-1\),
\[
 Y\ge L+\frac{sh+1/2}{c}\ge L+h,
\]
because \(1/2+(s-c)h=s^2\). Thus E is wholly above A, and
(7) applies.

A southeast normal \(n=(c,-s)\) similarly gives
\[
 cX-sY-\frac12\ge s(1-L).
\]
Using \(Y\ge h\),
\[
 X\ge\frac{sh+s(1-L)+1/2}{c}\ge h,
\]
because \(1/2+(s-c)h+s(1-L)=s^2+s(1-L)\ge0\).
Thus E is wholly to the right of A, and (5) applies.
Pure coordinate normals have already been included.

Only a northeast side-axis separator remains.

## 3. Shallow northeast side-axis separator

Let \(n=(c,s)\), with \(c\ge s\ge0,\ c^2+s^2=1\).
The separation inequality is
\[
                           cX+sY\ge sL+\frac12.
\tag{10}
\]
Since \(\alpha\ge\beta\) and \(c\ge s\),
\[
 H_N=\frac{\beta(c-s)+\alpha(c+s)}2.
\]
Using (10), \(Y\ge h\), and
\(\alpha-\beta s/c\ge0\), we obtain
\[
 \begin{split}
 \max_E N\cdot z
 &\ge \frac{\beta}{c}\left(sL+\frac12\right)
       +\left(\alpha-\frac{\beta s}{c}\right)h+H_N\\
 &=\beta\left(c-s+\frac{s}{c}L\right)+\alpha(c+s).
 \end{split}
\tag{11}
\]

Subtract \(\beta+\alpha L\) and divide by alpha. The result is
linear in \(k=\beta/\alpha\in[0,1]\):
\[
 c+s-L+k\left(c-s-1+\frac{s}{c}L\right).
\tag{12}
\]
At k=0 it is nonnegative because \(c+s\ge1\ge L\).
At k=1 it is
\[
 2c-1-L(1-s/c)\ge2c-2+s/c\ge0.
\tag{13}
\]
For the last inequality,
\[
 2c-2+\frac{s}{c}
   =\frac{s}{c}\left(1-\frac{2cs}{1+c}\right)\ge0;
\]
use \(2cs\le1\le1+c\).
The complete k interval therefore satisfies (3).

## 4. Steep northeast side-axis separator

Write this normal as \(n=(s,c)\), with
\(c\ge s\ge0,\ c^2+s^2=1\). Now
\[
                       sX+cY\ge cL+\frac12.
\tag{14}
\]
Set \(h=(c+s)/2,\ j=(c-s)/2\).

If \(\beta c\ge\alpha s\), then
\(H_N=\beta h+\alpha j\). The coefficient
\(\beta-\alpha s/c\) is nonnegative, so (9), (14) give
\[
 \begin{split}
 \max_E N\cdot z
 &\ge\left(\beta-\frac{\alpha s}{c}\right)(h-1)
                  +\alpha L+\frac{\alpha}{2c}+H_N\\
 &=\beta(c+s-1)+\alpha\left(L+c-s+\frac{s}{c}\right).
 \end{split}
\tag{15}
\]
After subtracting \(\beta+\alpha L\), use
\(c+s-2<0\), \(\beta\le\alpha\), and (13):
\[
 \beta(c+s-2)+\alpha(c-s+s/c)
                  \ge\alpha(2c-2+s/c)\ge0.
\tag{16}
\]

If \(\beta c\le\alpha s\), then
\(H_N=-\beta j+\alpha h\). The same coefficient is now
nonpositive, so use \(X\le1-h\):
\[
 \begin{split}
 \max_E N\cdot z
 &\ge\left(\beta-\frac{\alpha s}{c}\right)(1-h)
                  +\alpha L+\frac{\alpha}{2c}+H_N\\
 &=\beta(1-c)+
               \alpha\left(L+s+\frac{1-s}{c}\right).
 \end{split}
\tag{17}
\]
The difference from the desired bound is at least
\[
 \alpha\left(s+\frac{1-s}{c}-c\right)
                  =\alpha\,\frac{s(c+s-1)}{c}\ge0.
\tag{18}
\]
The equality between the two coefficient cases belongs to both
valid arguments.

Every possible side-axis separator has now been covered. This
proves (3). If E also lay in (4), its maximum would be at most
\(\beta+\alpha\ell<\beta+\alpha L\), a contradiction.

The proof is an exact all-orientation support argument. It contains
no angle sampling, finite sign certificate, force selection, or
assumption about which corner of E contacts the obstacles.
