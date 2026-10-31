# A Fermat bound for the six corners derived from an oriented triangle

**Status: complete elementary geometric inequality; root and separate
independent full hand audits passed.**
Let \(f_0,f_1,f_2\) be the vertices of a nondegenerate counterclockwise
triangle, with cyclic indices. Put
\[
                  F_i=f_{i-1}-f_i,\qquad
                  P=\sum_i|F_i|.
\tag{1}
\]
Let \(J\) denote counterclockwise rotation through \(\pi/2\).
Choose one constant \(\chi\in\{0,1\}\), and define
\[
              g_i=\chi f_{i-1}+(1-\chi)f_i+JF_i.
\tag{2}
\]
Thus the \(g_i\) are the consistently selected outer corners of
the three unit-ratio squares erected on the triangle's sides.

**Theorem.**
\[
 \min_x\sum_{i=0}^2\bigl(|f_i-x|+|g_i-x|\bigr)
       \le C P,\qquad
 C=\frac{1+\sqrt{4+\sqrt3}}{\sqrt3}<\frac{79}{40}.
\tag{3}
\]
The proof is independent of square packing and of any stress.
It supplies a whole analytic inequality; no numerical extremum is
used.

## 1. An exact two-variable inequality

For \(p,q\ge0\), put
\[
 D(p,q)=\sqrt{p^2+pq+q^2},\qquad
 E(p,q)=\sqrt{2p^2+(1+\sqrt3)pq+q^2},
\tag{4}
\]
and define
\[
 A=\frac{\sqrt{4+\sqrt3}}{\sqrt3},\qquad
 B=\frac1{2\sqrt{4+\sqrt3}}.
\tag{5}
\]
We claim
\[
                           E(p,q)\le A D(p,q)+B(p-q).
\tag{6}
\]

Write \(s=p+q\), \(t=p-q\). If \(s=0\) all quantities vanish.
Otherwise \(|t|\le s\), and the right side of (6) is positive:
\[
 AD+Bt\ge\left(\frac{\sqrt3 A}{2}-B\right)s>0.
\]
The exact squared identities are
\[
 \begin{split}
 D^2&=\frac34s^2+\frac14t^2,\\
 E^2&=\frac{4+\sqrt3}{4}s^2+\frac12st
                          +\frac{2-\sqrt3}{4}t^2.
 \end{split}
\tag{7}
\]
Since \(2AB=1/\sqrt3\), inequality (6) after squaring is equivalent to
\[
             \frac12st+c_0t^2\le\frac{D}{\sqrt3}t,
 \qquad
 c_0=\frac{2-4\sqrt3}{12}
                -\frac1{4(4+\sqrt3)}<-\frac1{12}.
\tag{8}
\]

For \(t\ge0\), use \(D/\sqrt3\ge s/2\) and \(c_0<0\).
For \(t<0\), put \(u=-t\). Then
\[
 \frac D{\sqrt3}-\frac s2
   =\frac{u^2}{12(D/\sqrt3+s/2)}
   \le\frac{u^2}{12s}\le\frac u{12}<-c_0u.
\tag{9}
\]
This is precisely (8) after division by the negative \(t\).
Thus (6) holds for the whole nonnegative quadrant.

The symmetric estimate
\[
                           D(p,q)\ge\frac{\sqrt3}{2}(p+q)
\tag{10}
\]
follows by subtracting squares; the difference is \((p-q)^2/4\).

## 2. The original triangle's Fermat point

Let \(o\) minimize
\[
                              \sum_i|f_i-o|.
\]
A minimizer exists because the function is continuous and coercive.

If \(o\) is not a triangle vertex, differentiating this convex
function gives
\[
                             \sum_i\frac{f_i-o}{|f_i-o|}=0.
\tag{11}
\]
Three unit vectors summing to zero have pairwise angle \(2\pi/3\).
Thus the three rays from \(o\), in the triangle's counterclockwise
order, have successive angles \(2\pi/3\).

If \(o\) is a triangle vertex, let \(v,w\) be the two unit rays
from it toward the other vertices. The directional derivative
condition is \(|v+w|\le1\); equivalently their angle is at least
\(2\pi/3\). These two cases exhaust every nondegenerate triangle,
including an angle exactly \(2\pi/3\).

The six-point minimum in (3) is at most its value at this particular
point \(o\).

## 3. Interior Fermat point

Translate \(o\) to zero. Write \(p_i=|f_i|\).
For a directed side from \(f_{i-1}\) to \(f_i\), the angle of its
two radial vectors is \(2\pi/3\), so
\[
                       |F_i|=D(p_{i-1},p_i).
\tag{12}
\]
For \(\chi=1\), direct expansion of (2) gives
\[
                         |g_i|=E(p_{i-1},p_i).
\tag{13}
\]
The cross term is positive because the triangle is counterclockwise:
\(f_{i-1}\cdot J(f_{i-1}-f_i)
  =\det(f_{i-1},f_i)=\sqrt3\,p_{i-1}p_i/2\).
For \(\chi=0\), the same formula holds with the two arguments of
\(E\) interchanged.

Sum (6) over the three directed sides. The linear differences cancel
for either constant choice of \(\chi\), giving
\[
                              \sum_i|g_i|\le A P.
\tag{14}
\]
Summing (10) gives
\[
                               \sum_i p_i\le\frac P{\sqrt3}.
\tag{15}
\]
Equations (14)--(15) prove the bound \(CP\) at \(o\).

## 4. Fermat point at a triangle vertex

After a cyclic relabeling, put \(f_0=o=0\), let
\[
                     |f_1|=p>0,\qquad |f_2|=q>0,
\]
and let their angle be \(\theta\ge2\pi/3\).
Then
\[
 |f_2-f_1|^2=p^2+q^2-2pq\cos\theta
              \ge p^2+pq+q^2
              \ge\frac34(p+q)^2.
\tag{16}
\]
Consequently
\[
                       P\ge(1+\sqrt3/2)(p+q).
\tag{17}
\]

For \(\chi=1\), the three derived corners have lengths
\[
 |g_0|=\sqrt2\,q,\qquad |g_1|=p,\qquad
 |g_2|\le\sqrt2\,p+q.
\]
For \(\chi=0\) the reflected list has the same total upper bound.
Adding the two nonzero original vertex lengths yields
\[
             \sum_i(|f_i|+|g_i|)\le(2+\sqrt2)(p+q).
\tag{18}
\]
Thus its ratio to \(P\) is at most
\[
       \frac{2+\sqrt2}{1+\sqrt3/2}<\frac{24}{13}<C.
\tag{19}
\]
For the first comparison use \(\sqrt2<10/7\) and \(\sqrt3>12/7\).
For the second, \(\sqrt{4+\sqrt3}>7/3\) and
\(\sqrt3<7/4\) give \(C>40/21>24/13\).
This proves (3) in the remaining Fermat case.

## 5. Exact comparison with the research lower radius

Finally
\[
 C^2=\frac{5+\sqrt3+2\sqrt{4+\sqrt3}}3
       <\frac{5+7/4+24/5}{3}
       =\frac{77}{20}
       =\frac{6160}{1600}
       <\frac{6241}{1600}
       =\left(\frac{79}{40}\right)^2.
\tag{20}
\]
Here \(\sqrt3<7/4\), and \(4+\sqrt3<23/4<(12/5)^2\).
All quantities are positive, so \(C<79/40\) as asserted.

At an equilateral force triangle the centroid is a six-point
minimizer by rotational symmetry, and equality holds in the first
inequality in (3). The constant \(C\) is therefore sharp for this
pure geometric statement. This observation is not a claim that the
corresponding six physical packing units are feasible.

