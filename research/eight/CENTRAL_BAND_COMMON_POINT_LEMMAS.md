# Three short polynomial lemmas for the central-depth argument

All squares in this note are closed unit squares contained in the disk
of squared radius \(Q=9789/2500\). With their center ray horizontal, choose
the nearer square axis and reflect if necessary so that

\[
0\le\alpha\le\pi/4,\qquad
(a,-b)=(r\cos\alpha,-r\sin\alpha),\qquad a\ge b\ge0.
\]

The farthest vertex gives

\[
(a+1/2)^2+(b+1/2)^2\le Q. \tag{1}
\]

The proof below uses (1) and the stated lower bound on \(a\). It does not
use a boundary reduction or an interval-tree certificate.

## 1. Statements

**Transverse segment.** If \(a>1/2\), the entire segment

\[
V=\{(11/12,y): |y|\le7/20\}
\]

lies in the interior of the square.

**Band A.** Suppose \(a>5007/10000\). If the center ray makes an angle

\[
|\beta|\le 3741/10000
\]

with the horizontal axis, then \((10007/10000,0)\) lies in the square's
interior. Therefore the smaller center angle of two such squares with
disjoint interiors is greater than \(3741/5000\).

The strict hypothesis on \(a\) is relevant here: at \(\alpha=\beta=0\),
the primary side estimate uses \(10007/10000-a<1/2\).

**Band B.** Suppose \(a\ge107/200\). If the center ray makes an angle

\[
|\beta|\le19/50
\]

with the horizontal axis, then \((41/40,0)\) lies in the square's interior.
The corresponding smaller center angle is greater than \(19/25\).

## 2. A shared polynomial calculation

For \(0\le\theta\le\pi/2\), let \(\rho(\theta)>0\) satisfy

\[
\rho^2+\rho(\cos\theta+\sin\theta)+1/2=Q.
\]

For constants \(C_-,C_+,D,A\) listed below, the required two inequalities
are

\[
\rho(\theta)\cos\theta
 <1/2+C_-\cos\theta-D\sin\theta, \tag{2}
\]

and

\[
C_+\sin\alpha+D\cos\alpha-A\tan\alpha<1/2.
\tag{3}
\]

Set \(u=\tan(\theta/2)\), and introduce the three polynomials

\[
z=1+u^2,\qquad c=1-u^2,\qquad s=2u.
\]

Define

\[
\begin{aligned}
H&=\tfrac12z+C_-c-Ds,\\
P&=H^2z+Hc(c+s)+(\tfrac12-Q)c^2z,\\
V&=\tfrac12cz+Asz-C_+sc-Dc^2.
\end{aligned} \tag{4}
\]

The degrees of \(P,V\) are at most six and four. Since \(D<1/2\), the
right side of (2) is positive. The nonnegative number
\(\rho\cos\theta\) is the nonnegative root of

\[
X^2+X\cos\theta(\cos\theta+\sin\theta)
 +(1/2-Q)\cos^2\theta=0.
\]

This polynomial is increasing for \(X\ge0\), so \(P>0\) on \([0,1]\)
proves (2). Similarly \(V>0\) on \([0,3/7]\) proves (3), because
\(\tan(\alpha/2)\le\sqrt2-1<3/7\).

The constants used in (4) are:

| Case | \(A\) | \(C_-\) | \(C_+\) | \(D\) |
|---|---:|---:|---:|---:|
| Segment | \(1/2\) | \(11/12\) | (11/12) | \(7/20\) |
| A | \(5007/10000\) | \((10007/10000)(9308368/10^7)\) | \((10007/10000)(9308369/10^7)\) | \((10007/10000)(365435/10^6)\) |
| B | \(107/200\) | (\(41/40\)(9286/10000)) | (\(41/40\)(9287/10000)) | (\(41/40\)(371/1000)) |

For case A, put \(h=3741/10000\); for B, put \(h=19/50\). The rational
bounds in the last three columns satisfy

\[
C_-<\lambda\cos h<C_+,\qquad \lambda\sin h<D,
\]

where \(\lambda=10007/10000\) or \(41/40\), respectively. These follow
directly from the alternating cosine series through degrees six and eight
and the sine series through degree nine. All arguments belong to \((0,1)\),
where those alternating truncations have the indicated signs.

## 3. The complete finite arithmetic

In every row, substitute \(u=l+(r-l)v\) and express the indicated polynomial
in the Bernstein basis
\(\binom nk v^k(1-v)^{n-k}\). The listed integers divided by \(10^6\)
are lower bounds for all \(n+1\) coefficients in their natural order. All
are positive, and the basis terms are nonnegative with sum one.

| Case | Polynomial | Interval | Lower coefficient numerators, denominator \(10^6\) |
|---|---|---|---|
| Segment | \(P\) | \([0,1/4]\) | 8011, 14261, 20852, 24921, 25307, 22675, 18731 |
| Segment | \(P\) | \([1/4,1/2]\) | 18731, 14787, 9532, 4674, 2967, 7433, 19695 |
| Segment | \(P\) | \([1/2,1]\) | 19695, 44218, 99921, 199778, 334345, 418333, 180000 |
| Segment | \(V\) | \([0,3/14]\) | 150000, 105357, 66071, 39112, 29658 |
| Segment | \(V\) | \([3/14,3/7]\) | 29658, 20203, 28253, 58985, 115785 |
| A | \(P\) | \([0,1/4]\) | 65047, 66616, 68215, 66933, 61593, 52875, 42551 |
| A | \(P\) | \([1/4,3/8]\) | 42551, 37389, 31825, 26080, 20444, 15250, 10838 |
| A | \(P\) | \([3/8,7/16]\) | 10838, 8631, 6620, 4847, 3354, 2183, 1375 |
| A | \(P\) | \([7/16,1/2]\) | 1375, 566, 120, 76, 471, 1339, 2709 |
| A | \(P\) | \([1/2,1]\) | 2709, 13672, 56758, 146628, 276434, 364583, 144311 |
| A | \(V\) | \([0,3/14]\) | 134309, 88153, 47594, 19679, 9628 |
| A | \(V\) | \([3/14,9/28]\) | 9628, 4603, 4043, 8602, 18819 |
| A | \(V\) | \([9/28,3/7]\) | 18819, 29035, 44909, 66978, 95668 |
| B | \(P\) | \([0,1/2]\) | 143981, 138542, 131658, 99535, 46555, 9605, 5160 |
| B | \(P\) | \([1/2,1]\) | 5160, 714, 28774, 105813, 227896, 317762, 114672 |
| B | \(V\) | \([0,3/14]\) | 119725, 75055, 36206, 10492, 3374 |
| B | \(V\) | \([3/14,15/56]\) | 3374, 1595, 977, 1608, 3563 |
| B | \(V\) | \([15/56,9/28]\) | 3563, 5519, 8800, 13485, 19645 |
| B | \(V\) | \([9/28,3/7]\) | 19645, 31963, 50179, 74860, 106455 |

These are fixed polynomial expansions. For hand checking, if
\(\sum a_jv^j\) is the substituted power expansion, its Bernstein
coefficient of index \(k\) is

\[
b_k=\sum_{j\le k}a_j\frac{\binom{k}{j}}{\binom{n}{j}}.
\]

The script `central_band_polynomials.py` reproduces precisely these rows
using rational arithmetic and records the full coefficients in
`central_band_polynomial_tables.json`.

## 4. Deduction for the transverse segment

For \((11/12,y)\) with \(|y|\le7/20\), the displacement in the square
frame has coordinates

\[
d_e=\tfrac{11}{12}\cos\alpha+y\sin\alpha-a,
\quad
d_f=-\tfrac{11}{12}\sin\alpha+y\cos\alpha+b.
\]

The first strict side estimate follows from \(a>1/2\) and

\[
\left(\frac{11}{12}\right)^2+
\left(\frac7{20}\right)^2<1:
\qquad
d_e<\sqrt{(11/12)^2+(7/20)^2}-1/2<1/2.
\]

Inequality (2) at \(\theta=\alpha\) bounds \(-d_e<1/2\). Applying (2)
at \(\theta=\pi/2-\alpha\), and using
\(\rho(\pi/2-\alpha)=\rho(\alpha)\), gives

\[
b<1/2+\tfrac{11}{12}\sin\alpha-\tfrac7{20}\cos\alpha,
\]

which proves \(d_f<1/2\). Finally (3) and \(b=a\tan\alpha\ge
(1/2)\tan\alpha\) give \(-d_f<1/2\). Thus the entire segment lies in
the interior, including its two endpoints.

## 5. Deduction for the two angular bands

The four-side argument in
`COMMON_POINT_AND_THREE_QUARTER_ANGLE.md` applies with \(5/9\) replaced
by the stated \(A\), and \((h,\lambda)\) replaced by the constants in
Section 1. Explicitly the target point has displacement

\[
d_e=\lambda\cos(\alpha+\beta)-a,
\qquad d_f=-\lambda\sin(\alpha+\beta)+b.
\]

The upper primary side uses \(\lambda-a<1/2\). Inequality (2), with the
strict trigonometric comparisons, bounds the other primary side and the
positive secondary side (the latter by the complementary angle). Inequality
(3) bounds the negative secondary side. All four inequalities are strict.
Rotating the bisector of any two center rays then gives the pair-angle
consequences in Section 1.
