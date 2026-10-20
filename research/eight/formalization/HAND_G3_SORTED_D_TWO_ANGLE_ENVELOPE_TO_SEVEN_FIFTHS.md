# The two-angle sorted-D envelope through coefficient seven fifths

## 1. Statement

Use
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=.7,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad c_0=\sqrt{Q/2}-1/2,
 \qquad k_*=.6692.
\tag{1}
\]
All decimals denote exact rationals. Let S be the actual
sorted outer-circle support, and set
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},
\]
\[
 \begin{split}
 D_c(x,y)={}&c\{W(x)-1\}+W(y)-1+(1+c)c_0\\
       &-S(c\sin x+\cos y,c\cos x+\sin y).
 \end{split}
\tag{2}
\]
For \(1\le c\le7/5\), and actual signed arguments with
\[
 P=(x)_++(y)_+\le h,\qquad
 N=(-x)_++(-y)_+\le h,
\]
we have the whole-domain bound
\[
                     D_c(x,y)\ge-.65P+V_{k_*,1}(N).
\tag{3}
\]
Consequently the same statement holds with any
\(.5\le k\le k_*\) in place of \(k_*\), since
\(V_{k,1}\) increases with k on \([0,h]\).

This extends the sorted-D conclusion of
[the original two-angle envelope](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md)
to the larger coefficient interval. Its proof needs one
additional intrinsic endpoint certificate, supplied below.

## 2. The additional endpoint at c=7/5

We prove
\[
                  D_{7/5}(h,-n)+.65h-V_{k_*,1}(n)>0
                          \qquad(0\le n\le h).
\tag{4}
\]
Use the rational constants
\[
 c_-=.8992140,\qquad T_+=2.380990934.
\]
Positive squaring gives
\((c_-+1/2)^2<Q/2\) and \(T_+^2>Q(1+k_*^2)\).
Let \(S_j,C_j\) be the alternating Taylor polynomials
ending at the indicated degree, put c=7/5, and define
\[
 \Phi_-=C_{10}(h)+S_{11}(h),
\]
\[
 A=c\Phi_-+1+(c+1)(c_--1/2)+.65h-T_+>2.0048,
\]
\[
 P(n)=1+c^2+2cS_9(h-n),\qquad
 H(n)=1+k_*^2-2k_*S_9(n),
\]
\[
 Z(n)=4A^2QH(n)-\{Q(P(n)-H(n))-A^2\}^2.
\tag{5}
\]
Here \(H>.58\) on \([0,h]\). The full-circle upper bound
on the final support in (2) gives
\[
 D_c(h,-n)+.65h-V_{k_*,1}(n)
                 \ge A-R\sqrt{P(n)}+R\sqrt{H(n)}.
\tag{6}
\]
The polynomial Z has degree eighteen. Define its exact
rational coefficients by
\(Z(.35+u)=\sum_{j=0}^{18}z_ju^j\). Direct expansion of
(5) gives the single whole-interval coefficient-norm bound
\[
                z_0-\sum_{j=1}^{18}|z_j|(.35)^j>1.585.
\tag{7}
\]
For reproduction, its unrounded value is greater than
1.5855179; (5) and the finite Taylor formulas completely
specify every coefficient. Hence Z is positive throughout
the interval. It follows that
\[
 Q(P-H)-A^2<2A\sqrt{QH},
 \qquad \sqrt{QP}<A+\sqrt{QH},
\]
which proves (4). The first comparison uses the absolute
value bound from Z and therefore needs no sign assumption
on \(Q(P-H)-A^2\).

The c=1 version of (4) is already proved by Sections 2--3 of
[the intrinsic sorted-D endpoint certificates](HAND_G3_POSITIVE_BT3_SORTED_D_ENDPOINT_CERTIFICATES.md).
For fixed x,y, \(D_c(x,y)\) is concave in c: its baseline
and width terms are affine, and its subtracted support is
convex in the affine force. Thus these two endpoints imply
\[
                 D_c(h,-n)+.65h-V_{k_*,1}(n)>0
                  \quad(1\le c\le7/5,\ 0\le n\le h).
\tag{8}
\]

## 3. Support branches on the enlarged interval

Write \(f=c\sin x+\cos y\), \(g=c\cos x+\sin y\).
The second coordinate is always positive:
\[
                         g\ge\cos h-\sin h>.12.
\tag{9}
\]
The first coordinate may now be nonpositive. Such points
belong to the diagonal support branch: if \(f\le0<g\),
the function \(fa(b)+gb\) increases with b on the sorted
arc, since \(a'(b)<0\), and has its maximum at \(a=b=c_0\).
More generally the diagonal branch is \(g\ge f\). The
other two branches have \(f>0\) and retain the usual
interior and tangent-zero formulas from the original
two-angle envelope.

Every analytic estimate in Sections 2--5 of that envelope
continues to hold with the present upper coefficient 7/5:

* On the diagonal branch the derivative of the residual
  \(D_c+.65P-V_{k_*,1}(N)\) in a positive-angle variable
  is at least \(.65-c(c_0-1/2)>.65-1.4(.4)=.09\).
  Its derivative in a negative-angle variable is greater
  than \(1.327-1.101>0\), as in the original endpoint
  calculation.
* The full-circle second derivative in a positive mixed
  argument is less than \(-.055c\): the ordinary norm
  bound applies because \(1/c\ge5/7>1/2\).
* The tangent-zero derivative in that argument is less
  than \(.65-c(.914)<0\).
* At the other mixed boundary, \(D_c(0,-n)\ge V_{k_*,1}(n)\)
  follows from the one-angle sorted-D comparison, whose
  coefficient domain includes \(k_*\le c\le2\).

For clarity, the support paths used by that reduction still
have exactly the stated order. In the mixed quadrant
\(x=t\ge0,y=-n\le0\), f is positive and
\[
 (g/f)'=-c\{c+\sin(t-n)\}/f^2<0.
\]
Thus the order is diagonal, interior, tangent-zero. Its
right endpoint is supplied by (8). The opposite mixed
quadrant is entirely diagonal, since
\[
 f-g=\cos t-\sin t-c(\cos n+\sin n)\le0.
\]
For two positive arguments of fixed total, \(f'=g,g'=-f\)
again gives the same decreasing-ratio support order, with
the same strict concavity on the interior and decreasing
residual on the tangent-zero branch.

For two negative arguments write
\(x=-t,y=-(n-t)\). Then \(f'=-g,g'=f\). While f is
positive its ratio increases; once the diagonal branch is
entered it cannot leave, because
\[
 (f-g)'=-(f+g),\qquad
 f+g=\cos(n-t)-\sin(n-t)+c(\cos t-\sin t)>0.
\tag{10}
\]
This also covers any subsequent f=0 crossing. The initial
point has no tangent-zero branch, and the interior residual
has second derivative \(-c\cos t-\cos(n-t)<0\), exactly
as in the original reduction.

All intrinsic boundaries are therefore safe by the same
concavity and monotonicity argument, using (8) for the only
new endpoint. This proves (3) on every sign quadrant,
including weak support ties and zero arguments.
