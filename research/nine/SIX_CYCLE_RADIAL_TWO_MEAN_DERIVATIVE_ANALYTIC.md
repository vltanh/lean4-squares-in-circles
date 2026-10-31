# A table-free derivative inequality for two radial mean interfaces

Date: October 26, 2026.

**Status: complete scalar proof, accepted after independent C6 and root
reviews.** See REVIEW_C6_RADIAL_TWO_MEAN_DERIVATIVE_C6_2026_10_26.md
and REVIEW_C6_RADIAL_MEAN_FAMILIES_ROOT_2026_10_26.md.
This source proves one whole-domain rational
inequality. It introduces no coefficient packet or sampled sign premise.
The geometric author must separately establish the domain and the connected
interpolation for actual original radial applications before using this
inequality to classify a physical core.

## 1. Scalar domain and the derivative expression

Let
\[
 a\ge\frac43,\qquad \frac47\le u\le1,\qquad
 \frac12\le r<1,\qquad D=1-ur>0,
 \qquad k=\frac{1-u}{D}.
\tag{1}
\]
Define
\[
 \mathcal B=
 \left(1-\frac{1+u}{a(u+r)}\right)
       \left(2-2k+\frac{k^2}{a}\right)
 -\frac{r(1+u)(a-k)^2}{a^2D}.
\tag{2}
\]
The conclusion is
\[
                         \boxed{\mathcal B<0.}
\tag{3}
\]

For the radial mean-port notation, set
\(u=c/s\), \(r=b/a\), \(Z=as-bc\), \(A=ac+bs\),
\(C=c+s\), and \(t=(s-c)/Z\). Thus
\[
 t=k/a,\quad C/A=(1+u)/(a(u+r)),\quad
 t'=\frac{(a-k)(1+u)}{a^2D}.
\]
Whenever these are the original geometric quantities, the derivative
bracket
\[
 (1-C/A)\{2-a(2t-t^2)\}-t'(1-t)b
\]
is exactly (2). In particular the geometric formula
\[
 F_M'=2b\big[(1-C/A)\{2-a(2t-t^2)\}-t'(1-t)b\big]
\tag{4}
\]
and \(b>0\) give \(F_M'<0\). Equation (4) and its geometric domain
are not asserted here without the separate physical derivation.

The purely algebraic positive clearing is
\[
 a^2(u+r)D^3\mathcal B=P(a,u,r)
      =A_2a^2+A_1a+A_0,
\tag{5}
\]
where
\[
 A_2=(u+r)(2u-r-3ur)D^2,
\]
\[
 A_1=(u+r)(1-u)\{(1-u)+2r(1+u)\}D
           -2u(1+u)(1-r)D^2,
\]
\[
 A_0=-(1+u)(1-u)^2(1+r^2).
\tag{6}
\]
These identities follow by substituting \(k=(1-u)/D\) in (2).

It suffices to prove
\[
 Q=P(4/3,u,r)<0,\qquad
 Q_a=P_a(4/3,u,r)<0,\qquad A_2\le0.
\tag{7}
\]
Indeed, the last inequality makes \(P_a\) nonincreasing in \(a\),
so the first two imply \(P(a,u,r)<0\) for all \(a\ge4/3\).

## 2. The quadratic coefficient is nonpositive

The sign is that of \(2u-r-3ur=u(2-3r)-r\). If
\(r\ge2/3\), this is negative. If \(1/2\le r\le2/3\),
using \(u\le1\) gives
\[
               u(2-3r)-r\le2-4r\le0.
\]
Thus \(A_2\le0\); equality at the scalar corner
\((u,r)=(1,1/2)\) causes no difficulty because the other two
inequalities in (7) will be strict there.

## 3. The endpoint value is negative on the entire rectangle

Put
\[
             x=1-u\in[0,3/7],\qquad y=1-r\in(0,1/2].
\tag{8}
\]
A direct expansion of (5)--(6) gives
\[
 -9Q=B_0(x)+B_1(x)y+y^2\{B_2(x)+B_3(x)y+B_4(x)y^2\},
\tag{9}
\]
where
\[
 B_0=2x^2(1-2x)(2-x)\ge0,
\]
\[
 B_1=2x(16-46x+45x^2-10x^3)\ge0,
\]
\[
 B_2=64-272x+422x^2-253x^3+40x^4,
\]
\[
 B_3=-112+408x-496x^2+224x^3-24x^4,
\]
\[
 B_4=16(1-x)^2(4-3x)>0.
\tag{10}
\]
For the displayed sign of \(B_1\), its cubic factor has derivative
\[
 -46+90x-30x^2\le-46+270/7=-52/7<0
\]
and endpoint value \(1291/343>0\).

The one-dimensional discriminant identity is
\[
 4B_2B_4-B_3^2=64(1-x)^3 W(x),
\]
\[
 W(x)=60-184x+251x^2-93x^3-21x^4+9x^5.
\tag{11}
\]
For \(0\le x\le3/7\),
\[
 W''(x)=502-558x-252x^2+180x^3
            \ge\frac{10612}{49}>0.
\]
Consequently \(W'\) is increasing, and
\[
 W'(x)\le W'(3/7)=-\frac{60496}{2401}<0.
\]
Thus \(W\) is decreasing and
\[
 W(x)\ge W(3/7)=\frac{325146}{16807}>0.
\tag{12}
\]
The quadratic in braces in (9) is strictly positive for every real
\(y\), by the exact completed square
\[
 B_2+B_3y+B_4y^2
 =B_4\left(y+\frac{B_3}{2B_4}\right)^2
       +\frac{4B_2B_4-B_3^2}{4B_4}>0.
\]
Since the actual scalar domain has \(y>0\), equations (9)--(12)
give \(-9Q>0\), including \(u=1\) and \(r=1/2\).

## 4. The endpoint derivative is negative by a cubic chord identity

The same substitution yields the shorter factorization
\[
                      -3Q_a=D\,T(x,y),
\tag{13}
\]
where
\[
 T=T_0(x)+U(x)y+V(x)y^2+W_3(x)y^3,
\]
\[
 T_0=x(2-x)(4-5x)\ge0,
\]
\[
 U=32-96x+83x^2-20x^3,
\]
\[
 V=-68+158x-106x^2+18x^3,
\]
\[
 W_3=32-56x+24x^2=8(1-x)(4-3x)>0.
\tag{14}
\]
At the other endpoint, writing \(u=1-x\),
\[
 T(x,1/2)=-1+u+\frac52u^2+\frac12u^3
                      \ge\frac{165}{343}>0.
\tag{15}
\]
This follows from monotonicity of the displayed polynomial in
\(u\ge4/7\), with equality in the lower bound at \(u=4/7\).

Moreover,
\[
 V+W_3=-36+102x-82x^2+18x^3.
\]
Its derivative is at least
\(102-164(3/7)=222/7>0\). Hence
\[
 V+W_3\le(V+W_3)(3/7)=-\frac{2034}{343}<0.
\tag{16}
\]
The cubic lies above its endpoint chord by the exact identity
\[
\begin{split}
 T(x,y)-\{(1-2y)T_0(x)+2yT(x,1/2)\}
 &=y(y-1/2)\{V+W_3(y+1/2)\}\ge0.
\end{split}
\tag{17}
\]
Here \(y(y-1/2)\le0\), while \(y+1/2\le1\) and
\(W_3>0\) make the other factor at most \(V+W_3<0\).
Because \(y>0\), equations (15) and (17) imply \(T>0\).
With \(D>0\), equation (13) gives \(Q_a<0\).

This completes (7), hence (3), over the full unpartitioned domain (1).

## 5. Scope of the result

The proof uses factorization, monotonicity, one completed square and
one cubic chord identity. The displayed rational values are endpoint
reserves derived from these whole-interval arguments; they are not a
list of interval-cell controls or a replacement certificate packet.

This source alone does not classify a radial body, alter any contact
mean, suppress a zero individual circle weight, or count any extra
square. The complete original geometric hypotheses, admissible
interpolation and equal actual port norms must be supplied by the
physical M/M classification. In particular any claim that every
actual norm root has \(\eta<\pi/3\) remains a separate required step.
