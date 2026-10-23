# A common negative angular block for nearly equal outer weights

## 1. Statement

Let the squared circle ceiling \(\rho\) satisfy
\[
 \frac{19577}{5000}\le\rho\le\frac{9789}{2500},
 \qquad R=\sqrt\rho,\qquad h=\frac7{10}.
\]
For \(0<p\le r\) and \(0\le d\le h\), define the usual
negative angular block
\[
 V_{p,r}(d)=r(\cos d-1)
  +R\left\{\sqrt{p^2+r^2}
               -\sqrt{p^2+r^2-2pr\sin d}\right\}.
\tag{1}
\]
All decimals below are exact rationals.

The block increases with its smaller coefficient p on
\(0<p\le r\). It also increases with its larger coefficient
on the following whole coefficient region:
\[
 \boxed{\quad .86\le p/r\le1
  \quad\Longrightarrow\quad
  \partial_r V_{p,r}(d)>.17\sin d\quad(0<d\le h).
  \quad}
\tag{2}
\]
At d=0 both derivatives vanish.

Consequently, whenever
\[
 .86\le k\le1,\qquad 0<l\le k,\qquad k\le n\le1,
\]
one has the split-independent comparison
\[
                  V_{n,1}(d)\ge V_{k,1}(d)
                     \ge V_{k,k}(d)\ge V_{l,k}(d).
\tag{3}
\]
Thus two varying outer pairs \((n,1)\), \((c,1)\), with
\(k\le n,c\le1\), share the same negative minorant
\(V_{l,k}\) as fixed middle pairs \((l,k)\). No derivative
of n or c with respect to an angle is part of (3).

## 2. Monotonicity in the smaller coefficient

Put \(s=\sin d\),
\(N_0=\sqrt{p^2+r^2}\), and
\(N_- =\sqrt{p^2+r^2-2prs}\). Then
\[
 R^{-1}\partial_p V_{p,r}
                     =p/N_0-(p-rs)/N_-.
\tag{4}
\]
If \(p-rs\le0\), the right side is positive. Otherwise
all factors being compared are positive, and
\[
 p^2N_-^2-(p-rs)^2N_0^2
                 =r^2s\{2pr-s(p^2+r^2)\}>0.
\tag{5}
\]
Indeed \(p/r>s\) in this case, while
\(2(p/r)/(1+(p/r)^2)\ge p/r\) because \(p\le r\).
Positive squaring proves (4) is strictly positive when
d>0. This proves the first assertion without an additional
coefficient-ratio restriction.

## 3. An exact integral for the other derivative

Hold p fixed and write \(\lambda=p/r\). Differentiating
the difference of the two norm terms with respect to s
gives the exact identity
\[
 \partial_r V_{p,r}(d)
 =\cos d-1+R\int_0^{\sin d}
       \frac{\lambda^2(\lambda-u)}
                    {(1+\lambda^2-2\lambda u)^{3/2}}\,du.
\tag{6}
\]
For \(.86\le\lambda\le1\) and \(0\le u\le.65\), the
integrand has the uniform lower bound
\[
 \frac{\lambda^2(\lambda-u)}
                    {(1+\lambda^2-2\lambda u)^{3/2}}
       \ge\frac{\lambda^3}{(1+\lambda^2)^{3/2}}.
\tag{7}
\]
Here is a polynomial proof covering the whole rectangle.
For \(0\le z\le1\), the elementary identity with
\(w=\sqrt{1-z}\) gives
\[
 (1-z)^{3/2}-1+\tfrac32z-\tfrac12z^2
                       =-\tfrac12w^2(w-1)^2\le0.
\tag{8}
\]
Set \(a=2\lambda/(1+\lambda^2)\). The polynomial
\[
 P(\lambda,u)=2\lambda^4+\lambda^2-1-2\lambda^3u
\]
decreases with u and strictly increases with \(\lambda\)
on the rectangle: its latter derivative is
\(2\lambda(4\lambda^2+1-3\lambda u)>0\).
Its least endpoint is strictly positive:
\[
 P(.86,.65)=\frac{42147}{6250000}>0.
\tag{9}
\]
After multiplying positive denominators, (9) is exactly
\[
             1-\tfrac32au+\tfrac12a^2u^2
                             \le1-u/\lambda.
\tag{10}
\]
Apply (8) with z=au and use (10). Both sides are positive,
since \(u<\lambda\), and one obtains
\((1-au)^{3/2}\le1-u/\lambda\). Rearranging proves (7).
No subdivision of either coefficient or angle is used.

## 4. The strict slope and the common minorant

The function \(\lambda^3/(1+\lambda^2)^{3/2}\) increases
with \(\lambda>0\). Positive squaring at its least
coefficient and least radius gives
\[
 \frac{19577}{5000}(.86)^6
        -(.54)^2(1+(.86)^2)^3
             =\frac{3823900649831}{78125000000000}>0.
\tag{11}
\]
Thus the right side of (7), multiplied by R, exceeds .54.
Also \(\sin d<.65\) and \(\tan(d/2)<.366\) on \([0,h]\).
The latter bound follows from monotonicity of tangent and
the alternating sine and cosine polynomials at \(u=7/20\):
\[
 .366\left(1-u^2/2+u^4/24-u^6/720\right)
         -\left(u-u^3/6+u^5/120\right)
            =\frac{7007815411}{7680000000000}>0.
\tag{12}
\]
Using \(1-\cos d=\sin d\tan(d/2)\), (6)--(12) imply
\[
 \partial_rV_{p,r}(d)
       >(.54-.366)\sin d>.17\sin d,
\]
which proves (2).

For (3), first increase the smaller coefficient from k
to n in the pair \((k,1)\), using Section 2. Next compare
the larger coefficient r between k and 1 with p=k fixed;
the whole path has \(p/r\ge k\ge.86\), so (2) applies.
Finally increase the smaller coefficient from l to k in
the pair \((l,k)\), again using Section 2. This proves
each comparison in (3), including d=0.

A slightly wider consequence is sometimes useful. If
\(p\ge k\) and \(.86\le p/r\le1\), then
\[
                         V_{p,r}(d)\ge V_{k,k}(d).
\tag{13}
\]
Indeed (2) gives \(V_{p,r}\ge V_{p,p}=pV_{1,1}\), and
\(V_{1,1}\ge0\). The latter follows directly from
\(1-\sqrt{1-s}\ge s/2\):
\[
 V_{1,1}(d)\ge\sin d
                     \{R/\sqrt2-\tan(d/2)\}\ge0.
\]
Homogeneity then gives (13). This includes outer pairs
whose larger coefficient has passed one, provided their
ratio still lies in the stated range.

The argument is an exact differentiation, one positive
integral, and three rational reserves. It uses no numerical
minimizer, angular mesh, or generated coefficient inventory.
