# Exact endpoints for the two-angle sorted-D minorant

## 1. The intrinsic endpoint statement

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,\quad
 k_*=.6692,\quad c_0=\sqrt{Q/2}-1/2,\quad
 a_0=\sqrt{Q-1/4}-1/2.
\]
For the sorted outer support and width write
\[
 S(f,g)=\max_{0\le b\le c_0}
 \{f(\sqrt{Q-(b+1/2)^2}-1/2)+gb\},\qquad
 W(t)=\frac{1+\cos t+|\sin t|}{2}.
\]
Define
\[
 \begin{split}
 D_c(u,v)={}&c\{W(u)-1\}+W(v)-1+(1+c)c_0\\
 &-S(c\sin u+\cos v,c\cos u+\sin v),\\
 V_*(n)={}&\cos n-1
 -R\{\sqrt{1+k_*^2-2k_*\sin n}-\sqrt{1+k_*^2}\}.
 \end{split}                                                    \tag{1}
\]

**Endpoint lemma.** For every \(0\le n\le h\),
\[
             D_c(h,-n)+.65h-V_*(n)>0
                  \qquad(c=1\text{ or }c=1.1642).                \tag{2}
\]
These are the only scalar endpoints required by
[the whole-domain sorted-D reduction](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md).
The proof below is independent of that reduction. All decimals
denote exact rationals.

## 2. Three rational comparisons of positive radicals

Use
\[
 \underline c=.8992140,\quad \overline a=1.414575672,
 \quad T_0=2.380990934.
\]
Positive squaring gives
\[
 (\underline c+1/2)^2<Q/2,\quad
 (\overline a+1/2)^2>Q-1/4,\quad
 T_0^2>Q(1+k_*^2).
                                                               \tag{3}
\]
Let \(C_j,S_j\) be the ordinary degree-j cosine and sine
Taylor polynomials, and put
\[
 \Phi_-=C_{10}(h)+S_{11}(h).
\]
For \(c\in\{1,1.1642\}\), define the positive rational
\[
 A_c=c\Phi_-+1+(c+1)(\underline c-1/2)+.65h-T_0>1.28.
                                                               \tag{4}
\]
For the variable n put
\[
 P_c(n)=1+c^2+2cS_9(h-n),\qquad
 H(n)=1+k_*^2-2k_*S_9(n),
\]
\[
 Z_c(n)=4A_c^2QH(n)
              -\{Q(P_c(n)-H(n))-A_c^2\}^2.                      \tag{5}
\]
Here \(H>.58\) on \([0,h]\), since \(\sin n<.645\).
The full-circle support bound in (1) gives
\[
 D_c(h,-n)+.65h-V_*(n)
 \ge A_c-R\sqrt{P_c(n)}+R\sqrt{H(n)}.                            \tag{6}
\]
If \(Z_c>0\), then
\[
 Q(P_c-H)-A_c^2<2A_c\sqrt{QH},
\]
so \(\sqrt{QP_c}<A_c+\sqrt{QH}\). Thus (6) is strictly
positive. No sign of the left side in the preceding displayed
inequality is required: (5) bounds its absolute value.

For \(c=1.1642\), the degree-eighteen polynomial (5) has
whole-interval coefficient lower bound
\[
                            Z_{1.1642}>.139.                    \tag{7}
\]
For c=1 use (5) on \(0\le n\le3/8\). Its derivative has
coefficient upper bound below \(-6.23\), and
\[
                              Z_1(3/8)>.228.                    \tag{8}
\]
Hence this part of (2) is also proved.

## 3. The tangent-zero support at the remaining c=1 endpoint

Put \(b=3/8\). For c=1 and \(n\in[b,h]\), the force in (1)
is
\[
                 f=\cos n+\sin h,\qquad
                 g=\cos h-\sin n.
\]
It lies on the tangent-zero support branch:
\[
                            S(f,g)=a_0f.                        \tag{9}
\]
Indeed f,g are positive, and g/f decreases in n: its derivative
has numerator \(-1+\sin(n-h)<0\). At n=b, the exact Taylor
comparison gives
\[
 \frac12\{C_{10}(b)+S_{11}(h)\}
 - (\overline a+1/2)\{C_{12}(h)-S_{11}(b)\}>.0242.
                                                               \tag{10}
\]
Thus \((a_0+1/2)g<f/2\), which is precisely the support
condition for the endpoint b_D=0. This is an intrinsic support
branch, not an assumption about the original D state.

Define
\[
 B_0=\frac{\Phi_--1}{2}-\overline aS_9(h)
          +2\underline c+.65h+\frac12-T_0,
\]
\[
 A(n)=B_0-(\overline a+1/2)C_{12}(n)+\frac12S_{11}(n).
                                                               \tag{11}
\]
Equations (3), (9), and the Taylor bounds give
\[
              D_1(h,-n)+.65h-V_*(n)
                              \ge A(n)+\sqrt{QH(n)}.
\]
It suffices that
\[
                         Y(n)=QH(n)-A(n)^2>0.                   \tag{12}
\]
Write \(n=b+x\), \(0\le x\le13/40\), and center its
degree-twenty-four polynomial at \(x=3/40\):
\[
             Y(b+3/40+z)=\sum_{j=0}^{24}y_jz^j.
\]
The whole interval lies in \(|z|\le1/4\). The exact rational
quantity
\[
          q=y_2-\sum_{j=3}^{24}|y_j|(1/4)^{j-2}
\]
satisfies
\[
                      q>1.754,\qquad
                      y_0-\frac{y_1^2}{4q}>.001.               \tag{13}
\]
Consequently \(Y\ge y_0+y_1z+qz^2>.001\), proving the
remaining part of (2). This completed square covers the entire
axis interval.

## 4. Explicit coefficient verification

For a polynomial \(p(x)=\sum p_jx^j\) on \([0,d]\), put
\[
 a_{j0}=4^{-j}\binom{2j}{j},\qquad
 a_{jr}=2\,4^{-j}\binom{2j}{j-r}\quad(1\le r\le j),
\]
and zero otherwise. Its shifted Chebyshev coefficients are
\[
                       b_r=\sum_jp_jd^ja_{jr}.
\]
The elementary identity
\(u^j=\sum_ra_{jr}T_r(2u-1)\), with \(|T_r|\le1\), gives
\[
             b_0-\sum_{r\ge1}|b_r|\le p
                    \le b_0+\sum_{r\ge1}|b_r|.                 \tag{14}
\]
Equations (4)--(5) and (14) give (7), the derivative bound in
(8), and its endpoint evaluation. Equations (10)--(13) are
direct rational evaluations and one completed square. The
unrounded coefficient bounds are respectively greater than
.139601, below -6.23593, greater than .228173, and greater
than .00100278. The rational outward bounds in (7), (8), and
(13) suffice.

This establishes both endpoints by three explicit polynomial
certificates on their full analytic domains. There is no sampled
minimum, state mesh, interval subdivision inventory, Lean
compilation, or CI premise.
