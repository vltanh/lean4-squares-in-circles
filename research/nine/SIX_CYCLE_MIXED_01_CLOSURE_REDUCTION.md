# Mixed two-share C6, placement 01: exact closure and a uniform force gap

Date: October 26, 2026.

**Status: complete necessary reduction, accepted after independent full
saved-source and physical-scope review.** See
`REVIEW_C6_MIXED_01_CLOSURE_REDUCTION_ROOT_2026_10_25.md`.
This source derives two whole-domain projections of actual closure and
the strict force-ratio bound `mu_1/mu_0>1+1/sqrt(2)` for the mixed
corner word `110` with shares at loaded units 0 and 1. It does not yet
exclude this full contact orbit or close an original roadmap gate.

All nine original physical squares, the common selected certificate,
every original positive force, every actual shared mean and endpoint,
the true unloaded transmitter equations, the unique physical circle
masks, and the complete radius window are retained. The finite
symmetry cover and unchanged normal form are those of
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`.

## 1. Exact physical data and a harmless force normalization

The corner bits and the genuine shared interfaces in this orbit are

\[
 (\chi_0,\chi_1,\chi_2)=(1,1,0),\qquad S_0W_0, S_1W_1.
\tag{1}
\]

Write `f_i=mu_i n_i`, and normalize the three positive magnitudes by
`mu_0` only in the scalar calculation, giving `(1,p,q)`. Put

\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\qquad
 \sum_i\alpha_i=\pi/2,
\]
\[
 c_i=\sin\alpha_i=-\cos\theta_i,\quad
 s_i=\cos\alpha_i=\sin\theta_i,\quad
 t_i=s_i-c_i\ge0,\quad h_i=s_i+c_i,
 \quad r=1/\sqrt2.
\tag{2}
\]

Rotate so that `n_0=(1,0)`, `n_1=(-c_1,s_1)`, and
`n_2=(-c_0,-s_0)`. The actual shared normal form gives

\[
 u_0=(0,-1),\quad \ell_0=1-qt_0,
 \qquad
 u_1=(s_1,c_1),\quad \ell_1=1-t_1/p,
 \qquad 0<\ell_0,\ell_1\le1.
\tag{3}
\]

The nonshared body 2 has its actual side vertices as ports, so
`ell_2=1`. Its bit-zero support vector is exactly

\[
 g_2=f_2+J(f_1-f_2)
   =(-qh_0-ps_1,\,-qt_0-pc_1),
 \quad u_2=g_2/|g_2|.
\tag{4}
\]

No physical share has been changed to a nonshared interface when an
actual chord equals one.

## 2. Two projections of the unchanged closure equation

The usual bit-zero angular interval, or the positive sum in (4),
puts the absolute direction of `u_2` in

\[
       [\,5\pi/4-\alpha_0,\ \pi+\alpha_1\,]
                       \subset[\pi,5\pi/4].
\tag{5}
\]

Indeed `alpha_0+alpha_1>=pi/4` makes the displayed interval
ordered. Write `u_2=(-m,-n)`. On this interval,

\[
                   m\ge s_1,\qquad n\ge rt_0.
\tag{6}
\]

The actual channel equations imply the unchanged closure
`sum_i(n_i+ell_i u_i)=0`. Its first coordinate gives

\[
 m=1-c_0-c_1+s_1-s_1t_1/p,
\]

and hence the first whole-domain restriction is

\[
 \boxed{\quad X:=p(1-c_0-c_1)-s_1t_1\ge0.\quad}
\tag{7}
\]

The second coordinate and (6) give the slightly stronger exact
necessary inequality

\[
 (q-r)t_0-1-s_0+h_1\ge c_1t_1/p\ge0.
\tag{8}
\]

Thus the weaker useful second restriction is

\[
 \boxed{\quad Y:=(q-r)t_0-1-s_0+h_1\ge0.\quad}
\tag{9}
\]

Since the actual positive chord in (3) gives `qt_0<1`, equations
(8)--(9) imply the strict angular consequence

\[
 \boxed{\quad h_1>(1+r)s_0-rc_0=:L(c_0),\quad}
 \qquad L(c)=(1+r)\sqrt{1-c^2}-rc.
\tag{10}
\]

These estimates include the original shared-mean endpoints. In
particular if `t_0=0`, then (9) would imply
`0>=1+r-sqrt(2)=1-r>0`, so that endpoint is impossible by actual
closure; it was not silently deleted from the input domain.

## 3. A whole-domain strict force-ratio consequence

**Lemma.** Every original configuration of type (1) satisfies

\[
                         p>1+r.
\tag{11}
\]

Suppose instead that `p<=1+r`, and put `kappa=sqrt(2)-1`.
From (7), using `s_1t_1>=0`,

\[
\begin{aligned}
 c_0
 &\le1-c_1-\frac{s_1t_1}{1+r}\\
 &=1-\frac1{1+r}
       +c_1\left(\frac{h_1}{1+r}-1\right)\\
 &\le\kappa-\kappa^2c_1.
\end{aligned}
\tag{12}
\]

Here `h_1<=sqrt(2)`; the last line follows from
`1-1/(1+r)=kappa` and
`sqrt(2)/(1+r)-1=-kappa^2`.

The function `L` in (10) is decreasing and strictly concave on
`[0,r]`, since

\[
 L'(c)=-(1+r)c/\sqrt{1-c^2}-r<0,
 \qquad L''(c)=-(1+r)/(1-c^2)^{3/2}<0.
\tag{13}
\]

For `0<=c<=r`, the affine value `kappa-kappa^2c` runs from
`kappa` to `1-r`. The following elementary lower line holds over
that entire interval:

\[
 L(\kappa-\kappa^2c)>A+Bc,
 \qquad A=\frac{788}{625},\quad B=\frac{2323}{10000}.
\tag{14}
\]

To prove (14), strict endpoint inequalities and concavity suffice.
Here are all the fixed arithmetic checks. First

\[
 r>r_0:=\frac{7071}{10000},\qquad
 \frac12-r_0^2=\frac{959}{10^8}>0.
\tag{15}
\]

At `c=0`, the inequality `L(kappa)>A` can be squared after
moving its nonnegative subtracted term to the other side. The
difference of the two squares is

\[
 (2A+4)r-A^2-2A-\frac12
 >(2A+4)r_0-A^2-2A-\frac12
 =\frac{323}{1562500}>0.
\tag{16}
\]

In (16), one uses `kappa=2r-1` and `r^2=1/2`. Both squared
quantities are positive. At `c=r`, the corresponding inequality
`L(1-r)>A+Br` has squared difference

\[
 \left[2-2(A-\tfrac12)(B+1)\right]r
  +\frac54-(A-\tfrac12)^2-\frac{(B+1)^2}{2}.
\tag{17}
\]

The coefficient of `r` in (17) is
`780827/6250000>0`. Replacing `r` by its lower bound in (15)
makes (17) equal to

\[
                    \frac{30169809}{125000000000}>0.
\tag{18}
\]

This proves both endpoint signs and therefore (14) by the chord
inequality for a concave function. These are fixed radical comparisons,
not an angle or force-ratio certificate packet.

Finally Cauchy's inequality gives, for every `0<=c<=r`,

\[
 \sqrt{1-c^2}+c-Bc
  \le\sqrt{1+(1-B)^2}<A,
\tag{19}
\]

because the last positive squared reserve is exactly

\[
                  A^2-1-(1-B)^2=\frac{5067}{20000000}>0.
\tag{20}
\]

Apply (14) and (19) at `c=c_1`. By (12)--(13),

\[
 h_1<L(\kappa-\kappa^2c_1)\le L(c_0),
\]

contradicting the strict physical consequence (10). This proves (11)
for every positive force triple and every genuine shared mean,
including the allowed endpoints.

## 4. Retained full-family virial obligation

The original support identity in the normalization of Section 1 is

\[
 R(D_0+D_1+D_2)=N,
\]
\[
 D_0=\sqrt{q^2+1+2qc_0},\quad
 D_1=\sqrt{1+p^2+2pc_1},\quad
 D_2=\sqrt{p^2+q^2+2pqc_2},
\]
\[
 N=2+2p+q+qh_0+h_1+
                   \sqrt{p^2+2q^2+2pqh_2}.
\tag{21}
\]

The full mixed-01 exclusion is now assembled in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md`, using a Cauchy gap,
whole-domain monotonicities and fixed endpoint inequalities for all
parameters satisfying these necessary conditions. This source supplies
the physical closure reduction and does not infer that conclusion
from a diagnostic optimization. No original force, mean, body or extra
square is deleted, and no numerical premise, angular subdivision,
Lean compilation or CI action is part of the reduction.
