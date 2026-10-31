# Double-shared C6: a table-free circle-slope comparison

Date: October 25, 2026.

**Status: accepted complete analytic replacement after independent review.**
See `REVIEW_C6_DOUBLE_SHARED_TABLE_FREE_2026_10_25.md` for the full
physical-domain, algebraic-identity and endpoint review.
This replaces the 49-coefficient circle comparison in Sections 3--4 of
`SIX_CYCLE_DOUBLE_SHARED_SLOPE_REDUCTION.md` by one elementary inequality.
Together with that source's already analytic torque comparison, the
entire scalar double-shared-channel contradiction is table-free. No
angular partition, Bernstein sign list, numerical sample, or additional
physical hypothesis is used. The retained geometric derivation is
Sections 1--4 of `SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md`.

## 1. Keep the actual circle and torque equations

Use exactly the original angles and physical side chord:

\[
 \frac\pi4\le\alpha,\beta<\frac\pi2,\qquad
 \frac\pi2<\Sigma=\alpha+\beta\le\frac{3\pi}4,\qquad
 \ell=\frac{1-\cos\alpha-\cos\beta}{\sin\beta}>0.
\]

Put

\[
 u=\cos\beta,\quad v=\sin\beta,\quad
 S=\sin\Sigma,\quad C=\cos\Sigma,
\]

\[
 p=1+u+v+S,\quad q=1+v-u-C,\quad
 r=1+u-v-\ell,\quad s=2+u+v.
\]

The actual unique circle corner of the third loaded square is \((A,B)\),
with \(A,B>1/2\). Its two unchanged equal-circle equations are

\[
 pA+qB=\frac{p^2+q^2}{2},\qquad
 rA+sB=\frac{r^2+s^2}{2},\qquad
 \Delta=ps-qr>0.
\]

Define the comparison numerator

\[
 N=(14p+15q)(r^2+s^2)-(14r+15s)(p^2+q^2).
 \tag{1}
\]

Cramer's rule gives the full identity

\[
 N=2\Delta(14B-15A).
 \tag{2}
\]

We will prove the simple uniform bound \(N>7\) throughout the original
physical domain. In particular \(B/A>15/14\).

## 2. A rectangle of elementary trigonometric bounds

The following letters are auxiliary scalars, not physical bodies or
new forces:

\[
 a=u+v,\qquad b=v-u,\qquad h=S-C,\qquad w=S+C,
 \qquad k=\sqrt2-1.
\]

The original angle interval gives

\[
 1\le a\le\sqrt2,\qquad 0\le b\le1,\qquad a^2+b^2=2,
 \qquad 0<h\le\sqrt2,\qquad w\ge0.
 \tag{3}
\]

There is also the whole-domain bound \(w<k\). Indeed, for fixed
\(\Sigma\), concavity of cosine on the allowed interval implies

\[
 \cos\alpha+\cos\beta
 \ge\frac1{\sqrt2}+\cos(\Sigma-\pi/4)
 =\frac{1+w}{\sqrt2}.
\]

Since \(\ell>0\), the left side is strictly less than one. Thus

\[
 0\le w<\sqrt2-1.
 \tag{4}
\]

In the new notation

\[
 p=1+a+\frac{h+w}{2},\quad
 q=1+b+\frac{h-w}{2},\quad
 r=1-b-\ell,\quad s=2+a.
\]

The proof below enlarges the physical domain only by using the bounds
(3)--(4) independently. It does not replace the actual chord or change
any physical contact.

## 3. Increasing the actual chord only improves the circle comparison

Let \(r_0=1-b\), \(T=p^2+q^2\), and \(L=14p+15q\). Let \(N_0\)
denote expression (1) with \(r=r_0\). The exact identity is

\[
 N=N_0+\ell\bigl(14T-2r_0L\bigr)+\ell^2L.
 \tag{5}
\]

Here \(0\le r_0\le1\), \(L>0\), and
\(p\ge2+1/\sqrt2>5/2\). Therefore

\[
\begin{aligned}
 14T-2r_0L
 &\ge14(p^2+q^2)-2(14p+15q)\\
 &=14p(p-2)+14(q-15/14)^2-225/14\\
 &>35/2-225/14=10/7>0.
\end{aligned}
\tag{6}
\]

Equations (5)--(6) show \(N>N_0\), since the actual \(\ell\) is
strictly positive. This is an algebraic lower comparison only; no
physical configuration with zero chord is invoked.

## 4. One short positive decomposition of the zero-chord comparison

Using \(a^2+b^2=2\) and \(h^2+w^2=2\), direct expansion gives

\[
 N_0=K+Hh+Ww,
 \tag{7}
\]

where all three expressions are short quadratics:

\[
\begin{aligned}
 K&=35+51a+29b+30ab-28b^2,\\
 H&=-33/2-16a-45b-ab+29b^2,\\
 W&=-67/2-46a+45b+29ab+b^2.
\end{aligned}
\tag{8}
\]

For a direct check before expansion, the same identity follows from

\[
\begin{aligned}
 r_0^2+s^2&=7+4a-2b,\\
 p^2+q^2&=5+2a+2b+(2+a+b)h+(a-b)w,\\
 14p+15q&=29+14a+15b+(29h-w)/2,\\
 14r_0+15s&=44+15a-14b.
\end{aligned}
\tag{9}
\]

Both coefficients of the trigonometric variables in (7) are negative
throughout the rectangle (3). First, \(b^2\le b\) gives

\[
 H\le-33/2-16a-16b-ab<0.
\]

Second, \(29b-46\le-17<0\) and \(a\ge1\) give

\[
\begin{aligned}
 W&=-67/2+45b+b^2+(29b-46)a\\
 &\le-159/2+74b+b^2\le-9/2<0.
\end{aligned}
\]

Consequently (3)--(4) imply

\[
 N_0\ge K+\sqrt2 H+(\sqrt2-1)W.
 \tag{10}
\]

The right side has the explicit positive decomposition

\[
\begin{aligned}
 K+\sqrt2 H+(\sqrt2-1)W
 ={}&\frac{331}{2}-112\sqrt2\\
 &+(97-62\sqrt2)(a-1)\\
 &+\bigl[(1+28\sqrt2)a-16\bigr]b\\
 &+(30\sqrt2-29)b^2.
\end{aligned}
\tag{11}
\]

All three variable terms are nonnegative. Their coefficients are
strictly positive using only \(1<\sqrt2<3/2\) and \(a\ge1\).
The constant is strictly greater than seven, because

\[
 317^2-8\cdot112^2=137>0,
 \qquad \frac{317}{2}>112\sqrt2.
\]

Thus (10)--(11) prove \(N_0>7\); equations (5)--(6) prove \(N>7\).
There is no finite sign packet left in this comparison.

## 5. Complete torque contradiction and scope

Section 2 of `SIX_CYCLE_DOUBLE_SHARED_SLOPE_REDUCTION.md` already
proves, by elementary whole-domain inequalities,

\[
 \frac{S+\ell C}{S(1-\ell)}<\frac{15}{14}.
\]

The present result, (2), \(\Delta>0\), and \(A>0\) prove

\[
 \frac{15}{14}<\frac BA.
\]

Since \(S,A,1-\ell\) are positive, the original torque expression
must satisfy

\[
 F=S[A-(1-\ell)B]+\ell CA<0,
\]

contradicting the genuine force-and-torque equation \(F=0\). The
original reflection covers either choice of the third square's shared
interface, exactly as before.

Every original positive force, application mean and endpoint, true body
degree, circle-corner mask, transmitter slider and additional physical
packing square remains. The proof uses no post-extraction contact-normal
choice and assumes no special force ratio. The unchanged derivation of
the double-shared channel supplies all hypotheses over its whole
original domain.

The accepted double-shared scalar packet is reduced from **49 to zero
coefficient checks** after independent review.
Including its older predecessor, the entire original 209-sign packet
has an elementary proof. With the already table-free three-share
matching proof, both former C6 packets require zero signs instead of
254. The three targeted packets including ABC R0 now require **270
instead of 1,813** signs; the remaining 270 are solely the large-ratio
ABC scalar certificate.

This replaces an already established exclusion; it creates no new
geometric closure or checklist ID. The remaining one-/two-share C6
completion families, strictly obtuse one-radial family, unrestricted
nine-square theorem, original equality classification and prior global
prerequisite audit are not closed by this scalar replacement. No Lean
compilation, CI or workflow dispatch was used.
