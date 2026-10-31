# Mixed two-share C6: the entire `q >= p` branch is impossible

Date: October 26, 2026.

**Status: complete analytic branch proof accepted after root and separate
independent saved-source and physical-scope review.** See
`REVIEW_C6_CONTACT_TYPE_CLOSURES_ROOT_2026_10_25.md` and
`REVIEW_C6_MIXED_02_SMALL_FORCE_BRANCH_2026_10_26.md`.
The complementary branch is now proved in
`SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md`, with its exhaustive
join reviewed in `REVIEW_C6_MIXED_02_LARGE_FORCE_AND_JOIN_2026_10_26.md`.
This proves a whole force-order
branch of the mixed two-share normal form. It does not by itself exclude
the complementary `q < p` branch or the other two symmetry types. No
numerical optimizer, interval grid, or coefficient certificate is a premise.

Retain the original nine physical squares, all original positive forces,
actual shared means, unique-circle masks, and the radius window

\[
                     79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

The upper endpoint of (1) will not be needed in this branch. Neither the
three extra squares nor the positions of the actual transmitters are
altered or discarded. Their exact equations imply the necessary closure
and virial identities used below.

## 1. Original mixed placement and exact scalar formulas

Use `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md` and
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`. Normalize the actual three
forces by their first positive magnitude, rotate the whole packing, and
write

\[
 \chi=(1,1,0),\qquad \mu=(1,p,q),\qquad p,q>0,
\]
\[
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad n_2=(-c_0,-s_0),
\]
\[
 \pi/2<\theta_i\le3\pi/4,\quad \sum_i\theta_i=2\pi,
 \quad c_i=-\cos\theta_i,\quad s_i=\sin\theta_i,
 \quad A_i=s_i-c_i,\quad h_i=s_i+c_i.
\tag{2}
\]

Here units 0 and 2 are genuinely shared: 0 is outgoing, and 2 is
incoming. Unit 1 is nonshared. The original mean-preserving normal form
gives

\[
 u_0=(0,-1),\quad \ell_0=1-qA_0,\qquad
 u_2=(-s_1,-c_1),\quad \ell_2=1-(q/p)A_2,
\]
\[
 u_1=(X,Y)=\frac{(1+ps_1,1+pc_1)}{L},\qquad
 L=\sqrt{2+p^2+2ph_1},\qquad \ell_1=1.
\tag{3}
\]

All actual chords satisfy \(0<\ell_i\le1\); the case \(A_i=0\),
and thus a genuine share with chord one, is included. In particular the
constant term of \(L^2\) is **2**.

The exact channel closure and virial identities are

\[
 \sum_i(n_i+\ell_i u_i)=0,\qquad R(D_0+D_1+D_2)=N,
\tag{4}
\]
where

\[
 \begin{split}
 D_0&=\sqrt{1+q^2+2qc_0},\\
 D_1&=\sqrt{1+p^2+2pc_1},\\
 D_2&=\sqrt{p^2+q^2+2pqc_2},\\
 N&=2+2p+q(1+h_0+h_2)+L.
 \end{split}
\tag{5}
\]

We prove that (2)--(5) and \(q\ge p\) force \(R<79/40\),
contradicting (1). We use necessary consequences of the original
geometry, so this contradiction also covers every retained physical
completion and every original shared-mean endpoint in this branch.

## 2. Contact closure forces a small force and a short angular interval

Set \(\sigma=1/\sqrt2\), and first retain arbitrary positive \(p,q\).
The first coordinate of (4) is

\[
 X=h_1+c_0-1-(q/p)A_2s_1.
\tag{6}
\]

Subtracting the two coordinates of (4), and using
\(X-Y=pA_1/L\), gives the useful additional identity

\[
 (q-1)A_0=2(1-s_1)+A_1\bigl[p/L+(q/p)A_2\bigr].
\tag{7}
\]

Its right side is positive because \(\theta_1>\pi/2\). Therefore
\(q>1\) and \(A_0>0\). Identity (7) is recorded for the
complementary branch; the radius argument below only needs (6).

Assume now \(q\ge p\). The angle sum gives

\[
                 c_0-A_2s_1=A_1c_2.
\]

Thus (6), \(c_2\le\sigma\), and \(X\ge Y>0\) imply

\[
 \sigma\le X\le h_1-1+\sigma A_1=:U.
\tag{8}
\]

Put \(\alpha=\theta_1-\pi/2\in(0,\pi/4]\). Then

\[
 U-\sigma=2\sin(\alpha/2)
 \bigl[(1-\sigma)\cos(\alpha/2)
              -(1+\sigma)\sin(\alpha/2)\bigr].
\]

Consequently \(\tan(\alpha/2)\le(\sqrt2-1)^2\), which yields

\[
 0\le c_1\le\frac13,
 \qquad s_1\ge\frac{2\sqrt2}{3},
 \qquad \pi/2\le\theta_1\le\theta_*:=\arccos(-1/3).
\tag{9}
\]

The slightly enlarged closed interval in (9) is convenient and harmless.
The two coefficients in
\(U+1=(1+\sigma)s_1+(1-\sigma)c_1\) have squared sum 3.
Hence \(X\le\sqrt3-1\), and

\[
 \frac{1+ps_1}{1+pc_1}=\frac{X}{Y}
 \le H:=\sqrt{2/\sqrt3}<\frac{43}{40}.
\]

The last strict bound follows by squaring twice:
\(3\cdot43^4-4\cdot40^4=16403>0\). Using (9) and
\(\sqrt2>7/5\), we obtain

\[
 p\le\frac{3(H-1)}{2\sqrt2-H}
 <\frac{3}{23}<\frac17.
\tag{10}
\]

It remains to prove the radius contradiction on the entire enlarged
domain (9), \(0\le p\le1/7\), with arbitrary \(q>0\). No
remaining force-ratio partition is used.

## 3. One Cauchy inequality eliminates the unrestricted force `q`

Write \(K=79/40\), and define

\[
 B=1+h_0+h_2,\qquad C=B-K,\qquad T=\sqrt{K^2-C^2}.
\tag{11}
\]

Concavity of \(h(\theta)=\sin\theta-\cos\theta\), at fixed
\(\theta_0+\theta_2=2\pi-\theta_1\), shows

\[
 1+\sqrt2(1+s_1)\le B\le1+2\sqrt2.
\tag{12}
\]

Indeed the minimum is at \(\theta_0=3\pi/4\) or
\(\theta_2=3\pi/4\), where the other \(h\) is
\(\sqrt2s_1\). In particular
\(7/3+\sqrt2\le B<2K\), so \(0<C<K\) and \(T>0\).

Since \(D_2\ge q+pc_2\), and since Cauchy gives

\[
 KD_0=K\sqrt{(q+c_0)^2+s_0^2}
       \ge C(q+c_0)+Ts_0,
\]

the full radius gap has the lower bound

\[
 \begin{split}
 K(D_0+D_1+D_2)-N&\ge G,\\
 G&=KD_1-L-2-2p+Kpc_2+Cc_0+Ts_0.
 \end{split}
\tag{13}
\]

This is a pointwise inequality for every original positive \(q\),
including arbitrarily small or large values. The value of \(q\) has
not been chosen to optimize, center, or change the physical packing.

## 4. The gap increases with `theta_0`

Fix \(\theta_1,p\), so \(\theta_2=2\pi-\theta_1-\theta_0\).
Put \(B'=A_0-A_2\), the derivative with respect to \(\theta_0\).
Direct differentiation gives

\[
 \frac{d}{d\theta_0}(Cc_0+Ts_0)
    =(T-B')\bigl((C/T)s_0-c_0\bigr).
\tag{14}
\]

We prove that the right side is greater than \(3/10\) throughout
the whole domain. The following uniform bounds will also be used below:

\[
 C>23/13,\qquad C/T>2,\qquad 2/3<T<1,
 \qquad 0\le A_0,A_2<1/2.
\tag{15}
\]

For clarity, every one follows from (9)--(12). First
\(C\ge43/120+\sqrt2>23/13\), and
\((23/13)^2>(4/5)K^2\), proving \(C/T>2\).
Also \(K<2\) and \(C^2>3\) give \(T<1\), while

\[
 T^2\ge\delta:=-101/20+(39/10)\sqrt2>9/20>4/9.
\tag{16}
\]

The strict bound \(\delta>9/20\) is just \(\sqrt2>55/39\).
Finally each of \(\theta_0,\theta_2\) is at least
\(5\pi/4-\theta_1\), where \(A=\sqrt2c_1\le\sqrt2/3<1/2\).

There is also the exact identity

\[
 T^2-(B')^2=2(K-1)B-3-4s_1>9/20.
\tag{17}
\]

To check it, expand
\((h_0+h_2)^2+(A_0-A_2)^2=4+4s_1\).
Substituting the lower bound (12) into the right side of (17)
leaves an affine function of \(s_1\) with negative coefficient.
Its minimum on \(s_1\le1\) is exactly \(\delta\) in (16).

We next establish the useful stronger angular bound

\[
                         C/T>\cot(\theta_1/4).
\tag{18}
\]

It suffices to show

\[
 f(\theta):=1+\sqrt2(1+\sin\theta)
                   -K(1+\cos(\theta/4))>0
\]

on \([\pi/2,\theta_*]\). This function is strictly concave since
\(f''=-\sqrt2\sin\theta+(K/16)\cos(\theta/4)<0\).
Its endpoints are positive by the following simple exact comparisons:

\[
 \cos(\pi/8)<37/40,\quad
 1+280/99>K\cdot77/40,
\]
\[
 \cos(\theta_*/4)=\sqrt{(1+1/\sqrt3)/2}<8/9,\quad
 7/3+140/99>K\cdot17/9.
\]

Here \(140/99<\sqrt2<99/70\). For the second cosine bound,
\(3\cdot47^2-81^2=66>0\) proves \(\sqrt3>81/47\).
Concavity gives \(f>0\), so \(C>K\cos(\theta_1/4)\),
which implies (18).

If \(B'\ge0\), then \(\theta_0\le\theta_2\), and hence
\(\theta_0\le\pi-\theta_1/2\). For fixed \(m=C/T>0\),
the function \(\cos\theta+m\sin\theta\) decreases on our obtuse
angular interval. Therefore (18) gives

\[
 (C/T)s_0-c_0
 \ge-\cos(\theta_1/2)+(C/T)\sin(\theta_1/2)>1.
\]

By (15)--(17),
\(T-B'>(9/20)/(T+B')>(9/20)/(3/2)=3/10\).
Thus (14) is greater than \(3/10\). If \(B'<0\), its first
factor is greater than \(2/3\), and its second is greater than
\(2\sigma-\sigma=\sigma\); the same conclusion follows.

Finally \(dc_2/d\theta_0=-s_2\), so (13) gives

\[
 \frac{\partial G}{\partial\theta_0}
 >3/10-Kp\ge3/10-K/7=1/56>0.
\tag{19}
\]

The minimum is consequently at
\(\theta_0=5\pi/4-\theta_1\), equivalently
\(\theta_2=3\pi/4\).

## 5. The gap decreases with `p`

On that angular face \(c_2=\sigma\). Direct differentiation of
(13) gives

\[
 \frac{\partial G}{\partial p}
 =K\frac{p+c_1}{D_1}-\frac{p+h_1}{L}-2+K\sigma.
\]

Here \(D_1\ge1\), \(p+c_1\le10/21\), and
\((p+h_1)/L\ge h_1/\sqrt2\ge\sigma\). The last claim follows
also by differentiating that ratio: its derivative is
\((2-h_1^2)/L^3\ge0\). Consequently

\[
 \frac{\partial G}{\partial p}
 \le K\cdot10/21+(K-1)\sigma-2
 <20/21+3/4-2<0.
\tag{20}
\]

The minimum is therefore at the enlarged force endpoint \(p=1/7\).

## 6. The remaining one-angle gap decreases to its endpoint

Write \(t=c_1\in[0,1/3]\), \(s=\sqrt{1-t^2}\). On the face
\(\theta_2=3\pi/4\),

\[
 c_0=\sigma(s-t),\quad s_0=\sigma(s+t),\quad
 B=1+\sqrt2(1+s),\quad C=B-K,
\]
\[
 G=K\sqrt{1+p^2+2pt}-\sqrt{2+p^2+2p(s+t)}
       -2-2p+Kp\sigma+H(t),
\tag{21}
\]
where

\[
                 H(t)=\sigma[(s-t)C+(s+t)T].
\]

A useful exact factorization of its derivative is

\[
 H'(t)=-\sigma\left[(C-T)+(C+T)t/s\right]
                         \left(1-\frac{\sqrt2t}{T}\right).
\tag{22}
\]

Put \(a=1+\sqrt2-K>0\), so \(C=a+\sqrt2s\). Expanding gives

\[
 T^2-2t^2=\delta+2\sqrt2a(1-s)>9/20.
\]

Therefore, over the entire interval,

\[
 \frac{\sqrt2t}{T}<\sqrt{40/121}
     =\frac{2\sqrt{10}}{11}<\frac35.
\tag{23}
\]

The final comparison follows from \(1000<1089\). We only need
the following two elementary estimates of the factors in (22):

* If \(0\le t\le1/6\), then \(T>2/3\) and \(\sqrt2<3/2\)
  give \(1-\sqrt2t/T>5/8\). Since \(C-T>10/13\) and
  \(\sigma>7/10\), it follows that \(-H'>35/104>3/10\).
* If \(1/6\le t\le1/3\), then
  \((C-T)+(C+T)t/s>10/13+(23/13+2/3)/6=275/234\).
  Equations (22)--(23) give \(-H'>77/234>3/10\).

This is a scalar proof with two transparent factor estimates, not a
subdivision into computational obligations. Since \(s>t\), the
derivative of the second radical in (21) is positive. The derivative
of its first term is at most \(Kp\). Hence, at \(p=1/7\),

\[
                         G'(t)<K/7-3/10=-1/56<0.
\tag{24}
\]

The minimum of (21) is at \(t=1/3\), \(s=2\sqrt2/3\).

## 7. One fixed radical corner has a strictly positive exact reserve

At the corner determined above, set

\[
 D=\sqrt{164/147},\qquad
 L_* =\sqrt{(311+28\sqrt2)/147},\qquad
 T_* =\sqrt{(319-129\sqrt2)/180}.
\]

Substitution into (21) and collection of the \(\sqrt2\) terms give

\[
 G_* =KD-L_* -16/7-17/180
          +(377/504)\sqrt2+(4+\sqrt2)T_*/6.
\tag{25}
\]

Use the three fixed radical comparisons

\[
        D>132/125,\qquad L_*<309/200,\qquad T_*>871/1000.
\tag{26}
\]

Their positive squared reserves, using \(\sqrt2<99/70\) where
needed, are explicitly

\[
 \frac{164}{147}-\left(\frac{132}{125}\right)^2
       =\frac{1172}{2296875},
\]
\[
 \left(\frac{309}{200}\right)^2
      -\frac{311+28(99/70)}{147}=\frac{11707}{5880000},
\]
\[
 \frac{319-129(99/70)}{180}
       -\left(\frac{871}{1000}\right)^2
       =\frac{617}{63000000}.
\]

All coefficients of \(\sqrt2,T_*\) in (25) are positive. Thus
(25)--(26) and \(\sqrt2>140/99\) give the explicit rational reserve

\[
 \begin{split}
 G_*&>\frac{79}{40}\frac{132}{125}-\frac{309}{200}
       -\frac{16}{7}-\frac{17}{180}
       +\frac{377}{504}\frac{140}{99}
       +\frac{4+140/99}{6}\frac{871}{1000}\\
     &=\frac{11891}{2835000}>0.
 \end{split}
\tag{27}
\]

Combining the monotonicities (19), (20), (24) with (13) yields,
throughout the original `q >= p` branch,

\[
 K(D_0+D_1+D_2)-N>11891/2835000>0.
\]

The positive denominator in (4) now forces \(R<K=79/40\), as
claimed. The normalization by \(\mu_0\) is homogeneous: before
normalization the displayed gap is multiplied by the original
\(\mu_0>0\). No physical force, shared mean, or corner was replaced.

## 8. Precise scope of the result

Every mixed `110` two-share configuration with genuine shares at 0
(outgoing) and 2 (incoming), and \(\mu_2\ge\mu_1\), is excluded
over the full retained radius window. This is an entire force-order
branch, including every actual shared-mean endpoint allowed by the
normal form. It uses no coefficient certificate.

The complementary \(\mu_2<\mu_1\) branch is now excluded in
`SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md`; the independently
reviewed exhaustive join closes this complete mixed 0/2 contact type.
The other mixed placement and the constant-bit placement require
their own sources before the whole two-share family can be marked
excluded. The one-share and
strictly obtuse one-radial families, global equality classification,
and the earlier prerequisite-chain audit are unaffected. No original
gate is checked solely by this branch manuscript. No Lean compilation,
CI, workflow dispatch, or numerical proof premise is used.
