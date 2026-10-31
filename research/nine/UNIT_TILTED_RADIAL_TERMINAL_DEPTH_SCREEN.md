# A tilted terminal may be moved radially outward within one exact depth bound

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_DEPTH_SCREEN_AND_ALIGNED_LONG_CERTIFICATE_REDUCTION_RECOVERY_2026_10_26.md. This extends the linked tilted
terminal screen to a radial interval \([D,D+1]\). No force,
circle-contact, mean or graph-degree premise is used.

Let
\[
 0<v<1/4,\quad c=(1+v^2)^{-1/2},\quad s=vc,\quad
 n=(c,s),\quad f=(-s,c),
\]
and suppose
\[
                         1\le D<c+s^2.
\tag{1}
\]
Define
\[
 T=[D,D+1]n+[-1/2-Dv,1/2-Dv]f,\qquad
 S=[1,2]\times[-1/2,1/2].
\tag{2}
\]

**Theorem.** If an arbitrary unit square E satisfies
\[
 E\subseteq\{y\ge0\},\qquad
 \max_E n\cdot z<D+1,\qquad
 E^\circ\cap T^\circ=\varnothing,
\tag{3}
\]
then \(E^\circ\cap S^\circ=\varnothing\).
Reflection gives the same left-terminal theorem. Every orientation
and position of E is retained.

For \(D=1\), (1) is automatic because
\(c+s^2=1+c(1-c)>1\), and the statement is the original linked
tilted-terminal screen.

## 1. A hypothetical intersection lies in the same small inner wedge

The actual two inner vertices of T are
\[
 V_+=(D/c-s/2,c/2),\qquad
 V_-=(D/c+s/2,-c/2).
\tag{4}
\]
This cancellation uses the actual linked transverse offset \(Dv\).

Suppose \(p\in E^\circ\cap S^\circ\). Since E is wholly in the
closed upper half-plane, its interior point has
\[
                     1<p_x<2,\qquad 0<p_y<1/2.
\]
The actual transverse coordinate is strictly inside T's strip.
For the lower side,
\[
 f\cdot p>-2s>-1/2-Dv,
\]
because \(1/2+Dv-2s\ge1/2+v(1-2c)>1/2-v>0\).
For the upper side,
\[
 f\cdot p<c/2-s<1/2-Dv.
\]
Indeed its final difference is
\[
 (c-1)/2+v(D-c)
 <-(1-c)/2+v s^2
 =(1-c)\{v(1+c)-1/2\}<0.
\tag{5}
\]
Here (1) and \(v<1/4\), \(c<1\) give the strict signs.

If \(n\cdot p>D\), these strip inequalities and (3) would put
p inside T. Thus
\[
 n\cdot p\le D,\qquad
 p_x<D/c,\qquad
 p_y<(D-c)/s<s<c/4.
\tag{6}
\]
In particular \(p_y<(V_+)_y\). Also
\[
 (V_+)_x-1=(D-c)/c-s/2
                       <s^2/c-s/2<0,
\tag{7}
\]
because \(s<c/4<c/2\). The other inner vertex has
\((V_-)_x>D/c>p_x\) and \((V_-)_y<0<p_y\).

## 2. Every possible separating direction is strictly northeast

The exact separating-axis theorem supplies an actual axis
\(\omega\) of E or T, oriented so
\[
                       \max_E\omega\cdot z
                         \le\min_T\omega\cdot z.
\tag{8}
\]

First \(\omega\cdot n>0\). If it were negative, compare p with
the point of T having the same strict transverse coordinate and
radial coordinate \(D+1\). By (6), that point has strictly
smaller \(\omega\)-projection, contradicting (8). If
\(\omega\cdot n=0\), the strict transverse interval from (5)
puts a transverse endpoint of T at a smaller projection instead.

If \(\omega_y\le0\), the positive \(n\)-projection forces
\(\omega_x>0\), and \(\omega\cdot f<0\). The minimizing
T vertex is V+. Equations (6)--(7) give
\(\omega\cdot(p-V_+)>0\), again contradicting (8).
If \(\omega_x\le0\), similarly \(\omega_y>0\),
\(\omega\cdot f>0\), the minimizing vertex is V-, and the
opposite strict coordinate inequalities give the same contradiction.
Thus
\[
                              \omega_x,\omega_y>0.
\tag{9}
\]
For an actual T axis, only n remains. All transverse and opposite
axes have already been excluded.

## 3. The radial T axis cannot separate

Let \(M=\max_E x>1\). For an actual square frame
\(\phi\in[0,\pi/2]\), put
\[
 H_\phi=(\cos\phi+\sin\phi)/2,\qquad
 \zeta=\arctan v.
\]
The center of E has x coordinate \(M-H_\phi\) and y coordinate
at least \(H_\phi\). Therefore
\[
 \max_E n\cdot z\ge cM+(s-c)H_\phi
       +\frac{|\cos(\phi-\zeta)|+|\sin(\phi-\zeta)|}{2}.
\tag{10}
\]
The last two terms are at least \(s^2\) on the entire frame
interval. For \(0\le\phi\le\zeta\) they equal
\[
 s\cos\phi+(s-c)\sin\phi,
\]
which strictly decreases to \(s^2\). For
\(\zeta\le\phi\le\pi/2\) they equal
\(s\sin\phi\ge s^2\). Consequently
\[
                  \max_E n\cdot z>c+s^2>D=\min_T n\cdot z,
\tag{11}
\]
contradicting separation by n.

## 4. No original E axis can separate

An actual remaining E axis has
\(\omega=(\cos\theta,\sin\theta)\), \(0<\theta<\pi/2\).
Its own halfwidth is \(1/2\), and its horizontal and vertical
halfwidths both equal \((\cos\theta+\sin\theta)/2\).
The same center bound gives
\[
          \max_E\omega\cdot z
             \ge M\cos\theta+\sin^2\theta
             >\cos\theta+\sin^2\theta.
\tag{12}
\]

For \(0<\theta\le\zeta\), the minimum on T is at V+. The
difference between the last lower bound in (12) and that
minimum is
\[
 D_+(\theta)
 =(1-(V_+)_x)\cos\theta+\sin^2\theta-(c/2)\sin\theta.
\]
The first coefficient is positive by (7). As a function of
\(z=\sin\theta\in[0,s]\), its derivative is
\[
 -\frac{z(1-(V_+)_x)}{\sqrt{1-z^2}}+2z-c/2<0,
\]
because \(s<c/4\). Its minimum is therefore at \(\theta=\zeta\),
where the exact value is
\[
                             D_+(\zeta)=c+s^2-D>0.
\tag{13}
\]

For \(\zeta\le\theta<\pi/2\), the minimum on T is at V-, and
the analogous difference is
\[
 D_-(\theta)
 =(1-(V_-)_x)\cos\theta+\sin^2\theta+(c/2)\sin\theta.
\]
Here the first coefficient is negative, since \(D/c>1\).
Each displayed term increases with \(\theta\) after its sign
is accounted for. Its minimum is again at \(\zeta\), with
\[
                             D_-(\zeta)=c+s^2-D>0.
\tag{14}
\]
Equations (12)--(14) contradict (8) for every actual E axis.
The separating-axis cover is exhaustive, proving the theorem.

## 5. Closed contacts and precise scope

The argument uses disjoint open interiors and hence allows all
closed contact endpoints between E and T. Its strict inequalities
come from the hypothetical open intersection with S, the given
outer screen and the positive depth reserve in (1).
No extra orientation is excluded or chosen numerically.

The upper-screen premise and the linked actual shift \(Dv\) must
be supplied by any application. This theorem alone does not infer
either from a graph degree or a chosen force. It adds no parameter
grid, computational coefficient packet or independent motion of E.
