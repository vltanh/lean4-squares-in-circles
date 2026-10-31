# A whole unit above the bisector cannot pass the tilted radial terminal

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_TILTED_TERMINAL_AND_DOUBLE_AXIS_LONG_C6_RECOVERY_2026_10_26.md. This present text is recovered from the exact
argument. No historical PASS is asserted for a reconstructed file.

Let
\[
 0<v<1/4,\quad c=(1+v^2)^{-1/2},\quad s=vc,\quad
 n=(c,s),\quad f=(-s,c),
\]
and put
\[
 T=[1,2]n+[-1/2-v,1/2-v]f,\qquad
 S=[1,2]\times[-1/2,1/2].
\tag{1}
\]

**Theorem.** If a closed unit square E, of any orientation, satisfies
\[
 E\subseteq\{y\ge0\},\qquad \max_E n\cdot z<2,\qquad
 E^\circ\cap T^\circ=\varnothing,
\tag{2}
\]
then \(E^\circ\cap S^\circ=\varnothing\).

There is no containing-circle hypothesis. The terminal shift in (1)
is retained exactly. The statement is a whole-unit exclusion, not a
pointwise inclusion of S in T.

## 1. Any hypothetical intersection lies in the inner terminal wedge

Suppose \(p\in E^\circ\cap S^\circ\). Since E is in the upper
half-plane, its interior point satisfies
\[
                    1<p_x<2,\qquad0<p_y<1/2.
\tag{3}
\]
Its actual transverse coordinate obeys
\[
 -2s<f\cdot p<c/2-s<1/2-v.
\]
The lower endpoint also lies strictly above \(-1/2-v\), since
\(2s<2v<1/2<1/2+v\). For the upper comparison use
\[
 c/2-s-(1/2-v)=(1-c)(v-1/2)<0.
\]
Thus \(f\cdot p\) is strictly inside the actual transverse interval
of T. The upper radial bound in (2) also gives \(n\cdot p<2\).
Avoidance of \(T^\circ\) then forces
\[
                              n\cdot p<1.
\tag{4}
\]
Equality is impossible too: a sufficiently small movement of p in
direction n remains in \(E^\circ\) and enters \(T^\circ\).

The actual two inner terminal vertices are
\[
 V_+=n+(1/2-v)f=(1/c-s/2,c/2),
\]
\[
 V_-=n+(-1/2-v)f=(1/c+s/2,-c/2).
\tag{5}
\]
Equations (3)--(4) imply
\[
 V_{+x}<1<p_x<1/c<V_{-x},\qquad
 0<p_y<\frac{1-c}{s}=\frac{s}{1+c}<s<c/2.
\tag{6}
\]
For \(V_{+x}<1\), use
\((1-c)=s^2/(1+c)<sc/2\), which follows from
\(2v<1+c\). All inequalities are strict on \(0<v<1/4\).

## 2. The exact separating-axis cover leaves only northeast normals

The separating-axis theorem for two closed squares with disjoint
open interiors supplies an actual side normal \(\omega\) of E or T,
oriented from E toward T, such that
\[
                   \max_E\omega\cdot z\le\min_T\omega\cdot z.
\tag{7}
\]
Since \(p\in E^\circ\), its projection is strictly smaller than
the left side.

First \(\omega\cdot n>0\). Otherwise the actual point
\[
                      z=2n+(f\cdot p)f\in T
\]
would satisfy \(\omega\cdot z\le\omega\cdot p\), because
\(2>n\cdot p\). This contradicts (7).

If the global y component of \(\omega\) were nonpositive, its x
component would be positive by \(\omega\cdot n>0\). The differences
in (6) would give
\[
                       \omega\cdot V_+<\omega\cdot p,
\]
again impossible. If its x component were nonpositive, its y
component would be positive and \(V_-\) would give the same
contradiction. Thus
\[
                            \omega_x,\omega_y>0.
\tag{8}
\]
Among the four terminal side normals \(\pm n,\pm f\), only n
satisfies (8). The remaining possibilities are all actual northeast
side axes of E. The next two sections exclude both complete classes.

## 3. The terminal radial axis cannot separate

Let \(M=\max_E x>1\). Represent the arbitrary square orientation
by its own side angle \(\phi\in[0,\pi/2]\). Put
\[
 H_0=(\cos\phi+\sin\phi)/2.
\]
Its center satisfies \(X_0=M-H_0\) and \(Y_0\ge H_0\), because
\(\min_E y\ge0\). Its centered support in direction n is
\[
 H_n=\frac{c\cos\phi+s\sin\phi+
                         |s\cos\phi-c\sin\phi|}{2}.
\]
Therefore
\[
                    \max_E n\cdot z\ge cM+(s-c)H_0+H_n.
\tag{9}
\]
Write \(\zeta=\arctan v\), so \(\cos\zeta=c,\sin\zeta=s\).
The last two terms in (9) are exactly
\[
 \begin{cases}
 s\cos\phi+(s-c)\sin\phi,&0\le\phi\le\zeta,\\
 s\sin\phi,&\zeta\le\phi\le\pi/2.
 \end{cases}
\]
The first decreases to \(s^2\), since \(s<c\); the second is at
least \(s^2\). It follows that
\[
 \max_E n\cdot z\ge cM+s^2>c+s^2
                     =1+c(1-c)>1=\min_T n\cdot z,
\]
contrary to (7). Every physical E orientation is included.

## 4. No actual northeast side axis of E can separate

Write such an axis as \(\omega=(\cos\theta,\sin\theta)\),
\(0<\theta<\pi/2\), and abbreviate its components by C,S.
Since this is an actual E side axis, its own half-support is \(1/2\)
and its horizontal and vertical half-widths are \((C+S)/2\).
The same center inequalities give
\[
                \max_E\omega\cdot z\ge MC+S^2>C+S^2.
\tag{10}
\]

Because \(\omega\cdot n>0\), its minimum on T is on the inner
radial face. For \(\theta\le\zeta\) it is at \(V_+\); for
\(\theta\ge\zeta\) it is at \(V_-\). Subtracting these actual
minimum supports from the right side of (10) gives
\[
 D_+(\theta)=C(1-1/c+s/2)+S^2-cS/2
                    \quad(0\le\theta\le\zeta),
\]
\[
 D_-(\theta)=C(1-1/c-s/2)+S^2+cS/2
                    \quad(\zeta\le\theta\le\pi/2).
\tag{11}
\]
The coefficient \(1-1/c+s/2=1-V_{+x}\) is positive.
Consequently
\[
 D_+'=-(1-1/c+s/2)S+C(2S-c/2)<0,
\]
using \(S\le s\) and \(2s<c/2\), the latter precisely \(v<1/4\).
The other coefficient \(1-1/c-s/2=1-V_{-x}\) is negative, and
\[
 D_-'=-(1-1/c-s/2)S+2SC+cC/2>0.
\]
Thus both complete intervals have their minimum at \(\zeta\), where
\[
                  D_+(\zeta)=D_-(\zeta)=c+s^2-1=c(1-c)>0.
\]
This contradicts (7) for every remaining actual E side axis.

The complete separating-axis cover has been exhausted, proving the
theorem. Reflecting in the vertical axis gives the identical screen
for the corresponding left tilted terminal. The same unchanged E
can therefore be screened against both terminals when their original
physical hypotheses hold simultaneously.

The proof has no orientation grid, sampled configuration, selected
application mean or disk approximation. It preserves every original
side or corner tangency through exact weak separation and the strict
hypothetical interior intersection.
