# The same-sign outer zero edges of 0011011 without curvature tables

This note completes the entire same-sign outer/outer zero-quarter component
of the 0011011 word argument without the two stationary-curve rows and six
angle intervals in `../WRONG_0011011_SAME_OUTER_ZERO_HAND_PROOF.md`.
It proves the same strict pair bound
\[
 C>.89777>.89765.
\]
The whole-word exclusion still requires its other pair components. In
particular this note does not assert that G2 is closed.

All decimals below are exact terminating rationals. The only polynomial
positivity argument is for one explicit degree-eight polynomial on its
whole domain; no subdivision or numerical minimum is used.

## 1. The existing geometric reductions

Put
\[
 Q=9789/2500,\quad d=\sqrt{Q/2}-1/2,\quad
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad a_0=a(0).
\]
The two representative label pairs are
\[
\begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055a(b)b,\\
 J(b)&=-.00026a(b)+.83194b-.11864b^2+.17627a(b)b,\\
 L(b)&=.03965+3.85510b-1.49748b^2-1.89442a(b)b,\\
 K(b)&=-.02112a(b)+.29090b+.44642a(b)b.
\end{aligned}
\]
The corrected cost is \(C=\phi+F(b)-G(B)\), with
\((F,G)=(P,J)\) or \((L,K)\). Both are the original role labels, so
reflected reversal preserves their contribution to the cyclic telescope.

The physical gap and all four original axes are retained. Sections 1--6
of the cited note give the following analytic reductions. Negative angles
are infeasible. Three axes have direct strict reserves. The remaining
source-secondary contact is
\[
 b=\tfrac12+(B+\tfrac12)\cos\phi
                   -(a(B)-\tfrac12)\sin\phi.                 \tag{1}
\]
Its only boundary types are \(B=0\), \(b=d\), and \(\phi=.7\).
The \(L,K\) row has no interior minimum and reduces to \(B=0\), where
its whole-interval strong-convexity argument gives \(C>.89777\).
Those arguments use explicit derivative implications and endpoint
comparisons, not the curvature rows replaced here.

It remains to exclude an interior minimum of the \(P,J\) row and to
handle its three contact boundaries. We give uniform arguments for the
stationary curve and the diagonal boundary, and also replace the two
angle estimates on its target-zero boundary by one circle estimate.

## 2. A decreasing critical-curve curvature

Write \(p=P'\), and set
\[
 E(b)=P''(b)-(b-1/2)p(b)^3.
\]
A critical point of the two-variable contact cost must have \(b>.6\).
Indeed its angular stationarity is \(p(b)v=1\), whereas for \(b\le.6\)
\[
 p(b)v\le p(.6)
 \left(\sqrt{Q-(.1-\sin(.7))^2}-\cos(.7)\right)<1.
\]
The contact-speed formula and monotonicity giving this inequality are
(13)--(16) of the cited note.

Here is a whole-interval proof that \(E\) decreases. Put
\(v_b=b+1/2\), \(u_b=\sqrt{Q-v_b^2}\). Direct differentiation gives
\[
 P'''(b)=\frac{3Q(.11055)(Q-v_b/2)}{u_b^5},
\]
\[
 P'''''(b)=\frac{3Q(.11055)}{u_b^9}
 \left(5Q^2-\frac{15}{2}Qv_b+30Qv_b^2-10v_b^3\right)>0.       \tag{2}
\]
For the sign, group the numerator as
\(5Q(Q-3v_b/2)+10v_b^2(3Q-v_b)\); both terms are positive for
\(Q>3.9\) and \(v_b<1.4\). Thus \(P'''\) is convex.
Its two endpoint values give the upper chord
\[
 P'''(.6+x)<.364+1.4x\qquad(0\le x\le d-.6<.3).
\]
Also \(P''>.253\) and \(p(.6)>.876\), hence
\(p(.6+x)>.876+.253x\). Therefore
\[
\begin{aligned}
 E'(.6+x)
 &=P'''-p^3-3(.1+x)p^2P''\\
 &<.364+1.4x-.876^3
       -3(.876)^2(.253)x-3(.1+x)(.876)^2(.253)\\
 &<-.29.                                                     \tag{3}
\end{aligned}
\]
The last line follows on the whole interval from \(0\le x<.3\).
In particular the exact endpoint comparisons imply
\[
                 .043<E(b)<.187\qquad(.6\le b\le d).          \tag{4}
\]

At a critical point, define the target corner coordinates by
\[
 q(b)=(b-1/2)^2+1/p(b)^2,\quad
 U(b)=\frac{Q+1-q(b)}2,\quad V(b)=\sqrt{Q-U(b)^2},\quad
 r(b)=V(b)/U(b).
\]
They follow directly by eliminating the contact angle from angular
stationarity. Since \(q'=-2E/p^3<0\), \(U\) increases and \(V\)
decreases. Exact endpoint comparisons give
\[
 1.8<U<1.852,\qquad .2<B=V-1/2<.32,\qquad r(.6)>.454.          \tag{5}
\]
Moreover
\[
 r'=-\frac{QE}{U^2Vp^3}>-.46.                                 \tag{6}
\]
To verify the single uniform bound, \(U^2\sqrt{Q-U^2}\) decreases
on this interval, since \(2Q-3U^2<0\). Also
\(\sqrt{Q-1.852^2}>.6968\). Thus
\[
 \frac{QE}{U^2Vp^3}
 <\frac{Q(.187)}{1.852^2(.6968)(.876)^3}<.46.
\]
Equations (5)--(6) and the lower tangent for \(p\) yield
\[
 rp^3>(.454-.46x)(.876+.253x)^3>.2725.                         \tag{7}
\]
The polynomial in the middle decreases for \(0\le x\le.3\): its
first derivative has the sign of
\(3(.253)(.454)-(.46)(.876)-4(.46)(.253)x<0\).
Its value at \(x=.3\) exceeds \(.2725\).

## 3. One negative Hessian determinant on the entire critical curve

In the local \((b,B)\) contact coordinates, the Hessian entries at a
critical point are
\[
 C_{bb}=E(b),\qquad C_{bB}=r(b)p(b)^3,
 \qquad C_{BB}=\phi_{BB}-J''(B).
\]
We record the uniform bound on the last entry to make the replacement
self-contained. Put \(z=b-1/2\), \(q=Q+1-2U\), and
\[
 f_1(U)=\frac{Q-U}{Uq},\qquad
 f_1'(U)=\frac{4QU-2U^2-Q(Q+1)}{U^2q^2}.
\]
The exact contact derivative is
\[
 \phi_{BB}=-r f_1'(U)+\frac{z}{q\sqrt{q-z^2}}
 \left(\frac Q{U^3}-\frac{2r^2}{q}
                         -\frac{r^2}{q-z^2}\right).           \tag{8}
\]
Let \(q_-=Q+1-2(1.852)\), \(q_+=Q+1-2(1.8)\), and
\[
 A_- =\frac{4Q(1.8)-2(1.8)^2-Q(Q+1)}{(1.8q_+)^2},\qquad
 B_+ =\frac Q{1.8^3}-\frac{3(.378)^2}{q_+}>0.
\]
The numerator of \(f_1'\) increases with \(U\), while \(Uq\)
decreases. Using \(r>.378\), \(0<z<.4\) in (8) therefore gives
\[
 \phi_{BB}<-.378A_-+
     \frac{.4B_+}{q_-\sqrt{q_--.16}}<-.05.
\]
Since \(J''(B)>J''(.32)>-.436\), it follows that \(C_{BB}<.386\).
If \(C_{BB}\le0\), the Hessian already cannot be positive semidefinite.
If \(C_{BB}>0\), (4) and (7) give, everywhere on the critical curve,
\[
 \det D^2C<(.187)(.386)-(.2725)^2<0.                           \tag{9}
\]
This replaces both former Hessian rows. No interior critical point can
be a minimum.

## 4. The entire source-diagonal boundary

Set \(z_0=d-1/2\), and parameterize \(b=d\) by
\[
 Z=z_0-\sin\phi,\quad Y=\sqrt{Q-Z^2},\quad
 U=Y\cos\phi-Z\sin\phi,\quad
 V=Y\sin\phi+Z\cos\phi,\quad B=V-1/2.
\]
The physical branch begins at \(B=0\), \(\phi=\phi_a>.10726\),
and ends at \(\phi=.7\). With \(f=1-\cos\phi/Y\),
\(U'=-Vf\) and \(B'=Uf>0\). Thus \(U\) decreases. Its endpoint
values, and the explicit bound for \(Z\), give
\[
            1.65<U<1.915,\qquad Y>1.95,\qquad B'>.8.          \tag{10}
\]
We prove one curvature inequality on this whole branch:
\[
                         \frac{B''}{(B')^2}<\frac14.          \tag{11}
\]
Regard \(\phi\) as a function of \(B\). Formula (8) still applies,
now with the constant \(z=z_0\), \(q=Q+1-2U\), and \(r=V/U\).
Furthermore
\[
 \phi_B=f_1(U)+\frac{z_0V}{Uq\sqrt{q-z_0^2}}>f_1(U)>0.
\]
The brace in (8) is positive on (10). Since \(z_0^2<.16\), it
suffices, after multiplication by positive denominators, to prove
\[
 R(U)=Qq(q-.16)-U(Q-U^2)(3q-.32)>0.
\]
For \(y=U-1.65\), direct expansion is the short identity
\[
 R(1.65+y)=.296662332816+7.00800948y
                  +y^2(12.55866-25.1732y-6y^2).
\]
Here \(0<y<.265\), and the last parenthesis exceeds
\(12.55-25.18(.265)-6(.265)^2>0\). Hence
\(\phi_{BB}\ge-rf_1'(U)\).

It remains to bound \(rf_1'/f_1<1/4\). The numerator
\(N=4QU-2U^2-Q(Q+1)\) is positive on (10), so this is equivalent
to positivity of the explicit polynomial
\[
 \mathcal P(U)=U^4q^2(Q-U)^2-16(Q-U^2)N^2.                     \tag{12}
\]
Here is a whole-domain proof of that sign. Write \(U=37/20+x\),
so \(|x|\le1/5\). Expanding (12), with the displayed exact value of
\(Q\), gives
\[
 \mathcal P(37/20+x)
 >8-39|x|+x^2\left(2407-4605|x|-975x^2
                         -371|x|^3-9|x|^5\right).             \tag{13}
\]
For transparency, the constant, linear, and quadratic coefficients of
the exact expansion are respectively greater than \(8\), of absolute
value less than \(39\), and greater than \(2407\). Its cubic
coefficient lies in \((0,4605)\); its fourth and fifth coefficients
lie in \((-975,0)\) and \((-371,0)\). Its sixth coefficient is
positive, its seventh lies in \((0,9)\), and its eighth is \(4\).
These are direct rational comparisons of the one polynomial (12),
not evaluations on pieces of its domain.

The parenthesis in (13) is greater than
\[
 2407-4605/5-975/25-371/125-9/3125>1444.
\]
Completing a square proves
\[
 \mathcal P(U)>8-39|x|+1444x^2
             \ge8-39^2/(4\cdot1444)>7>0.
\]
Consequently
\[
 \frac{B''}{(B')^2}=-\frac{\phi_{BB}}{\phi_B}
 \le\frac{rf_1'}{f_1}<\frac14,
\]
which proves (11), including points where \(B''\le0\).

For \(H_d(\phi)=\phi+P(d)-J(B(\phi))\), the original whole-arc
label bounds are \(J''<-.329\), \(0<J'<1.082\). Hence
\[
 H_d''=(B')^2\left(-J''-J'\frac{B''}{(B')^2}\right)
 >(.8)^2\left(.329-\frac{1.082}{4}\right)>\frac1{30}.          \tag{14}
\]
At the single rational reference angle \(.18909\),
\[
 H_d(.18909)>.89777605,\qquad |H_d'(.18909)|<10^{-6}.
\]
The reference is on the branch. Integrating (14) and completing a
square gives on its entire interval
\[
 H_d>.89777605-15\cdot10^{-12}>.89777.                          \tag{15}
\]
This replaces all six former angle-curvature intervals.

## 5. The target-zero boundary by one circle estimate

On \(B=0\), write \(b=b_0(\phi)\) as in (1),
\(v_0=-b_0'>0\), and \(q_0=Q-2a_0\). Exactly,
\[
                    v_0^2+(b-1/2)^2=q_0<1.087.
\]
Convexity of \(P'\) and its two endpoint values give the upper chord
\(P'(b)<.774+.223b=.8855+.223(b-1/2)\) for \(0\le b\le d\).
Put \(z=b-1/2\). If \(z\le0\), then
\(P'(b)v_0<.886(1.043)<1\). If \(z\ge0\), the circle tangent
\[
 \sqrt{q_0-z^2}\le\sqrt{q_0}-\frac{z^2}{2\sqrt{q_0}}
\]
gives, on dropping its negative cubic term and completing a square,
\[
 P'(b)v_0
 <.886\sqrt{q_0}+
       \frac{(.223)^2q_0^{3/2}}{2(.886)}
 <.886(1.043)+\frac{(.223)^2(1.087)(1.043)}{2(.886)}<1.
\]
Thus \(\phi+P(b_0(\phi))-J(0)\) increases over its whole physical
interval. Its first point has \(b_0=d\), \(\phi_a>.10726\), so
its cost is \(>.10726+P(d)-J(0)>.8985\).

The third boundary, \(\phi=.7\), retains the direct positive-curvature
identity in Section 11 of the cited note:
\[
 \frac{d^2}{dB^2}\{.7+P(b(B,.7))-J(B)\}>.329.
\]
Its single reference at \(B=.34621\) gives a cost greater than
\(.89778867\) on the entire connected boundary interval.

## 6. Coverage and arithmetic

Sections 2--3 exclude every possible interior minimum of the remaining
contact surface. Sections 4--5 cover its three boundaries. Together
with the analytic reductions in Section 1, this proves both representative
rows, all four original separating axes, both physical angle signs, and
their reflected reversals. Thus all sixteen same-sign outer/outer
zero-quarter branches of 0011011 have the strict reserve asserted at
the beginning.

The point comparisons use only the displayed rational inputs, squaring
positive radical bounds, and alternating sine/cosine Taylor inequalities.
They do not depend on the old companion's PASS result. The polynomial
(12) is derived and bounded on one whole interval; the former two
critical-curve rows and six angle-curvature rows are not premises.
No Lean source or generated certificate has been changed or run.
