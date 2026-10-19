# Whole-domain scalar bounds for the low/high frame pair

## Result and dependency boundary

This note replaces all six polynomial rows in Section 8 of
\(\texttt{LOW\_HIGH\_WHOLE\_PAIR\_HAND\_PROOF.md}\), and also the
three inherited rows in
\(\texttt{HIGH\_LOW\_NONALIGNED\_SHORT\_HAND\_PROOF.md}\).
The latter dependency is important: replacing only Section 8 would
leave 31 Bernstein-coefficient comparisons on the shorter
nonaligned interval.

Together with the original whole-pair proof's geometric contact
deformations, derivative bounds, aligned-contact lemmas, and
reflection/reversal argument, this proves the complete L/H entry
\(\mathcal C>.8833\) for both type orders, every sign pair, and
all original separating axes. No sign information is discarded,
and every scalar interval below is closed.

There are no coefficient arrays or subdivisions in these arguments.
Two bounds follow directly from curvature. For the other two
geometric supports, explicit expressions are dominated on their
whole domains by positive quadratics. The displayed expansions
and rational comparisons are part of the proof; a numerical
minimizer, a mesh, or a certificate replay is not a premise.

All terminating decimals are exact rational numbers. Use

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 \mu=.403875,\quad q=1.089065,\quad
 k=.569472,\quad v=.390886,\quad K=k+v=.960358,
\]

\[
 c=\sqrt{Q/2}-1/2,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad
 c_H=\pi/4+(k-v)c,\qquad \gamma=.8833.
\]

The elementary bounds inherited from the circle equation are

\[
\begin{split}
 1.978787507&<R<1.978787508,\\
 .899214065&<c<.899214066,\\
 1.414575670&<a_0<1.414575672,\qquad \pi>3.14159.
\end{split}                                                    \tag{1}
\]

The first three follow by squaring. The cited aligned-contact
proof supplies the elementary Machin-series proof of the fourth.
We write \(S_j,C_j\) for the sine and cosine Taylor sums through
the indicated odd and even degrees.

## 1. The two upper-high / low supports

This is the folded primary-axis regime in Section 5.4 of the
original proof. Its source label is
\(G(z)=\pi/2-H\), with \(G(c)=\pi/4\) and \(G'\ge K\).
For every \(0\le\lambda\le K\), the source support
\(G(z)-\lambda z\) is therefore minimized at \(z=c\).
Enlarging the low target to its full circle gives, exactly,

\[
\begin{split}
 F(x)={}&x+.09+\pi/4+\mu a_0+(\mu+q)/2
       +(.5-c)\lambda\\
       &+(\lambda-.09)\sin x-.09\cos x-RN(x),\\
 N(x)^2={}&\mu^2+q^2+\lambda^2+
                   2\lambda(\mu\sin x-q\cos x).
\end{split}                                                    \tag{2}
\]

### 1.1 The constant multiplier gives a concave support

Take \(\lambda=K\), \(.08\le x\le.11\). The norm in (2)
increases. The endpoint estimate \(N(.11)<.53\), together
with direct rational arithmetic, gives

\[
 N<.53,\qquad(\mu^2+q^2-K^2)^2>.18.
\]

For a rotating circle-support norm
\(N^2=a+b\sin x+d\cos x\), differentiation gives

\[
 N''+\frac N4=\frac{a^2-b^2-d^2}{4N^3}.
\]

Here its numerator is
\((\mu^2+q^2-K^2)^2\). Thus throughout the whole interval,

\[
\begin{split}
 F''
 &<.09+\frac{1.98(.53)}4
              -\frac{1.97(.18)}{4(.53)^3}\\
 &=-\frac{723863781}{2977540000}<-.24.                 \tag{3}
\end{split}
\]

The function is strictly concave, so only its two endpoints
need consideration. The Taylor bounds through sine degree 13
and cosine degree 14, (1), and the squared root bounds

\[
 N(.08)<.498360120,\qquad N(.11)<.526764919
\]

give

\[
 F(.08)>.88348,\qquad F(.11)>.88352.                  \tag{4}
\]

The coefficient of \(\sin x\) in (2) is positive and those
of \(\cos x,c,R\) are negative, so these substitutions have
their stated directions. Equations (3)--(4) prove the first
old row on its complete interval.

### 1.2 The affine multiplier has a positive quadratic lower bound

On \([.11,.46]\), take \(\lambda=1.005-.407x\).
It remains positive and below \(K\), as required in the source
support argument. Define the explicit polynomials

\[
\begin{split}
 T={}&x+.09+3.14159/4+\mu(1.414575670)+(\mu+q)/2-\gamma\\
     &+(.5-.899214066)\lambda
                  +(\lambda-.09)S_7(x)-.09C_8(x),\\
 V={}&\mu^2+q^2+\lambda^2+
                  2\lambda\{\mu S_9(x)-qC_{10}(x)\},\\
 P={}&T^2-QV.
\end{split}                                                    \tag{5}
\]

Alternating Taylor inequalities and (1) give
\(F-\gamma>T-RN\) and \(N^2\le V\).
Also \(T>0\): discard its nonnegative sine term, replace
\(-.09C_8\) by \(-.09\), put \(x=.11\) in the remaining
positive \(x\) term, and bound the negative multiplier term
using \(\lambda\le K\). The resulting constant is positive.
Therefore \(P>0\) is sufficient.

Put \(w=x-.135\), so \(-.025\le w\le.325\).
Expanding the factored expression (5), then grouping by powers
of \(w\), gives on this entire interval

\[
 P(x)>.000346-.001352|w|+.238w^2.                     \tag{6}
\]

The following details make this single domination readily
checkable without a coefficient test. The constant term of
\(P(.135+w)\) exceeds \(.000346\), its linear coefficient
has absolute value less than \(.001352\), and its quadratic
coefficient exceeds \(.2608\). In the terms of degree at least
three, the cubic and fifth-degree coefficients are positive
and less than \(.414,.208\), respectively. Their possible
negative contributions are at least

\[
 -\{.414(.025)+.208(.025)^3\}w^2.
\]

The negative coefficients of degrees \(4,6,7,10,11\) have
absolute values below \(.111,.028,.029,.0005,.000065\).
The positive even terms can be discarded. The remaining odd
and higher even terms together have magnitude less than
\(.000001w^2\) on the stated interval, whenever they are
negative. Each claim is obtained by direct multiplication
of the two explicitly displayed factors in (5).
Hence the coefficient multiplying \(w^2\) after this domination
is greater than

\[
\begin{split}
 .2608&-.414(.025)-.111(.325)^2-.208(.025)^3\\
 &-.028(.325)^4-.029(.325)^5
       -.0005(.325)^8-.000065(.325)^9-.000001\\
 &=\frac{12493980846514624151}{52428800000000000000}
 >.238,
\end{split}
\]

which proves (6). Completing the square now gives the uniform
strict bound

\[
 P(x)>.000346-\frac{.001352^2}{4(.238)}
     =\frac{5118189}{14875000000}>0.                   \tag{7}
\]

This handles the complete second old row, including both weak
endpoints, by one positive quadratic.

## 2. The low-negative / high-negative support is concave

The source axial minimum with multiplier \(\lambda=1\) was
proved geometrically in Section 7.1 of the whole-pair proof.
Its full-circle target support, on \([.3,.8]\), is

\[
\begin{split}
 F(x)&=x+.09+\tfrac12+c_H+(k-v)/2
                   +.91(\sin x+\cos x)-RN(x),\\
 N(x)^2&=k^2+v^2+1+2(k\sin x-v\cos x).
\end{split}                                                    \tag{8}
\]

The norm increases. Direct endpoint squaring gives
\(N(.8)<4/3\). The same rotating-norm identity, with its
nonnegative numerator, gives

\[
 F''\le-.91(\sin x+\cos x)+RN/4
       <-.91+\frac{1.98(4/3)}4<0.                     \tag{9}
\]

For the two endpoints, use \(c_H>.9459\),
\(N(.3)<1.04\),
\(\sin(.3)+\cos(.3)>1.25\), and
\(\sin(.8)+\cos(.8)>1.4\).
Then direct substitution gives

\[
\begin{split}
 F(.3)&>.3+.09+.5+.9459+.089293+.91(1.25)-1.98(1.04)
       =1.003493,\\
 F(.8)&>.8+.09+.5+.9459+.089293+.91(1.4)-1.98(4/3)
       =1.059193.
\end{split}                                                    \tag{10}
\]

All these endpoint bounds follow from (1), alternating Taylor
sums, and squaring. Concavity proves \(F>\gamma\) on the whole
interval. This removes the third old row.

## 3. One nonaligned argument on the entire interval

The remaining geometric support is high-positive to
low-positive on the original source \(+f\) axis. In this
section use the single interval

\[
 .08\le x\le.77,\qquad
 \lambda=.990906-.28x,\qquad w=x-.19.
\]

In particular \(-.11\le w\le.58\) and \(0<\lambda<1\).
The exact full-circle support formula is

\[
\begin{split}
 F(x)={}&x-.09\cos x+(\lambda-.09)\sin x+\lambda
          +c_H+\mu a_0\\
        &+(k-v+\mu+q+.18)/2-R(n_1+n_2),\\
 n_1^2={}&k^2+(\lambda-v)^2,\\
 n_2^2={}&\mu^2+q^2+\lambda^2+
                     2\lambda(\mu\sin x-q\cos x).
\end{split}                                                    \tag{11}
\]

This is the support derived by subtracting \(\lambda\) times
the actual separating margin, with both state arcs enlarged
to their full circles. No assumption about the locations of
their minimizing points is needed.

We give two simple, explicit quartic upper bounds:

\[
\begin{split}
 U_1(w)&=.789504-.193932w+.025833w^2
                         +.006347w^3+.001136w^4,\\
 U_2(w)&=.604838+.959440w-.205088w^2
                         -.061072w^3+.044940w^4.
\end{split}                                                    \tag{12}
\]

Their validity is established below on the whole interval by
monotonicity and positive quadratics. They are candidate scalar
functions, not entries in a lookup table.

Let \(S=S_9(x)\), \(C=C_8(x)\), \(e=.00000003\), and set

\[
 X_1=k^2+(\lambda-v)^2,\qquad
 X_2=\mu^2+q^2+\lambda^2+2\lambda(\mu S-qC).
\]

Since \(.77^{10}/10!<e\) and \(.77^{11}/11!<e\),
the alternating remainders give

\[
 S-e<\sin x<S,\quad C-e<\cos x<C,\quad
 n_1^2=X_1,\quad |n_2^2-X_2|<3e.                     \tag{13}
\]

The last inequality uses \(0<\lambda<1\) and \(\mu+q<3/2\).

### 3.1 The first squared norm bound decreases to a positive endpoint

Put \(A(w)=U_1(w)^2-X_1(w)\). We prove that \(A\) decreases
throughout \([-.11,.58]\).

For \(w=-y\in[-.11,0]\), expansion of the quartic square gives

\[
 A'(w)<-.00000097+.00000682y^2+.000002704y^3
                         +.000101y^6<0.              \tag{14}
\]

The second inequality follows by putting \(y=.11\) in the
positive terms. For \(0\le w\le.58\), grouping the four highest
terms of the derivative gives

\[
\begin{split}
 A'(w)<{}&-.00000097+.000000269w+.00000682w^2\\
 &+w^4\{-.000563+.000594w+.000101w^2+.0000104w^3\}.
\end{split}                                                    \tag{15}
\]

The braces are less than \(-.00018\), by putting \(w=.58\)
in their positive terms. Complete the square in \(w^2\):

\[
\begin{split}
 A'(w)&<-.00000097+.000000269(.58)
                     +.00000682w^2-.00018w^4\\
 &\le-.00000097+.000000269(.58)
                     +\frac{.00000682^2}{4(.00018)}
 <0.
\end{split}                                                    \tag{16}
\]

For clarity, (14)--(15) follow by expanding \(U_1^2-X_1\)
with the six-decimal coefficients in (12). Terms omitted
from the right sides have nonpositive sign on the indicated
half interval. Thus these estimates prove monotonicity
everywhere, rather than testing it at intermediate angles.

Finally direct substitution in the polynomial gives
\(A(.58)>.00000264\). Therefore \(A>0\) throughout.
Also \(U_1>.67\), immediately from (12) and
\(-.11\le w\le.58\). Consequently

\[
 n_1<U_1.                                             \tag{17}
\]

### 3.2 The second squared norm bound is a sum of positive quadratics

Put

\[
 B(w)=U_2(w)^2-X_2(w)-3e.
\]

For \(w=-y\), \(0\le y\le.11\), direct expansion and grouping
the cubic and fifth-degree terms give

\[
\begin{split}
 B(-y)>{}&.00000120-.00000445y-.00000565y^2\\
         &+y^3(.001067-.078698y^2)-.01448y^6.
\end{split}                                                    \tag{18}
\]

The cubic braces are positive because
\(.001067>.078698(.11)^2\).
All omitted terms are positive. Dropping those braces and
putting \(y=.11\) in the three negative terms gives

\[
 B(-y)>
 .00000120-.00000445(.11)-.00000565(.11)^2
                       -.01448(.11)^6>.00000061.     \tag{19}
\]

For \(0\le w\le.58\), the terms of degrees five and above
are bounded below by \(.0685w^5\), after discarding their
positive even terms. Explicitly,

\[
 .07869-.01448w-.004493w^2-.00001615w^4
 \ge .07869-.01448(.58)-.004493(.58)^2
                     -.00001615(.58)^4>.0685.
\]

The remaining terms therefore give, with \(t=w^2\),

\[
\begin{split}
 B(w)>{}&.00000120-.00000565t+.000630t^2\\
        &+w\{.00000444-.001068t+.0685t^2\}.             \tag{20}
\end{split}
\]

Both quadratic expressions in \(t\) are positive for every
real \(t\), by completing the square:

\[
\begin{split}
 .00000120-\frac{.00000565^2}{4(.000630)}
       &>.00000118,\\
 .00000444-\frac{.001068^2}{4(.0685)}
       &>.00000027.
\end{split}
\]

This proves \(B>0\) also on the positive half interval.
The positive sign of \(U_2\) follows directly from (12).
For \(w\le0\), discard its positive cubic and quartic terms
and put \(|w|=.11\) in the remaining negative terms to obtain
\(U_2>.49\). For \(w\ge0\),

\[
 U_2\ge .604838+w\{.959440-.205088(.58)
                                  -.061072(.58)^2\}>.60.
\]

It follows from (13) and \(B>0\) that

\[
 n_2<U_2.                                             \tag{21}
\]

Thus (17) and (21) supply the two root bounds on the entire
interval without either of the inherited norm certificate lists.

### 3.3 The whole support has one positive quadratic lower bound

Using (1), (13), (17), and (21) in (11), define

\[
\begin{split}
 V_0(w)={}&x-.09C+(\lambda-.09)(S-e)+\lambda
             +3.14159/4\\
          &+(k-v)(.899214)+\mu(1.414575)
                +(k-v+\mu+q+.18)/2\\
          &-1.978788(U_1+U_2)-.8833.
\end{split}                                                    \tag{22}
\]

Every substitution has the correct direction:
\(\lambda-.09,k-v,\mu,U_1,U_2\) are positive, while
the coefficients of \(C,R\) in the original support are
negative. Thus \(F-.8833>V_0\).

Expansion of the explicit expression (22), followed by the
triangle inequality for its odd powers, gives

\[
\begin{split}
 V_0(w)>{}&.000074-.00179|w|+.04388w^2\\
 &-.006846|w|^3-.04236w^4-.004876|w|^5-.002391w^6\\
 &-.0000952|w|^7-.000001017|w|^9-.000000772w^{10}.
\end{split}                                                    \tag{23}
\]

This domination involves only the displayed Taylor sums and
the two quartics, so it is verified by direct multiplication.
The sole term omitted by sign is the positive eighth-degree
term. The constant term exceeds \(.000074\), the absolute
linear coefficient is less than \(.00179\), and the quadratic
coefficient exceeds \(.04388\).

For \(u=|w|\le.58\), the coefficient of \(w^2\) remaining
after the negative higher powers in (23) is greater than

\[
\begin{split}
 .04388
 &-.006846(.58)-.04236(.58)^2-.004876(.58)^3\\
 &-.002391(.58)^4-.0000952(.58)^5
      -.000001017(.58)^7-.000000772(.58)^8>.024.
\end{split}
\]

Consequently the entire interval satisfies

\[
\begin{split}
 F(x)-.8833
 &>V_0(w)>.000074-.00179|w|+.024w^2\\
 &\ge .000074-\frac{.00179^2}{4(.024)}
      =\frac{38999}{960000000}>0.                    \tag{24}
\end{split}
\]

This single proof covers \([.08,.77]\), including the previously
separate short interval and its extension. The three polynomial
rows in the inherited short proof and the three extension rows
are all unnecessary.

## 4. What has been discharged

Equations (3)--(7) replace the two upper-high / low rows.
Equations (8)--(10) replace the low-negative / high-negative
row. Equations (11)--(24) replace the three nonaligned extension
rows and all three inherited short-interval rows. These are all
the scalar coefficient premises in the complete L/H pair proof.

The proofs just given act on exactly the support functions
already derived from the original signed separating axes.
The continuous contact reductions, the parallel and quarter
contact strips, and the reflection/reversal cover in that proof
therefore retain their full strength. In particular the
inequality is strict even when a separating margin is zero,
at a type cut endpoint, or at an endpoint of a scalar interval.

This note establishes the complete L/H pair entry. The full
frame-concentration theorem additionally needs the other
four-type pair entries and their cyclic use; no claim about
the remaining cycle gates is made here.
