# Whole-interval curvature for the core/high and high/high frame costs

## Result and dependency boundary

This note replaces the sole remaining Bernstein-polynomial argument in each
of `../CORE_HIGH_WHOLE_PAIR_HAND_PROOF.md` and
`../HIGH_HIGH_WHOLE_PAIR_HAND_PROOF.md`, as well as the former two-interval
corner-tail estimate in the first note. The original geometric support,
sign, and axis arguments remain in force. Consequently their complete
core/high and high/high pair inequalities follow without either polynomial
coefficient list:

\[
\mathcal C>\frac{8833}{10000}\quad(C/H),\qquad
\mathcal C>\frac{9099}{10000}\quad(H/H).
\]

Both arguments below apply on their entire intervals by curvature. Neither
subdivides an angle interval or introduces a positivity lookup. The first
avoids the old degree-eighteen polynomial altogether; the second avoids
both squaring a radical inequality and the old degree-fourteen polynomial.

The complete frame-concentration gate also requires the other four-type
pair entries. They are not assumed proved by this note. All terminating
decimals below are exact rational numbers.

## 1. Two elementary curvature principles

If a twice differentiable function satisfies \(f''\le M\) on \([a,b]\),
subtract \(Mx^2/2\) and use concavity. If \(\ell\) is the line through
the endpoint values of \(f\), this gives

\[
 f(x)\ge\ell(x)-\frac M2(x-a)(b-x)
 \ge\min(f(a),f(b))-\frac M8(b-a)^2.                 \tag{1}
\]

Similarly, \(f''\ge m>0\) gives, at any \(x_0\) in the interval,

\[
 f(x)\ge f(x_0)+f'(x_0)(x-x_0)+\frac m2(x-x_0)^2
 \ge f(x_0)-\frac{f'(x_0)^2}{2m}.                    \tag{2}
\]

These are whole-interval consequences of curvature, not local Taylor
approximations with an unstated remainder.

## 2. Core/high: replace Section 5.2 of the inherited pair proof

Use exactly that proof's constants

\[
 g=1.077372,\quad u=.569472,\quad v=.390886,
 \quad R_+=1.978788,
\]

\[
 k_+=\frac{355}{452}+(u-v)(.899215),\qquad
 \gamma=.8833,
\]

and set

\[
\begin{aligned}
 B_0&=.09-k_++(-u+v+g)/2-\gamma+.914R_+,\\
 B_2&=.09+.35R_+=.7825758,\\
 C_0&=g-1.204902R_+,\qquad A=13g/12=1.167153.
\end{aligned}                                                       \tag{3}
\]

In particular \(B_0>0\). The circle-norm bound already derived by
differentiation in the inherited Section 5.2 is

\[
 n(s)=\sqrt{(g-us)^2+v^2s^2}
 <1.204902-.914s+.35s^2.                              \tag{4}
\]

It follows from \(n(1)<.640902\), \(n'(1)>-.214\), and
\(0<n''<.7\); no polynomial coefficient test enters (4).

For the original support expression \(H(x)\) in equation (22) of that
proof, multiply \(H(x)-\gamma\) by \(s=\sin x>0\) and use (4),
\(R<R_+\), and \(k<k_+\). This gives directly

\[
 s(H(x)-\gamma)>F(x),                                \tag{5}
\]

where, on the entire interval \(3/4\le x\le3/2\),

\[
 F(x)=(x+B_0)\sin x-B_2\sin^2x-.09\sin x\cos x
              +C_0+A\cos x.                         \tag{6}
\]

There is no need to replace the sines in (6) by a degree-eighteen
polynomial. We prove \(F>0\) by one curvature bound.

### 2.1. Concavity of the second derivative

Using double-angle identities, differentiation of (6) gives

\[
\begin{aligned}
 F''(x)&=(2-A)\cos x-(x+B_0)\sin x
                       -2B_2\cos2x+.18\sin2x,\\
 F'''(x)&=-(3-A)\sin x-(x+B_0)\cos x
                       +4B_2\sin2x+.36\cos2x,\\
 F^{(4)}(x)&=-(4-A)\cos x+(x+B_0)\sin x
                       +8B_2\cos2x-.72\sin2x,\\
 F^{(5)}(x)&=(5-A)\sin x+(x+B_0)\cos x
                       -16B_2\sin2x-1.44\cos2x,\\
 F^{(6)}(x)&=(6-A)\cos x-(x+B_0)\sin x
                       -32B_2\cos2x+2.88\sin2x.
\end{aligned}                                                       \tag{7}
\]

The last two double-angle terms are at most their amplitude. Direct
squaring gives

\[
 \sqrt{(32B_2)^2+2.88^2}<25.21.
\]

Also \(\cos x\le\cos(3/4)<.733\), while
\((x+B_0)\sin x>0\). Thus (7) implies the single bound

\[
 F^{(6)}(x)<(6-A)(.733)+25.21<29.                    \tag{8}
\]

At the expansion point \(x_0=9/8\), the explicit formulas give

\[
 F^{(4)}(9/8)<-4.23,\qquad |F^{(5)}(9/8)|<4.68.       \tag{9}
\]

Taylor's inequality with (8), valid on both sides of \(x_0\), now gives,
since \(|x-9/8|\le3/8\),

\[
\begin{aligned}
 F^{(4)}(x)
 &<-4.23+4.68|x-9/8|+\frac{29}{2}(x-9/8)^2\\
 &\le-4.23+4.68\frac38+\frac{29}{2}\left(\frac38\right)^2
 =-\frac{279}{640}<0.                                \tag{10}
\end{aligned}
\]

Therefore \(F''\) is concave throughout the original interval.

### 2.2. A global upper curvature bound and the endpoint chord

At \(x_1=13/12\), the first two formulas in (7) give

\[
 F''(13/12)<.003,\qquad |F'''(13/12)|<.02.             \tag{11}
\]

The tangent line to a differentiable concave function lies above it.
Use (10) for the concavity of \(F''\), and
\(|x-13/12|\le5/12\), to obtain

\[
 F''(x)\le F''(13/12)+F'''(13/12)(x-13/12)
 <.003+.02\frac5{12}<\frac3{250}.                    \tag{12}
\]

The endpoint values of the explicit expression (6) satisfy

\[
 F(3/4)>\frac3{1000},\qquad F(3/2)>\frac3{1000}.       \tag{13}
\]

Apply (1) with \(M=3/250\). It proves on the complete interval that

\[
 F(x)>\frac3{1000}-\frac{3/250}{8}\left(\frac34\right)^2
       =\frac{69}{32000}>0.                          \tag{14}
\]

Together with (5), this proves the inherited Section 5.2's entire
support bound, with a visible uniform reserve. Its Sections 2--5.1 and
5.3 use circle supports, monotonicity, and concavity. Replace the final
two-interval estimate of Section 5.4 by the following single argument.

### 2.3. One monotone bound for the positive core corner

The inherited geometric reduction leaves only \(2.28\le x\le2.5\)
and gives the necessary inequality
\(a\ge\tfrac12+\sin x+\cos x/12\) for the high source.
Set

\[
 z=\sin x+\frac{\cos x}{12},\quad
 D=-\cos x+\frac{\sin x}{12}
   =\sqrt{\frac{145}{144}-z^2},\quad
 K=1+z,\quad Y=\sqrt{Q-K^2}.
\]

Here \(z'=-D\), \(.53<z<.71\), and all radicals are positive.
The corner inequality and containing circle imply
\(a\ge K-1/2\), \(b\le Y-1/2\). The adverse labels satisfy
\(L_C<.786\), \(.18h<.0378\), and
\(L_H=k-ua+vb\), where \(k<.946\). Hence the original pair cost
is bounded below by

\[
 J(x)=x-.8238-k+u(K-\tfrac12)-v(Y-\tfrac12).
\]

Differentiation gives
\(J'=1-uD-vDK/Y\). To bound its last term uniformly, regard
\(G(z)=DK/Y\) as a function of \(z\). Its derivative has positive
denominator \(DY^3\) and numerator

\[
 Q\left(\frac{145}{144}-z^2\right)
       -zK(Q-K^2)
 >Q\left(\frac{145}{144}-.71^2\right)
       -.71(1.71)(Q-1.53^2)
 =\frac{17128331}{300000000}>0.
\]

Thus \(G(z)<G(.71)<1.23\); the last squared comparison has
positive difference \(2967291/100000000\). Similarly \(D<.86\),
since \(.86^2-(145/144-.53^2)=61/4500\). Therefore

\[
 J'>1-.57(.86)-.391(1.23)=\frac{2887}{100000}>0.
\]

At the single left endpoint, the alternating sine and cosine sums give
\(K-1/2>1.2\), and then \(Y-1/2<.514\) by squaring. Consequently

\[
 J(2.28)>2.28-.8238-.946+.569(1.2)-.391(.514)
         =.992026>.8833.
\]

This covers the whole corner tail without the two old angle cells.
All closed angle endpoints, core joins, signs, and axes in the inherited
geometric reduction remain included. The full \(C/H\) scalar
replacement is now complete.

## 3. High/high: replace Section 6 of the inherited pair proof

Use the inherited folded coordinates and exact endpoint

\[
 \mathcal R=\sqrt{2Q},\quad
 (a_1+1)^2+b_1^2=2Q,\quad b_1=\frac25a_1,
 \quad Q=\frac{9789}{2500}.
\]

Put

\[
 u=.089293,\quad v=.480179,\quad
 \lambda(x)=.734-.4x,
 \quad A=1+a_1-b_1,\quad B=1-a_1-b_1.                \tag{15}
\]

Here \(A>0>B\). On the complete remaining interval
\(3/5\le x\le19/20\), \(.354\le\lambda\le.494\).
The original source-circle and target-endpoint support gives

\[
\begin{aligned}
 F(x)={}&x+.09+2\lambda+u(1+a_1)+vb_1\\
 &+(\lambda A-.09)\cos x+(\lambda B-.09)\sin x
   -\mathcal R N(x),\\
 N(x)&=\sqrt{(u+\lambda)^2+(v-\lambda)^2}.             \tag{16}
\end{aligned}
\]

We retain the actual radical rather than squaring a Taylor-polynomial
lower bound. The desired conclusion is \(F>.9099\).

### 3.1. The second derivative is concave

Set

\[
 \Delta=.16(u+v)^2>0,\qquad
 T=.4(v-u-2\lambda).
\]

For the affine vector \(r=(u+\lambda,v-\lambda)\), one has
\(N=|r|\), \(T=r\cdot r'\), and
\(\Delta=|r|^2|r'|^2-(r\cdot r')^2\). Differentiation gives the
exact identities

\[
 N'=T/N,\qquad N''=\Delta/N^3,\qquad
 N^{(4)}=\frac{3\Delta(4T^2-\Delta)}{N^7}.           \tag{17}
\]

All denominators are positive. Moreover

\[
 4\lambda+u-3v\ge4(.354)+.089293-3(.480179)
                 =.064756>0.                       \tag{18}
\]

Thus \(2(2\lambda+u-v)>u+v>0\). Squaring this strictly positive
comparison shows \(4T^2>\Delta\), so \(N^{(4)}>0\).

The fourth derivative of the trigonometric part of (16) is

\[
 (\lambda B-.09-1.6A)\sin x
       +(\lambda A-.09+1.6B)\cos x.                 \tag{19}
\]

Both coefficients are negative. For the second it is enough to use
\(A<2.028\), \(B<-1.398\), and \(\lambda\le.494\).
Since \(\sin x,\cos x>0\), equations (17)--(19) imply

\[
 F^{(4)}(x)<0.                                      \tag{20}
\]

Consequently \(F''\) is concave on the full interval. Directly
differentiating (16) gives its convenient endpoint formula

\[
 F''(x)=(.8A-\lambda B+.09)\sin x
             +(-\lambda A+.09-.8B)\cos x
             -\mathcal R\Delta/N^3.                \tag{21}
\]

It satisfies

\[
 F''(3/5)>\frac34,\qquad F''(19/20)>\frac{59}{100}.
\]

Concavity puts \(F''\) above its endpoint chord. In particular

\[
 F''(x)>\frac12                                      \tag{22}
\]

throughout the entire original interval.

### 3.2. A single interior evaluation proves the complete bound

At \(x_0=4/5\), formula (16) and its first derivative give

\[
 F(4/5)>\frac{911}{1000},\qquad |F'(4/5)|<\frac1{250}.
\]

Use (2) with \(m=1/2\). For every \(x\in[3/5,19/20]\),

\[
 F(x)>\frac{911}{1000}-\left(\frac1{250}\right)^2
       =\frac{113873}{125000}
       =\frac{9099}{10000}+\frac{271}{250000}.        \tag{23}
\]

This is a strict lower bound for the whole varying-multiplier case.
All other cases in the inherited high/high proof have analytic
monotonicity or concavity arguments. Its intrinsic sign and support
classification therefore still covers every originally feasible axis,
including the reflected target axes and common interval endpoints.
Equation (23) completes the \(H/H\) scalar replacement.

## 4. Exact scalar arithmetic, without numerical sampling

The few evaluations in this note follow from fixed rational substitution
in the displayed formulas. To make their precision reproducible, define

\[
 S_n(x)=\sum_{2j+1\le n}\frac{(-1)^j x^{2j+1}}{(2j+1)!},
 \qquad
 C_n(x)=\sum_{2j\le n}\frac{(-1)^j x^{2j}}{(2j)!}.
\]

For the positive arguments used above, alternating remainders give

\[
 S_{11}(x)<\sin x<S_{13}(x),\qquad
 C_{14}(x)<\cos x<C_{12}(x).                         \tag{24}
\]

Use \(\sin2x=2\sin x\cos x\) and
\(\cos2x=\cos^2x-\sin^2x\) in (7). Substitution at
\(9/8\), \(13/12\), and the two original endpoints proves
(9), (11), and (13) by rational arithmetic; the excess precision of
(24) is much greater than their stated reserves. This does not assert
a value at any unevaluated state: (8)--(12) are what prove the uniform
curvature bound.

For the high/high values, the necessary positive-root brackets are

\[
 2.79842813<\mathcal R<2.79842814,\qquad
 1.71322294<a_1<1.71322295,
\]

\[
\begin{aligned}
 .58345671&<N(3/5)<.58345673,\\
 .50762535&<N(4/5)<.50762537,\\
 .46090109&<N(19/20)<.46090111.
\end{aligned}                                                       \tag{25}
\]

Each is verified by squaring positive rationals against the defining
quadratic. The bracket for \(a_1\) uses
\((29/25)a_1^2+2a_1+1=2Q\), whose left side increases for
\(a_1>0\). Equations (21), (24), and (25) give the endpoint
curvature bounds, and (16)--(17) give the value and slope at \(4/5\).
The inequalities in (18), (19), and (23) are already explicit rational
comparisons.

The proof consists of these stated identities, elementary circle
supports, and whole-interval curvature arguments. Symbolic and exact
rational calculations were used to check transcription. No calculated
PASS statement, interval cover, root-isolation routine, Lean compilation,
or generated coefficient list is a mathematical premise.
