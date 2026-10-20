# The short positive excess in the paired negative core-E system

## 1. Scope

Put

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 K=\frac{13}{12},\qquad T=\frac{61}{250},\qquad
 p(t)=1+\frac{t^2}{2}+50t^4.
\tag{1}
\]

Use the ordinary full-circle increment

\[
 U_{v,w}(d)=v(\cos d+\sin d-1)
 -R\left\{\sqrt{v^2+w^2+2vw\sin d}-\sqrt{v^2+w^2}\right\},
 \quad \frac12\le\frac vw\le1,
\tag{2}
\]

and the exact EH baseline gain from
[the adaptive EH estimate](HAND_G3_CORE_E_ADAPTIVE_EH_QUADRATIC_GAIN.md):

\[
 \begin{split}
 A(t)&=1+\frac12\cos t+K\sin t,\\
 H_k(t)&=p(t)A(t)-\frac32
 -R\left\{\sqrt{p(t)^2+k^2}-\sqrt{1+k^2}\right\}.
 \end{split}
\tag{3}
\]

For fixed \(\theta\in[0,T]\), suppose
\(\theta\le t\le T\), \(.647\le k\le.8\), and every
unaffected pair in (2) has \(w\le2\). Then each of

\[
 H_k(t)+U_{v,w}(t-\theta),\qquad
 H_k(t)+U_{k,p(t)}(t-\theta)
\tag{4}
\]

is strictly increasing in \(t\). Thus every pure positive-excess
term after the DE error has reached zero is minimized at
\(t=\theta\). The first expression in (4) applies to the G and B
pairs. The second retains the actual changing H coefficient.

This is a scalar comparison. It does not create a new original
owner or move a center. In particular, its derivative proof uses
the exact gain (3); only at the resulting endpoint need that gain
be replaced by its proved polynomial lower bound. All terminating
decimal constants in this note are exact rationals.

## 2. A short-angle derivative bound for U

The whole-interval concavity proved in
[the TD2 concentration note](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
implies \(U'(d)\ge U'(T)\) for \(0\le d\le T\).
Write \(r=v/w\), \(S=\sin T\), \(C=\cos T\). Then

\[
 \frac{U'(T)}w=f(r)
 =r(C-S)-\frac{RrC}{\sqrt{1+r^2+2rS}}.
\tag{5}
\]

It is strictly convex on \([1/2,1]\), since

\[
 f''(r)=\frac{RC\{3r+2S+2Sr^2+rS^2\}}
                  {(1+r^2+2rS)^{5/2}}>0.
\tag{6}
\]

At the single pivot \(r_0=173/200=.865\), alternating Taylor
bounds and positive squaring give

\[
 f(r_0)>-.4982,\qquad 0<f'(r_0)<.001.
\tag{7}
\]

Here sufficient explicit enclosures are

\[
 \begin{gathered}
 1.978787507<R<1.978787508,\\
 1.471791049<\sqrt{1+r_0^2+2r_0S}<1.471791051,\\
 S_{11}(T)<S<S_9(T),\qquad C_{10}(T)<C<C_{12}(T),
 \end{gathered}
\tag{8}
\]

where \(S_n,C_n\) are the corresponding truncated sine and
cosine series. For example, the lower value in (7) is bounded by
\(r_0(C_{10}-S_9)-1.978787508r_0C_{12}/1.471791049\).
For the derivative, use
\(f'=C-S-RC(1+rS)/(1+r^2+2rS)^{3/2}\) and the same
one-sided enclosures. The tangent to (5) therefore gives

\[
 f(r)>-.4982-.365(.001)=-.498565>-.5.
\tag{9}
\]

Consequently

\[
                         U'_{v,w}(d)>-\frac w2
                    \qquad(0\le d\le T).
\tag{10}
\]

## 3. The exact EH gain has derivative greater than one

The function \(Rp/\sqrt{p^2+k^2}\) decreases with \(k\), and
is concave as a function of \(p>0\). Its tangent at \(p=1\),
using \(k=.647\), gives

\[
 \frac{Rp}{\sqrt{p^2+k^2}}<1.662+.492(p-1),\qquad p\ge1.
\tag{11}
\]

The two rational square comparisons are

\[
 Q<1.662^2(1+.647^2),\qquad
 Q(.647)^4<.492^2(1+.647^2)^3.
\tag{12}
\]

Set \(C_2=1-t^2/2\), \(S_3=t-t^3/6\), and

\[
 \begin{split}
 A_-&=1+C_2/2+KS_3,\qquad A'_- =KC_2-t/2,\\
 P_H(t)&=(t+200t^3)\{A_- -1.662-.492(p(t)-1)\}
                         +p(t)A'_-.
 \end{split}
\tag{13}
\]

Since \(p'\ge0\), (11) and the alternating Taylor bounds imply
\(H_k'(t)\ge P_H(t)\). This is a degree-seven polynomial.
For an entirely explicit whole-interval certificate, expand
\(P_H(T(x+1)/2)=\sum_{j=0}^7 b_j\mathcal T_j(x)\), where
\(\mathcal T_j\) denotes the Chebyshev polynomial. Direct rational
coefficient collection gives

\[
 b_0-\sum_{j=1}^7|b_j|
 =\frac{225281487991795900741}{225000000000000000000}
 >1.0012.
\tag{14}
\]

The coefficients in (14) are uniquely specified by the fixed
polynomial (13); no sampled values or interval rows enter the
comparison. It follows that \(H_k'>1.0012\). Combining this with
(10) and \(w\le2\) proves strict increase of the first expression
in (4), with derivative greater than \(.0012\).

## 4. Retaining the changing H pair

Put \(d=t-\theta\in[0,t]\),
\(N=\sqrt{p^2+k^2+2kp\sin d}\), and \(\phi=\cos+\sin\).
After cancellation of the intermediate H norm, the derivative
of the second expression in (4) is exactly

\[
 p'\left\{A-\frac{R(p+k\sin d)}N\right\}
       +pA'+k\phi'(d)-\frac{Rkp\cos d}N.
\tag{15}
\]

On the stated domain,

\[
 \frac{R(p+k\sin d)}N<1.81,\qquad
 \frac{Rkp\cos d}N<1.32,\qquad
 k\phi'(d)\ge .647(C_2-t).
\tag{16}
\]

For the first bound, write \(r=k/p\). The ratio
\((1+r\sin d)/\sqrt{1+r^2+2r\sin d}\) decreases with \(r\)
and increases with \(d\). Thus use \(k=.647,p=p(T),d=T\)
and the bounds (8), and square the positive terms. For the second,
drop \(\cos d\), replace \(N\) by \(\sqrt{p^2+k^2}\),
and then use \(p=p(T),k=.8\). The resulting two exact tests are

\[
 \begin{split}
 Q(p(T)+.647S_9)^2
   &<1.81^2\{p(T)^2+.647^2+2p(T)(.647)S_{11}\},\\
 Q(.8)^2p(T)^2&<1.32^2\{p(T)^2+.8^2\}.
 \end{split}
\tag{17}
\]

Equations (15)--(16) bound the derivative below by

\[
 \begin{split}
 L(t)&=pA'_-+.647(C_2-t)-1.32+p'(A_- -1.81)\\
 &=\frac{1231}{3000}-\frac{1457}{1000}t
   +\frac{4559}{6000}t^2-\frac{125}{2}t^3
   +\frac{38935}{144}t^4-75t^5-\frac{2275}{36}t^6.
 \end{split}
\tag{18}
\]

For \(0\le t\le T\), absorb the last two terms into the
fourth-degree term. This gives \(L(t)\ge P_4(t)\), where

\[
 P_4(t)=\frac{1231}{3000}-\frac{1457}{1000}t
   +\frac{4559}{6000}t^2-\frac{125}{2}t^3+248.3196t^4.
\tag{19}
\]

Expand \(P_4(43/200+x)=\sum_{j=0}^4 c_jx^j\). The first
completed square gives

\[
 c_2+c_3x+c_4x^2\ge
 D:=c_2-\frac{c_3^2}{4c_4}
 =\frac{197004243693449}{31039950000000}>6.346.
\tag{20}
\]

The second gives the global lower bound

\[
 P_4(t)\ge c_0-\frac{c_1^2}{4D}
 =\frac{32650606596168998498285449}
        {788016974773796000000000000}>.0414.
\tag{21}
\]

Thus (15) is positive on the full domain, proving the remaining
claim in (4). The proof retains the actual EH multiplier and the
actual H norm throughout; it needs no monotonicity of a lower
polynomial substitute for \(H_k\).
