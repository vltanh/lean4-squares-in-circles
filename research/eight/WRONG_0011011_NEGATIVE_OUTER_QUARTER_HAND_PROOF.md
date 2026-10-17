# 0011011: the whole negative outer-to-outer edge-2 quarter row

**Theorem.** Let both squares in edge 2 be outer states with negative local
tangent. For every retained separating axis and every
\[
 \frac\pi2-.7\le\phi\le\frac\pi2+.7,
\]
the corrected cost is strictly greater than \(.89777\), hence greater than
\(\gamma=.89765=17953/20000\). Reflected reversal gives the corresponding
edge-6 row.

This is a whole-angle hand argument. The contact-curve reductions below
use five fixed rational curvature rows, two early curvature rows, three
third-derivative rows, and explicit one-variable comparisons. The companion
contains only these fixed arithmetic checks. No minimizing search,
adaptive cover, or sampled contact hypothesis is used.

## 1. Notation and scalar facts

All decimals denote exact terminating rationals. Set
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\quad a_0=a(0).
\]
Write \(A=a(B)\), \(0\le b,B\le d\). Thus
\[
 .899<d<.9,\quad 1.4145<a_0<1.415,\quad \sqrt Q<2.
\]
The exact two labels and the cost are
\[
\begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055a(b)b,\\
 T(B)&=.01670+2.42322B-.91744B^2-.95769A B,\\
 C&=\phi-P(b)+T(B).
\end{aligned}                                                     \tag{1}
\]
Put \(s=\sin\phi,c=\cos\phi\), \(W=(1+s+|c|)/2\).
The retained projections are
\[
\begin{array}{c|l}
1&-b+As+Bc\\
2&-ac-bs+A\\
3&as-bc+B\\
4&a-Ac+Bs.
\end{array}                                                       \tag{2}
\]
At least one is at least \(W\). We prove the lower cost separately for
each of these four alternatives.

For either label \(F=c_0+p a+q b+r b^2+t ab\), writing
\(u=a+1/2,\ v=b+1/2,\ \rho=v/u\), differentiation gives
\[
\begin{aligned}
 F'&=-p\rho+q+2rb+t(a-b\rho),\\
 F''&=2r-2t\rho-(p+tb)\frac Q{u^3},\\
 F'''&=-\frac{3Q\{tQ+(p-t/2)v\}}{u^5}.
\end{aligned}                                                     \tag{3}
\]
For \(P,T\), \(p=0,t<0\). Their third derivatives are positive and
increasing: the numerator governing the fourth derivative is
\(Q(5v-1/2)-2v^2>0\) for \(1/2\le v<1.4\).
Endpoint evaluations and (3) give
\[
 .773<P'<.973,\quad P''>0,\quad P'(d)>.972,\quad P'''<.779.          \tag{4}
\]
Convexity also gives the global upper chord
\[
 P(b)\le P(0)+g b,\qquad g=.853.                                  \tag{5}
\]
Indeed \(gd>P(d)-P(0)\).

The elementary target-label bounds are
\[
 .609<T'<1.069,\qquad T'''>1.38.                                  \tag{6}
\]
For completeness, \(T'(.6)>.6101\), \(-.049<T''(.6)<0\), and
\[
 T'''=.95769\left(\frac{3Q}{u^3}
                +\frac{3bQ(b+1/2)}{u^5}\right)
       >\frac{3(.95)(3.9)}8>1.38.
\]
The integrated tangent bound gives
\(T'>.6101-(.049)^2/2.76>.609\). Convexity of \(T'\), together with
the two endpoint bounds \(T'(0),T'(d)<1.069\), gives the upper bound.
In particular both labels increase.

All appearances of \(\pi/2\) in the fixed comparisons use the enclosure
\[
 1.57079632679489<\pi/2<1.57079632679490.                           \tag{7}
\]
It follows from
\(\pi/2=8\arctan(1/5)-2\arctan(1/239)\) and alternating sums with,
respectively, 15/16 and 4/5 terms. The companion checks both rational
inequalities, in addition to the trigonometric and radical comparisons.

## 2. The aligned contact

At \(\phi=\pi/2\), axes 3 and 4 both require \(a+B\ge1\).
Since \(T\) increases, take \(B=\max(0,1-a)\).
If \(a\ge1\), the cost decreases as \(b\) increases to
\(b_1=\sqrt{Q-9/4}-1/2\). It remains to treat \(d\le a\le1\).

Define \(b=\sqrt{Q-(a+1/2)^2}-1/2\) and \(M(a)=-P(b)\).
With \(u=a+1/2,w=b+1/2\), direct simplification gives
\[
\begin{aligned}
 M''(a)&=.04726+\frac{Q(.961795-.11055u)}{w^3}
                         -.2211\,\frac u w,\\
 M'''(a)&=\frac{3Q\{.961795u-.11055Q\}}{w^5}>0.
\end{aligned}                                                     \tag{8}
\]
Thus \(M''\) increases. On the two intervals \([d,.95]\), \([.95,1]\),
\[
\begin{aligned}
 M''(.95)+T''(1-d)&<0,\\
 M''(1)+T''(.05)&<0.
\end{aligned}                                                     \tag{9}
\]
Here \(T''\) increases, so (9) bounds the second derivative of
\(M(a)+T(1-a)\) above on both intervals. Its first derivative therefore
decreases, and its value at \(a=1\) exceeds \(.0149\).
Consequently the aligned minimum is at \(a=d,b=d,B=1-d\), with
\[
 \frac\pi2-P(d)+T(1-d)>.8977827.                                  \tag{10}
\]

We will also use the consequences of (8)
\[
 M''>.979,\quad M'>.972\qquad(d\le a\le a_0),
 \qquad M'(1)<1.084.                                              \tag{11}
\]

## 3. Axes 1 and 2

Write \(\ell=\pi/2-.7\).
On the lower half \(\ell\le\phi\le\pi/2\), one has
\(s>.764,\ 0\le c<.645,\ s>c\).

Axis 1 and the chord (5) give
\[
 C\ge\phi-P(0)+T(B)-gAs-gBc+gW.
\]
The derivative of the right side in \(B\) exceeds
\[
 .609-g\{.645-.261(.764)\}>0,
\]
because \((B+1/2)/(A+1/2)>.261\).
Set \(B=0\). The resulting scalar is
\[
 F_1(\phi)=\phi+T(0)-P(0)+\frac g2+\frac g2\cos\phi
                                      -g(a_0-.5)\sin\phi.         \tag{12}
\]
Its derivative is positive, since
\(g^2\{1/4+(a_0-.5)^2\}<1\). The endpoint \(F_1(\ell)>.95\).

For axis 2, use \(a\ge d\) to bound
\(b\le(A-dc-W)/s\), substitute (5), and again minimize at \(B=0\).
The scalar exceeds (12) by
\[
 g\frac cs\{d+.5-\tfrac12s-(a_0-.5)c\}>0,                         \tag{13}
\]
using \((d+.5)^2>1/4+(a_0-.5)^2\).

On the upper half, axis 1 has the same positive target derivative.
Its scalar is
\[
 \phi+T(0)-P(0)+g/2-(g/2)\cos\phi-g(a_0-.5)\sin\phi,
\]
which increases and already exceeds \(.95\) at \(\pi/2\).
For axis 2, \(\phi\ge1.68\) gives
\(C\ge1.68-P(d)+T(0)>.9\).
For \(\pi/2\le\phi\le1.68\), the axis implies
\[
 b\le\frac{a_0(1+\sin(.11))-1}{\cos(.11)}<.6.
\]
Hence \(C\ge\pi/2-P(.6)+T(0)>.95\).
This completes both axes on their full angle intervals.

## 4. The upper halves of axes 3 and 4

Set \(\phi=\pi/2+x,\ 0\le x\le.7\).

### 4.1. Axis 3

The least target coordinate is
\[
 B=\max\{0,\ B_*(x)\},\qquad
 B_*(x)=\tfrac12-(a-\tfrac12)\cos x-(b-\tfrac12)\sin x.
\]
On its active part,
\[
 \frac{d}{dx}\{x+T(B_*)\}
   =1+T'(B_*)\{(a-\tfrac12)\sin x-(b-\tfrac12)\cos x\}
   >1-1.069(.4)>0.                                               \tag{14}
\]
On the inactive part it is 1.
The flow to \(x=0\) remains in the target interval:
if \(b\le1/2\), \(B_*\) increases; if \(b\ge1/2\), \(B_*\) is convex.
In either case its value between two endpoints is bounded by the larger
endpoint, and \(B_*(0)=1-a<d\). Thus this axis reduces to (10).

### 4.2. Axis 4

This axis requires
\[
 a\ge a_*(x)=\tfrac12+(\tfrac12-B)\cos x-(A-\tfrac12)\sin x.
\]
The function \(a_*\) decreases, since
\((A-.5)\cos x+(.5-B)\sin x>.399(.764)-.4(.645)>0\).
Because \(M\) increases, use \(a=\max(d,a_*)\).
The active range satisfies \(d\le a\le1\).
Put \(q_0=Q-2a_0\). If \(v=-a_*'\), then
\[
 v^2\le q_0-(a-\tfrac12)^2.
\]
By (11), the function
\(M'(a)\sqrt{q_0-(a-1/2)^2}\) increases: its derivative has the sign of
\[
 M''\{q_0-(a-\tfrac12)^2\}-M'(a-\tfrac12)
 >.67(q_0-.25)-1.084(.5)>0.
\]
At \(a=1\) its value is
\(M'(1)(a_0-.5)<1\).
Therefore \(1-M'v>0\) throughout the active part, while the inactive
cost derivative is 1. This axis also reduces to alignment.

## 5. Axis 4 on the lower half

Now \(\phi=\pi/2-x\). Axis 4 requires
\[
 a\ge a_*(x)=\tfrac12+(\tfrac12-B)\cos x+(A+\tfrac12)\sin x.        \tag{15}
\]
The right side increases, and
\[
 (a_*')^2=Q-2B-(a_*-\tfrac12)^2.
\]
On its active part, (11) gives
\[
 \frac{d}{dx}\{-x+M(a_*)\}
 >-1+.972\sqrt{Q-1.8-(.915)^2}>0.                                \tag{16}
\]
On its inactive part \(a_*<d\), the derivative is \(-1\).
Thus a minimum occurs either at alignment or when \(a_*=d\).
For every \(B>1-d\), that crossing occurs before \(x=.7\):
the smallest value of (15) at \(.7\), attained at \(B=d\), exceeds \(d\).

Parameterize the diagonal boundary by
\[
\begin{gathered}
 k=\tfrac12-d,\quad Z=\cos x+k,\quad Y=\sqrt{Q-Z^2},\\
 U=Y\cos x-Z\sin x,\quad V=Y\sin x+Z\cos x,\quad B=V-\tfrac12,\\
 f=1-\frac{\sin x}{Y}.
\end{gathered}
\]
Direct differentiation gives
\[
 U'=-Vf,\quad V'=Uf,\quad
 f'=\frac{(1-Q+k^2)\cos x+k(1+\cos^2x)}{Y^3}<0.                   \tag{17}
\]
Hence \(B'>0,\ B''=-Vf^2+Uf'<0\).
The boundary begins at \(B=1-d,x=0\) and ends at \(B=d,x=x_*\),
where \(x_*<.556\).

Its cost is \(H=\pi/2-x-P(d)+T(B(x))\).
For \(0\le x\le.3\), \(T''(B)<0\), so \(H''<0\).
For \(.3\le x\le.4\), the following fixed endpoint bounds hold:
\[
\begin{gathered}
 B<.724,\quad T''(B)<.396,\quad B'<1.394,\\
 V>1.092,\quad U>1.554,\quad f>.795,\quad -f'>.4.
\end{gathered}
\]
For the final estimate in this line, use \(Y<2,\cos x>.92\) in (17);
the negative numerator exceeds \(3.2\).
These bounds give
\[
 H''<.396(1.394)^2
       -.609\{1.092(.795)^2+1.554(.4)\}<0.                        \tag{18}
\]
For \(.4\le x\le x_*\), convexity of \(T'\) bounds it by \(.774\)
at the two target endpoints, while \(B'\le B'(.4)<1.238\).
Thus \(H'<-1+.774(1.238)<0\).
The boundary minimum is consequently at one of its two endpoints.
The first is (10); the second has
\[
 H(x_*)>\pi/2-.556-P(d)+T(d)>.903.                               \tag{19}
\]

## 6. Axis 3 on the lower half: contact completeness and concavity

This final axis requires
\[
 B\ge B_*(b,x)
 =\tfrac12-(a-\tfrac12)\cos x+(b+\tfrac12)\sin x.                 \tag{20}
\]
Since \(T\) increases, take \(B=\max(0,B_*)\).
On an inactive part \(B_*\le0\), increasing \(b\) decreases the cost;
the flow reaches \(B_*=0\), since \(B_*(d,x)>0\).
It therefore suffices to consider the contact (20).

Write
\[
 u=a+\tfrac12,\quad r=\frac{b+1/2}{u},\quad
 q=Q+1-2u,\quad z=B-\tfrac12,\quad v=\sqrt{q-z^2}.
\]
Here \(q>1\), \(-.5\le z<.4\), and \(v>0\).
The contact determines a smooth \(x=x(b,B)\). Its derivative satisfies
\[
 -x_b=\frac{Q-u}{u q}+\frac{zr}{qv}.                             \tag{21}
\]
Also \(x_b<0\), directly from the positive \(b\)- and \(x\)-derivatives
of (20). Thus, for each fixed \(B\), the admissible \(b\)'s form a closed
interval. Its endpoints have \(b=0\), \(b=d\), \(x=0\), or \(x=.7\).

For \(F(b,B)=-x(b,B)-P(b)\), differentiating (21) gives
\[
 F_{bb}=-r f_1'(u)
   +\frac z{qv}\left\{\frac Q{u^3}-\frac{2r^2}q-\frac{r^2}{v^2}\right\}
   -P''(b),                                                     \tag{22}
\]
where
\[
 f_1'(u)=\frac{4Qu-2u^2-Q(Q+1)}{u^2q^2}.
\]
The following five fixed rows bound (22) strictly above by a negative
number for every target coordinate:
\[
\begin{array}{c|r}
 b\text{ interval}&\text{upper bound for }F_{bb}\\ \hline
 [0,.2]&-.018\\
 [.2,.4]&-.096\\
 [.4,.6]&-.126\\
 [.6,.8]&-.045\\
 [.8,.9]&-.081
\end{array}                                                       \tag{23}
\]
Here is an explicit rational recipe for each row. On its \(b\) interval,
bound \(u=\sqrt{Q-(b+1/2)^2}\), \(r=(b+1/2)/u\), \(q=Q+1-2u\)
by their endpoint intervals. The numerator of \(f_1'\) increases in \(u\).
The expression in braces in (22) is between
\[
 \frac Q{u^3}-\frac{2r^2}q-\frac{r^2}{q-.25},
 \qquad
 \frac Q{u^3}-\frac{3r^2}q.
\]
Let \(N\) be the larger absolute endpoint bound for these two intervals.
Replace the middle term of (22) by
\(.5N/\{q\sqrt{q-.25}\}\), and replace \(P''\) by its left endpoint
value. Ordinary directed rational arithmetic gives exactly (23).
These are five displayed evaluations of the stated formula, with no
subdivision algorithm.

Strict concavity in \(b\) now forces the minimum to one of the four
boundary types listed after (21). Alignment is (10).
We handle the other three boundaries next.

### 6.1. The axial source \(b=0\)

If \(x\le.65\), the direct bound is
\[
 C\ge\pi/2-.65-P(0)+T(0)>.9.
\]
If \(.65\le x\le.7\), (20) increases with \(x\) and gives \(B>.074\).
Therefore
\[
 C>\ell-P(0)+T(0)+.609(.074)>.9.                                 \tag{24}
\]

### 6.2. The diagonal source \(b=d\)

On this boundary
\[
 B=\tfrac12-(d-\tfrac12)\cos x+(d+\tfrac12)\sin x,\qquad
 v=B'=\sqrt{Q-2d-(B-\tfrac12)^2}.
\]
It runs from \(B=1-d\) to \(B=d\).
For \(H(x)=\pi/2-x-P(d)+T(B(x))\),
\[
\begin{aligned}
 H'&=-1+T'v,\\
 H''&=T''v^2-T'(B-\tfrac12),\\
 H'''&=v\{T'''v^2-3T''(B-\tfrac12)-T'\}>0.                       \tag{25}
\end{aligned}
\]
For \(B\le1/2\), the last inequality follows from
\(T'''>1.6,\ T''>-1.17,\ |B-1/2|<.4\).
For \(B\ge1/2\), use \(T'''>2.64,\ T''<1.317\).
In both cases \(v^2>Q-2d-.16\) and \(T'<1.069\); the two resulting
rational lower bounds are strictly positive.

A fixed comparison gives \(H'(.4)<0\).
Since \(H''\) increases, \(H\) has no interior minimum on \([0,.4]\):
a stationary point with nonnegative second derivative would force
\(H'(.4)>0\). Its endpoint values are (10) and \(H(.4)>.9095\).

For \(x\ge.4\), \(H''\ge H''(.4)>.3\).
At the rational point \(x=.5\),
\[
 H(.5)>.90204,\qquad |H'(.5)|<.022.
\]
The integrated tangent inequality and completing a square give
\[
 H>.90204-\frac{(.022)^2}{.6}>.9012.                              \tag{26}
\]
The reference point lies on the physical boundary, as \(B(.5)<d\).

### 6.3. The endpoint angle \(x=.7\)

Let \(B=B_*(b,.7)\), and put \(k=B_b,\ k_1=B_{bb},k_2=B_{bbb}\).
Explicitly,
\[
 k=r\cos(.7)+\sin(.7),\quad
 k_1=\frac Q{u^3}\cos(.7),\quad
 k_2=\frac{3Q(b+1/2)}{u^5}\cos(.7).
\]
All three increase with \(b\). The target \(B\) increases, and feasibility
\(B\le d\) implies \(b<.76\). For
\(J(b)=\ell-P(b)+T(B(b))\),
\[
\begin{aligned}
 J'&=-P'+T'k,\\
 J''&=-P''+T''k^2+T'k_1,\\
 J'''&=-P'''+T'''k^3+3T''kk_1+T'k_2.
\end{aligned}                                                     \tag{27}
\]
Two fixed endpoint substitutions give
\[
\begin{array}{c|r}
 b\text{ interval}&\text{upper bound for }J''\\ \hline
 [0,.1]&-.389\\
 [.1,.2]&-.362
\end{array}
\]
and three more give
\[
\begin{array}{c|r}
 b\text{ interval}&\text{lower bound for }J'''\\ \hline
 [.2,.3]&.410\\
 [.3,.5]&.916\\
 [.5,.76]&3.85
\end{array}.                                                       \tag{28}
\]
For the first table, use the right endpoint of the negative \(T''\),
the left endpoint of \(k\), the left endpoint of the decreasing \(T'\),
and the right endpoint of \(k_1\).
For the second, use the increasing \(T'''\), \(P'''\), and \(k,k_1,k_2\).
The \(T''\) lower endpoint in each row is negative, so its term is
bounded below using the right endpoints of \(k,k_1\).
The last positive term uses \(T'>.609\).
These rules, (3), and the displayed endpoints give (28).

Thus \(J\) has no interior minimum on \([0,.6]\):
it is concave through \(.2\), and thereafter \(J''\) increases while
\(J'(.6)<0\). Its endpoint costs exceed \(.9\) at \(b=0\), by (24),
and \(.906\) at \(b=.6\).

On the remaining feasible interval, \(J''\ge J''(.6)>.65\).
At the rational reference \(b=.72365\), which has \(B<d\),
\[
 J(.72365)>.89778507,\qquad |J'(.72365)|<10^{-6}.
\]
Completing a square gives
\[
 J>.89778507-\frac{10^{-12}}{1.3}>.89778.                         \tag{29}
\]
Equations (23)--(29) close the last half-axis, and therefore all of
the row (1)--(2).

Every final bound is strict. This row cannot occur in an equality
configuration for a cyclic sum whose proposed target is \(7\gamma\).

