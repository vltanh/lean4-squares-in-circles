# The zero-quarter row for every core/outer boundary pair

This is a hand proof of the entire \(k=0\) row of the common transition
table. It uses a finite list of named geometric regimes, elementary
one-variable concavity, and the displayed rational endpoint bounds.
No search output or subdivision certificate is a premise.

Put
\[
 Q=\frac{9789}{2500},\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},\quad
 h=\frac{291}{250},\quad a_C=\frac7{12}.
\]
The positive half of an outer state is
\[
 O=\{(a,b):0\le b\le a,\ (a+\tfrac12)^2+(b+\tfrac12)^2=Q\}.
\]
The positive core boundary \(C\) consists of the side
\(a=7/12,\ 0\le b\le1/2\), followed by the arc
\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},
 \qquad \frac12\le b\le a.
\]
Define positive-half labels
\[
 L_O(a,b)=-\frac9{100}+pa+qb,\qquad
 L_C(a,b)=\frac{73}{10}(a_C-a)+hb.                      \tag{1}
\]
For signs \(\sigma,\tau\in\{-1,1\}\), use source/target labels
\(\sigma L_s,\tau L_t\). The quantity to bound is
\[
 {\cal C}=\phi+\sigma L_s(a,b)-\tau L_t(A,B).            \tag{2}
\]
Assume
\[
 |\phi|\le\frac7{10},\qquad
 \delta=\phi+\sigma\arctan(b/a)-\tau\arctan(B/A)
       >\frac{19}{25}.                                 \tag{3}
\]
If the two squares have a true separating axis, then
\[
 \boxed{{\cal C}>\frac{391}{400}.}                       \tag{4}
\]
The proof only needs the four surviving SAT axes established by the
common-point and backward-axis lemmas. Reflection followed by reversing
the pair preserves \(\phi,{\cal C},\delta\), changes the signs to
\((-\tau,-\sigma)\), and exchanges source/target axes. Therefore it
suffices to consider the source secondary and negative-primary axes:
\[
\begin{array}{ll}
\text{secondary:}&
 \sigma b+A\sin\phi-\tau B\cos\phi\ge W,\\
\text{negative primary:}&
 a-A\cos\phi-\tau B\sin\phi\ge W,\\
&W=(1+|\sin\phi|+|\cos\phi|)/2.
\end{array}                                             \tag{5}
\]

## 1. Elementary state bounds used throughout

Let \(a_0=\sqrt{Q-1/4}-1/2\) and \(d=\sqrt{Q/2}-1/2\). Direct squaring gives
\[
 \frac{141}{100}<a_0<\frac{283}{200},\qquad
 \frac{89}{100}<d<\frac9{10}.                            \tag{6}
\]
Every outer state has \(d\le a\le a_0,\ 0\le b\le d\).
As a function of \(b\),
\[
 a'(b)=-\frac{b+1/2}{a+1/2}\in[-1,0],\qquad a''(b)<0.
\]
Consequently \(L_O\) increases and is positive. Also
\[
 -\frac{19}{1000}<L_O(a,b)-b<\frac1{500}.                \tag{7}
\]
For the lower inequality in (7), the concave function
\(pa+(3/200)b\) takes its minimum at an arc endpoint; (6) gives
the result at both endpoints. For the upper inequality, its derivative
is negative, since
\((b+1/2)/(a+1/2)\ge100/383>3/13\). Its maximum is axial,
and (6) again suffices.

Every core state satisfies
\[
 \frac{11}{20}<a\le a_C,\quad 0\le b<\frac{14}{25},\quad
 L_C\ge hb.                                            \tag{8}
\]
If \(b<1/2\), then \(a=a_C\) and \(L_C=hb\).

For later support calculations, the following elementary rule removes
the outer state variable. If \(v\ge0\), the minimum of \(u a+v b\) on
\(O\) is attained at the axial or diagonal endpoint. For \(u\ge0\)
this follows from concavity. For \(u<0\) its derivative is positive,
so the axial endpoint is the minimum.

We use the Taylor bounds
\[
\begin{array}{c|ccc}
x&\text{lower }\sin x&\text{upper }\sin x&\text{lower }\cos x\\ \hline
1/10&9983/100000&999/10000&199/200\\
1/4& &1/4&31/32\\
2/5&389/1000&2/5&23/25\\
1/2&47/100&1/2&7/8\\
7/10&3221/5000&16106/25000&19121/25000
\end{array}                                             \tag{9}
\]
Empty entries are not needed. The degree \(7,5,6\) alternating Taylor
bounds prove all the nontrivial entries.

We will also use this simple endpoint criterion: if
\(F(x)=x+c+A\cos x-B\sin x\), with \(A,B>0\), on an interval
in \((0,\pi/2)\), then \(F''=\cos x(-A+B\tan x)\) changes
sign at most once, from negative to positive. If the derivative at
the right endpoint is negative, \(F\) has no interior minimum.

## 2. Source-secondary regimes

The sign pattern \((-,+)\) is impossible by (3), because then
\(\delta\le\phi\le7/10\). The following table records the complete
remaining cover. The proofs follow the table.

| source/target | signs | lower cost or reason |
|---|---|---|
| \(C,C\) | \(+,+\) or \(-,-\) | impossible |
| \(C,C\) | \(+,-\) | \(11/10\) |
| \(C,O\) | \(-,-\) | \(9831104/10000000\) |
| \(C,O\) | \(+,+\) | \(501811/500000\) |
| \(C,O\) | \(+,-\) | \(19657/20000\) |
| \(O,C\) | \(-,-\) | impossible |
| \(O,C\) | \(+,+\) | \(17785/15000\) |
| \(O,C\) | \(+,-\) | \(19657/20000\) |
| \(O,O\) | \(-,-\) | \(979/1000\) |
| \(O,O\) | \(+,-\) | \(9783/10000\) |
| \(O,O\) | \(+,+\) | \(9783839/10000000\) |

Every displayed lower value exceeds \(391/400\).

### 2.1 Impossible secondary cases

For target core and signs \((-,-)\), the projection is at most
\(A\sin\phi+B\cos\phi\). If \(\phi\le0\) this is below \(14/25\);
if \(\phi>0\), it is below
\((7/12)(13/20)+14/25<1\). This treats both \(C,C\) and \(O,C\).
For \(C,C\) and signs \((+,+)\), the projection is at most
\(14/25+(7/12)(13/20)<1\). These contradict \(W\ge1\).

### 2.2 \(C,C\), signs \((+,-)\)

For \(\phi\ge0\), (5), (8), and \(A\le7/12\) give
\[
 {\cal C}\ge
 \phi+\frac{291}{500}(1+\cos\phi)-\frac{97}{1000}\sin\phi.
\]
Its derivative is positive on \([0,7/10]\), so its minimum is
\(291/250\). For \(\phi=-x\le0\), the same argument using
\(A>11/20\) gives
\[
 {\cal C}>
 -x+\frac{291}{500}(1+\cos x)+\frac{6111}{5000}\sin x.
\]
This is concave on \([0,7/10]\). Both endpoint values exceed
\(11/10\), by (9).

### 2.3 \(C,O\), signs \((-,-)\)

Here \(\phi>0\). On an outer arc, \(A\sin\phi+B\cos\phi\) increases
with \(B\), since \(\cos\phi>\sin\phi\). Hence
\[
 b\le d(\sin\phi+\cos\phi)-W
 <\frac25\sqrt2-\frac12<\frac7{100}.
\]
Thus the core source has \(L_C=hb\). Nonnegativity of \(b\) also
implies \(\sin\phi+\cos\phi>5/4\), so \(\phi>1/4\).

Use SAT multiplier \(1\). The source remainder is greater than
\(-(h-1)(7/100)=-287/25000\). The target coefficients
\(p-\sin\phi<0,\ q-\cos\phi>0\) force its minimum to the axial
endpoint. Using (6) gives
\[
 {\cal C}>
 F(\phi):=\phi+\frac{49017}{100000}
                 +\frac12\cos\phi-\frac{183}{200}\sin\phi.
\]
The endpoint criterion in Section 1 applies, since \(F'(7/10)<0\).
The table (9) gives
\[
 F(1/4)>\frac{199159}{200000},\qquad
 F(7/10)>\frac{9831104}{10000000}.
\]

### 2.4 \(C,O\), signs \((+,+)\)

Feasibility forces \(\phi>1/10\): for \(\phi\le0\) the projection is
at most \(b<14/25\), and for \(0\le\phi\le1/10\) it is at most
\(14/25+(283/200)(1/10)<1\).

Set \(\lambda=21/20<h\). The source remainder
\(L_C-\lambda b\) is nonnegative. Allowing the whole outer circle
for the target gives
\[
\begin{split}
 {\cal C}&\ge F(\phi)
 =\phi+\frac{231}{200}+\lambda\sin\phi-RN(\phi),\\
 N^2&=p^2+q^2+\lambda^2
                   +2\lambda(p\sin\phi-q\cos\phi).
\end{split}                                             \tag{10}
\]
The identity
\[
 N''+\frac N4
 =\frac{(p^2+q^2-\lambda^2)^2}{4N^3}\ge0                 \tag{11}
\]
proves concavity of \(F\). For completeness,
\[
 \frac{N^2}{\sin^2\phi}
 =\left(\frac{q-\lambda\cos\phi}{\sin\phi}\right)^2
  +\left(\lambda+\frac p{\sin\phi}\right)^2.
\]
The first ratio increases and lies between \(-2/5\) and \(2/5\)
by (9); the second is less than \(7/4\). Thus
\(N<(9/5)\sin\phi\). Since \(R<2\), (11) gives
\(F''<(-\lambda+9/10)\sin\phi<0\).

The two endpoint computations are
\[
\begin{array}{c|cc}
x&\text{upper }N(x)&\text{lower }F(x),\ R<1979/1000\\ \hline
1/10&173/1000&2034909/2000000\\
7/10&193/250&501811/500000 .
\end{array}
\]
Each norm bound is checked by squaring and using (9).

### 2.5 \(C,O\), signs \((+,-)\)

Set \(\lambda=q=203/200\). The source remainder
\(L_C-\lambda b\) is nonnegative. The target coefficients are
\(p-\lambda\sin\phi,\ q-\lambda\cos\phi\), with second coefficient
nonnegative, so the outer endpoint rule applies. The two resulting
lower bounds are
\[
\begin{split}
 F_a(\phi)&=\phi+\lambda W-\frac9{100}
                          +(p-\lambda\sin\phi)a_0,\\
 F_d(\phi)&=\phi+\lambda W-\frac9{100}
                   +(p+q-\lambda(\sin\phi+\cos\phi))d.  \tag{12}
\end{split}
\]
For \(\phi\ge0\),
\[
 F_d(\phi)-F_d(0)
 =\phi-\lambda(d-\tfrac12)(\sin\phi+\cos\phi-1)\ge0,
\]
using \(\sin\phi+\cos\phi-1\le\phi\) and
\(\lambda(d-1/2)<1\). Also
\[
 F_a(\phi)>
 \phi+\frac{10183}{20000}
       +\frac{203}{400}\cos\phi-\frac{37149}{40000}\sin\phi.
\]
This last function has no interior minimum by the endpoint criterion;
its endpoint values exceed \(1\) and \(9989/10000\), respectively.

For \(\phi=-x\le0\), each difference \(F_a(-x)-F_a(0)\) and
\(F_d(-x)-F_d(0)\) is nonnegative. Explicitly, these differences are
\[
\begin{split}
 -x-\frac\lambda2(1-\cos x)+\lambda(a_0+\tfrac12)\sin x,\\
 -x+\lambda(d-\tfrac12)(1-\cos x)
                   +\lambda(d+\tfrac12)\sin x .
\end{split}
\]
Use (6), \(\sin x\ge(551/600)x\), and
\(1-\cos x\le(7/20)x\).
Finally,
\[
 F_a(0)>1,\qquad
 F_d(0)=\lambda-\frac9{100}+pd>\frac{19657}{20000}.
\]

### 2.6 \(O,C\), signs \((+,+)\)

First \(\phi>0\). If \(B\ge1/2\), then the separating projection is
less than
\[
 \frac9{10}+\frac7{12}\frac{13}{20}
                       -\frac12\frac{19}{25}<1.
\]
Thus \(B<1/2\), so \(A=a_C\), \(L_C=hB\).
Also (5) gives \(b\ge W-a_C\sin\phi\). For \(\phi\le2/5\) the
right side is at least
\(1/2+(1/2)(23/25)-(1/12)(2/5)>9/10\), impossible.
Hence \(\phi>2/5\).

From SAT,
\[
 b-B\ge W-a_C\sin\phi-B(1-\cos\phi)
       \ge\cos\phi-\frac1{12}\sin\phi.
\]
Using (7) and \(B<1/2\),
\[
 {\cal C}>
 \phi+\cos\phi-\frac1{12}\sin\phi-\frac{101}{1000}.
\]
This increases on \([2/5,7/10]\). The lower bound at \(2/5\)
from (9) is \(17785/15000\).

### 2.7 \(O,C\), signs \((+,-)\)

For \(\phi\ge0\), use \(\lambda=q\). The source remainder is
\(-9/100+pa\ge-643/20000\). For the target, put \(u=a_C-A\ge0\):
\[
 L_C-\lambda(A\sin\phi+B\cos\phi)
 =-\lambda a_C\sin\phi
 +(73/10+\lambda\sin\phi)u+(h-\lambda\cos\phi)B
 \ge-\lambda a_C\sin\phi.
\]
Consequently
\[
 {\cal C}\ge
 \phi+\frac{9507}{20000}+\frac{203}{400}\cos\phi
                   -\frac{203}{2400}\sin\phi .
\]
Its derivative is positive, so its minimum is
\(19657/20000\).

For \(\phi=-x<0\), feasibility and (8) imply \(x<1/2\):
otherwise the SAT margin is less than
\[
 \frac25+\frac3{50}\cos x-\frac{21}{20}\sin x
 \le\frac{23}{50}-\frac{21}{20}\frac{47}{100}<0.
\]
SAT also yields
\[
 B\ge-\frac25+\frac12\cos x+\frac{21}{20}\sin x.
\]
The right side is positive. Using (7), \(L_C\ge hB\), and SAT
once more gives
\[
 {\cal C}>
 \frac{2077}{5000}+\frac{291}{500}\cos x
                      +\frac{6111}{5000}\sin x-x .
\]
This is concave on \([0,1/2]\). Its endpoint lower bounds are
\(4987/5000\) and \(499542/500000\), both exceeding (4).

### 2.8 \(O,O\), signs \((-,-)\)

Feasibility forces \(\phi>0\). It also forces \(B>7/25\):
\[
 B\ge W-A\sin\phi>
 \frac12+\frac12\cos\phi-\frac{183}{200}\sin\phi
 >\frac7{25}
\]
by (9). Now (7) and SAT give
\[
 {\cal C}>
 \phi+\frac{759}{1000}
            +\frac{11}{50}\cos\phi-\frac{183}{200}\sin\phi .
\]
The derivative is positive, since
\((11/50)^2+(183/200)^2<1\). Its value at zero is \(979/1000\).

### 2.9 \(O,O\), signs \((+,-)\)

Use \(\lambda=39/40\). The outer endpoint rule shows that the source
remainder \(pa+(q-\lambda)b\) is at least \(pa_0\); indeed the diagonal
endpoint is larger by (6). The target is again minimized at one of its
two endpoints. The lower bounds are
\[
\begin{split}
 F_a(\phi)&=\phi+\lambda W-\frac9{50}
                                +pa_0+(p-\lambda\sin\phi)a_0,\\
 F_d(\phi)&=\phi+\lambda W-\frac9{50}
                       +pa_0+(p+q-\lambda(\sin\phi+\cos\phi))d.
\end{split}                                             \tag{13}
\]
At zero, both are at least
\[
 F_a(0)=\lambda-\frac9{50}+2pa_0>\frac{9783}{10000}.
\]
For \(\phi\ge0\), the diagonal difference is nonnegative exactly as
in Section 2.5. For the axial difference, the degree-five upper bound
for sine and degree-two lower bound for cosine give
\[
 F_a(\phi)-F_a(0)\ge\phi P(\phi),
\]
where
\[
 P(x)=1-\frac{35685}{40000}-\frac{39}{160}x
          +\frac{35685}{240000}x^2-\frac{35685}{4800000}x^4.
\]
Its derivative is negative on \([0,7/10]\), and \(P(7/10)>0\).
For \(\phi=-x\le0\), the same two nonnegative differences as in
Section 2.5 apply, with \(\lambda=39/40\).

### 2.10 \(O,O\), signs \((+,+)\)

This is the critical regime proved separately in
QUARTER_ZERO_OUTER_POSITIVE_HAND_PROOF.md.
That argument uses \(\lambda=1939/2000\), a single outer-circle
quadratic, and the norm identity (11). Its two endpoint rows give
the lower bound \(9783839/10000000\).

## 3. Source negative-primary regimes

All source-core cases are impossible: their projection is less than
\[
 \frac7{12}-\frac{11}{20}\frac{19}{25}
                           +\frac9{10}\frac{13}{20}<1.
\]
If the target sign is positive, then the source sign must also be
positive by (3), and \(\phi>19/25-\pi/4>-1/30\).
For \(\phi\ge0\), the projection is less than
\(283/200-(11/20)(19/25)<1\).
For \(-1/30<\phi<0\), it is less than
\[
 \frac{283}{200}-\frac{11}{20}\frac{999}{1000}
                              +\frac9{10}\frac1{30}<1.
\]
Thus only outer-source, negative-target cases remain. These have
\(\phi>0\) by the same bound without the last term.

The separating expression is independent of the source sign, and
\(L_O>0\). Hence negative source sign is the worse case and covers
both source signs.

### 3.1 Outer target

We claim \(b<B\). Otherwise \(a\le A\), and
\[
 a-A\cos\phi+B\sin\phi
 \le A(1-\cos\phi)+B\sin\phi
 \le d(1-\cos\phi+\sin\phi)<W.
\]
The middle maximum is diagonal because
\(\sin\phi>1-\cos\phi\) and the outer-arc derivative is nonnegative.
The last inequality follows from
\[
 W-\frac9{10}(1-\cos\phi+\sin\phi)
 =-\frac25+\frac75\cos\phi-\frac25\sin\phi>0
\]
throughout \([0,7/10]\), by monotonicity and (9).

Since \(b<B\), the bound \(a'\ge-1\) gives \(a-A\le B-b\).
SAT and the same diagonal maximum now imply
\[
 B-b\ge-\frac25+\frac75\cos\phi-\frac25\sin\phi.
\]
Using (7),
\[
 {\cal C}>
 \phi-\frac{421}{1000}+\frac75\cos\phi-\frac25\sin\phi.
\]
This is concave. Its endpoint lower bounds are \(979/1000\)
and a number greater than \(109/100\), proving (4).

### 3.2 Core target

Feasibility forces \(\phi>2/5\). Indeed for \(0\le\phi\le2/5\)
the SAT margin is at most
\[
 \frac{183}{200}-\frac{21}{20}\cos\phi
                           +\frac3{50}\sin\phi
 \le\frac{183}{200}-\frac{21}{20}\frac{23}{25}
                           +\frac3{50}\frac25<0.
\]

Use \(\lambda=12/5\). The source outer circle gives the lower support
\[
 \frac{p+q+\lambda}{2}
     -R\sqrt{(p+\lambda)^2+q^2}.
\]
For the target, put \(u=a_C-A\), and write
\[
 L_C+\lambda(A\cos\phi-B\sin\phi)
 =\lambda a_C\cos\phi+v u+wB,
\quad
 v=\frac{73}{10}-\lambda\cos\phi,\quad w=h-\lambda\sin\phi.
\]
Here \(v\ge49/10\) and \(\max(-w,0)<2/5\).
On the vertical core side, the minimum of \(wB\) is
\(\min(0,w/2)\). On the corner arc, the lower support of the
whole radius-\(1/12\) circle gives an additional loss no larger than
\[
 \frac{\max(-w,0)^2}{24v}<\frac1{500}.
\]
This follows from
\(\sqrt{v^2+w^2}\le v+w^2/(2v)\); when \(w\ge0\) the axial point
already minimizes. Thus the same bound covers the entire core boundary.

Finally,
\[
 R\sqrt{(p+\lambda)^2+q^2}<\frac{132}{25}
\]
by squaring. Combining these bounds gives
\[
 {\cal C}>
 \phi+\frac{303}{100}-\frac{132}{25}
 +\frac{13}{5}\cos\phi
 +\min\left(\frac65\sin\phi,\frac{291}{500}\right)
 -\frac1{500}.                                         \tag{14}
\]
The right side is the minimum of two concave functions, hence concave
on \([2/5,7/10]\). The two endpoint lower bounds from (9) are
\[
 \frac{2517}{2500}=1.0068,\qquad
 \frac{63655}{62500}=1.01848.
\]
Both prove (4).

## 4. Closed sign endpoints and conclusion

Every argument above treats each signed half-domain as closed.
At tangent zero, define the odd marker to be zero, the average of its
two one-sided values. Averaging the already proved inequalities over
the zero-tangent choices preserves the bound. Thus no boundary
state is omitted.

Sections 2 and 3 cover both source SAT axes for every ordered C/O pair
and every sign pattern allowed by (3). Reflection and reversal cover
the remaining target axes. The excluded axes are covered by the
earlier common-point/cap lemmas. This proves the full row (4).
