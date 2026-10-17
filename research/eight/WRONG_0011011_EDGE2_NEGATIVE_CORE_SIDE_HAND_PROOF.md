# 0011011: the complete negative outer-to-core-side edge-2 transition

## Theorem and coverage

Let edge 2 have an outer source of negative sign and a core-side target
of negative sign. For every retained separating axis and every
\[
 \pi/2-.7\le\phi\le\pi/2+.7,
\]
its corrected cost is strictly greater than \(.89765\).

Together with
\`WRONG_0011011_EDGE2_NEGATIVE_CORE_CORNER_HAND_PROOF.md\`, this proves
the **whole** negative outer-to-negative core transition of edge 2.
Reflection followed by reversal also proves its edge-6 partner.
The other mixed sign/kind families are not claimed by this note.

All decimals below are exact rationals. The proof has one degree-nine
polynomial with ten positive Bernstein coefficients and fixed scalar
comparisons; its standalone checker makes 67 exact comparisons.
No sampled minimum or subdivided domain certificate is a premise.

Put
\[
 Q=3.9156,\quad a_C=7/12,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2.
\]
The outer coordinates satisfy
\[
 a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad0\le b\le d;
\]
the target side has \(A=a_C,\ 0\le B\le1/2\).
Both actual own-frame centers are \((a,+b),(A,+B)\).
Write
\[
\begin{aligned}
 L(b)&=.02478+.93015b+.02363b^2-.11055ab,\\
 c_-&=.22042-.34492(7/12),\\
 C_-(B)&=c_-+.98439B-.05334B^2.
\end{aligned}
\tag{1}
\]
The cost is \(C=\phi-L(b)+C_-(B)\).

Set \(s=\sin\phi,c=\cos\phi\) and
\(W=(1+s+|c|)/2\). The four possible separating margins are
\[
\begin{array}{c|l}
1&-b+As+Bc-W\\
2&-ac-bs+A-W\\
3&as-bc+B-W\\
4&a-Ac+Bs-W .
\end{array}
\tag{2}
\]
A margin is nonnegative for a separating axis.

## 1. Preliminary bounds and the late range

Let \(r=(b+1/2)/(a+1/2)\), so \(a'=-r\).
The direct derivatives are
\[
 L'=.93015+.04726b-.11055a+.11055br>.773,\qquad
 L''=.04726+.11055(2r+br')>0 .
\]
The fixed endpoint comparisons give
\[
 .899<d<.9,\quad a_0<1.415,\quad
 L(d)<.79091,\quad L'(d)<1.073,\quad L'(.7)>.903.
\tag{3}
\]
We also use
\[
 .261<r\le1,\quad r'>.557,\qquad L'/r<3.
\tag{4}
\]
For completeness, multiplication of the derivative of \(L'/r\) by
\(r^2\) gives the upper bound
\[
 .04726+.22110-(.93015-.11055\cdot1.415).557<0.
\]
Thus that ratio decreases, and its axial value is below 3.
The radial bounds follow immediately from the circle equation.

The core label increases on the side and corner, and has its minimum
\(c_-\) at \(B=0\). Therefore, whenever \(\phi\ge1.67\),
\[
 C>1.67-.79091+c_->.89765,
\tag{5}
\]
without using any separating axis. The interval
\(\pi/2\le\phi\le\pi/2+.1\) overlaps this direct range.

On the lower half \(\phi\le\pi/2\), axes 1 and 2 are impossible:
axis 1 is at most the norm of a core center, less than .8, before
subtracting \(W\ge1\), and axis 2 is at most \(A-W<0\).

On the upper strip write
\[
 x=\phi-\pi/2,\quad u=\sin x,\quad v=\cos x,\qquad 0\le x\le.1.
\tag{6}
\]
Here \(u<.1,\ v>.995,\ W\le1.05\).
Axis 1 is at most \(A-W<0\); axis 2 is at most
\(a_0u+A-W<1.415(.1)+7/12-1<0\).
It remains to cover axes 3 and 4.

## 2. A global quadratic minorant for the outer label

Write \(y=a+1/2\). As a function of this coordinate, the negative outer
label is
\[
 M(y)=.369499372+.02363y^2-.055275y
       -(.961795-.11055y)\sqrt{Q-y^2}.
\tag{7}
\]
For a physical state, \(M(a+1/2)=-L(b)\).
If \(t=\sqrt{Q-y^2}\), differentiation gives
\[
\begin{aligned}
 M'&=.04726y-.055275+.11055t+
              \frac{(.961795-.11055y)y}{t},\\
 M''&=.04726-\frac{.22110y}{t}
              +\frac{Q(.961795-.11055y)}{t^3},\\
 M'''&=\frac{3Q(.961795y-.11055Q)}{t^5}.
\end{aligned}
\tag{8}
\]
For \(1\le y\le1.915\), \(M'''>0\).
The fixed comparisons \(M'(1)>.67\), \(M''(1)>.58\) then show
that \(M\) is increasing and convex throughout this interval.

Here is the elementary tangent-quadratic lemma used below.
For a \(C^3\) function with nonnegative third derivative, define
\[
 T(y)=
 \frac{2\{M(y)-M(r)-M'(r)(y-r)\}}{(y-r)^2}
 =2\int_0^1(1-t)M''(r+t(y-r))\,dt,
\tag{9}
\]
with the continuous value at \(y=r\).
The integral shows that \(T\) increases with \(y\).
Consequently an endpoint check \(T(l)\ge m\) proves
\[
 M(y)\ge M(r)+M'(r)(y-r)+\frac m2(y-r)^2
 \qquad(y\ge l)
\tag{10}
\]
throughout the interval of definition.

Take \(l=1,r=1.4,m=.78\).
Exact radical brackets give
\[
\begin{aligned}
 M(1)-M(1.4)+.4M'(1.4)-.39(.4)^2&>.0014,\\
 M(1.4)&>-.790136934,\\
 |M'(1.4)-.973417553|&<4\cdot10^{-10}.
\end{aligned}
\tag{11}
\]
Since \(|y-1.4|<.6\), (9)--(11) prove the strict rational minorant
\[
 M(y)>P(y):=-.790136935+.973417553(y-1.4)+.39(y-1.4)^2
 \quad(1\le y\le1.915).
\tag{12}
\]
The extra downward allowance \(10^{-9}\) in the constant exceeds
\(.6(4\cdot10^{-10})\).

## 3. Axis 4 on the entire lower half

The separating inequality is
\[
 a\ge W+A\cos\phi-B\sin\phi.
\]
For \(A=7/12\), put
\[
 y_*:=1+\frac{13}{12}\cos\phi+(1/2-B)\sin\phi .
\tag{13}
\]
Then \(a+1/2\ge y_*\ge1\).
For every feasible state \(y_*\le a_0+1/2<1.915\).
The increasing function (7) and the minorant (12) therefore give
\[
 C>\phi+P(y_*)+c_-+.98439B-.05334B^2.
\tag{14}
\]
This only lowers the cost; no existence of the continued contact state
is required.

Put
\[
 x=\pi/2-\phi\in[0,.7],\quad s=\cos x,\quad c=\sin x,
 \quad D=-.4+\frac{13}{12}c+\frac12s,
\]
and use the rational constants
\[
 p=.973417553,\quad k=.39,\quad g=.98439,\quad z=.05334,
 \quad v=\phi-.790136935+c_--.89765.
\]
The right side of (14), after subtracting \(.89765\), is the quadratic
\[
 \mathcal A B^2+\mathcal B B+\mathcal C,
\quad
 \mathcal A=ks^2-z,\quad
 \mathcal B=g-s(p+2kD),\quad
 \mathcal C=v+pD+kD^2.
\tag{15}
\]
Here \(\mathcal A>.39(.76)^2-.05334>0\).
It is enough to prove \(4\mathcal A\mathcal C-\mathcal B^2>0\);
this proves positivity even for every real \(B\).

The exact cancellation gives the short expression
\[
 E(x)=s^2(4kv-p^2)+2gps+4gkDs
             -4z(v+pD+kD^2)-g^2 .
\tag{16}
\]
We verify \(E>0\) with one explicit polynomial on the entire interval.

Let
\[
 S_9=x-x^3/3!+x^5/5!-x^7/7!+x^9/9!,\quad
 C_{10}=1-x^2/2!+x^4/4!-x^6/6!+x^8/8!-x^{10}/10!.
\]
In (16), substitute \(s=C_{10},c=S_9\) and
\[
 \phi=\frac{3.141592653589793238}{2}-x.
\]
Call the resulting degree-21 polynomial \(E_{21}\).
The rational replacement of \(\pi\) lowers (16), because its coefficient
is \(4\mathcal A>0\).
The alternating-series errors on \(0\le x\le.7\) are
\[
 |\sin x-S_9|<5\cdot10^{-10},\quad
 |\cos x-C_{10}|<3\cdot10^{-11}.
\]
On the enclosing rectangle
\(.76\le s\le1.001,\ 0\le c\le.701\), we have \(|D|<1,|v|<1\).
Direct differentiation of (16) bounds its two partial derivatives
in magnitude by 10 and 3, respectively. The replacement error is thus
less than \(10^{-7}\).

Write \([E_{21}]_{\le9}\) for its terms of degree at most 9.
The sum of the absolute negative tail terms, each evaluated at \(x=.7\),
is less than \(10^{-7}\). Therefore
\[
 E(x)>E_9(x):=[E_{21}]_{\le9}-2\cdot10^{-7}.
\tag{17}
\]
All ten degree-nine Bernstein coefficients of \(E_9\) on \([0,.7]\)
have the following strict rational lower bounds:
\[
 \boxed{
 .0001770,\ .0059290,\ .0067752,\ .0049065,\ .0024489,\
 .0010489,\ .0014710,\ .0033222,\ .0050111,\ .0038894.}
\tag{18}
\]
For clarity, these mean the coefficients in
\[
 E_9(.7t)=\sum_{j=0}^9 e_j\binom9j t^j(1-t)^{9-j}.
\]
All are positive, proving \(E>0\) on the full interval.
Equations (14)--(18) close every lower-half axis-4 side state.

## 4. Axis 3 through \(\phi=1.5\)

Convexity of \(L\) and its endpoints give
\[
 L(b)\le.02478+.853b,\qquad
 C_-(B)\ge c_-+.9545B.
\tag{19}
\]
Subtract \(\lambda=.9545\) times the axis-3 inequality
\(a\sin\phi-b\cos\phi+B-W\ge0\) from this lower cost.
The full-circle support formula gives
\[
 F(\phi)=\phi+c_--.02478+\frac{\lambda+q}{2}
               +\lambda\sin\phi-\sqrt Q\,N(\phi),
\]
\[
 q=.853,\qquad
 N^2=\lambda^2+q^2-2\lambda q\cos\phi .
\tag{20}
\]
Indeed \(ua+vb\ge-(u+v)/2-\sqrt Q\sqrt{u^2+v^2}\) follows directly
from the outer circle after translating its center.

On \([\pi/2-.7,1.5]\), \(N\) increases and
\[
 N''+N/4=\frac{(\lambda^2-q^2)^2}{4N^3}>0.
\]
The fixed endpoint comparison
\[
 \lambda\sin(\pi/2-.7)-\frac{\sqrt Q}{4}N(1.5)>0
\]
thus makes \(F\) concave throughout this interval.
Its endpoints satisfy
\[
 F(\pi/2-.7)>.96,\qquad F(1.5)>.907.
\]
This proves the desired bound for this whole axis-3 range.

## 5. Axis 3 from \(1.5\) to the quarter angle

If \(b\le.7\), then (3) immediately gives
\[
 C\ge1.5-L(.7)+c_->1.5-.604399+c_->.89765.
\tag{21}
\]
It suffices to treat \(b>.7\).
The core label increases, so at fixed source we decrease \(B\) until
axis 3 is at contact or \(B=0\). If \(B=0\) and there is slack,
increase \(b\); this lowers the cost and reduces the separating
margin because its derivative is \(-r\sin\phi-\cos\phi<0\).
At the outer diagonal with \(B=0\), the margin is negative, so
contact is reached before the outer endpoint.

On a contact with \(B>0\),
\[
 B=W-a\sin\phi+b\cos\phi .
\tag{22}
\]
The bounds \(\sin1.5>.997,\cos1.5<.071\) imply
\[
 B<1.0345-.899(.926)<.21.
\tag{23}
\]
At fixed \(b\),
\[
 B_\phi=-(a-1/2)\cos\phi-(b+1/2)\sin\phi<0.
\]
Writing \(g_B=.98439-.10668B\), its contact cost derivative satisfies
\[
 C_\phi
 =1+g_BB_\phi
 <1-[.98439-.10668(.21)](1.2)(.997)<0.
\tag{24}
\]
Thus increasing \(\phi\) toward \(\pi/2\) decreases the cost until
either the quarter angle or \(B=0\) is reached.

At \(B=0\), retain contact by changing \(b\). Implicit differentiation
gives
\[
 b_\phi=
 \frac{(a-1/2)\cos\phi+(b+1/2)\sin\phi}
      {r\sin\phi+\cos\phi}
 >\frac{1.2(.997)}{1.071}.
\tag{25}
\]
Since \(b>.7\), \(L'>.903\), and therefore
\[
 C_\phi=1-L'b_\phi
 <1-\frac{.903(1.2)(.997)}{1.071}<0.
\tag{26}
\]
This branch has increasing \(b\), remains below the diagonal
(the latter has a negative contact margin), and continues to the
quarter angle. Its terminal cost exceeds .89777 by the complete
aligned mixed-quarter theorem.

The reductions in this section exhaust positive slack, positive core
coordinate, and zero core coordinate. Equations (24) and (26) also
show that no unexamined endpoint can obstruct the continuation.

## 6. Both axes on the upper strip

Use (6). The source-arc derivative of axis 3 is
\(-rv+u<-.261(.995)+.1<0\); for axis 4 it is \(-r<0\).
As before, decrease \(B\) to contact or zero, and, at a zero with slack,
increase \(b\) to contact. The outer diagonal cannot block this step:
with \(B=0\), its respective margins are bounded by
\[
 (d-.5)(u+v)-.5<.4(1.1)-.5<0,\qquad
 d+a_Cu-W<.9+(7/12)(.1)-1<0.
\tag{27}
\]

### 6.1. Positive core coordinate, axis 3

The contact formula is
\[
 B=.5-(a-.5)v-(b-.5)u,
\qquad
 F:=-B=(a-.5)v+(b-.5)u-.5.
\]
Every contact has
\(B\le1.05-.899(.995)<.156\), so it remains on the side.
At fixed source,
\[
 F_x=-(a-.5)u+(b-.5)v
 \le\max(b-.5,0)<.4.
\]
Thus \(C_x=1-g_BF_x>1-.98439(.4)>0\).
Moving \(x\) down toward zero lowers the cost.

### 6.2. Positive core coordinate, axis 4

Here
\[
 F:=-B=\frac{a-.5}{v}-.5+(a_C-.5)\tan x.
\]
Every contact has \(B<(1.05-.899)/.995<.152\).
Also
\[
 F_x=\frac{(a-.5)u+1/12}{v^2}
 <\frac{.915(.1)+1/12}{.995^2}<.177.
\]
Again \(C_x>1-.98439(.177)>0\), so the cost decreases toward zero.

### 6.3. Zero core coordinate, axis 3

The contact is \(av+bu=W\). It has
\[
 a\le1.05/.995<1.056<a(.7),
\]
so \(b>.7\), \(r>1.2/1.556>.77\). Differentiating gives
\[
 b_x=\frac{-(a-.5)u+(b-.5)v}{rv-u}
      <\frac{.4}{.666}.
\]
Consequently
\[
 C_x=1-L'b_x>1-\frac{1.073(.4)}{.666}>0.
\tag{28}
\]
The same estimate holds if its numerator is negative.

### 6.4. Zero core coordinate, axis 4

The contact determines
\[
 a=.5+.5v-\frac{u}{12},\qquad
 a_x=-.5u-\frac v{12}\ge-.05-\frac1{12}.
\]
Using \(L'/r<3\) from (4),
\[
 C_x=1+(L'/r)a_x
 >1-3(.05+1/12)>0.
\tag{29}
\]
All four contact paths stay in the indicated coordinate bounds.
If a positive-\(B\) path reaches zero, continue on the corresponding
zero-\(B\) branch; equations (27)--(29) preclude a blocking outer
endpoint. They all arrive at \(x=0\) with no larger cost.
The aligned theorem gives a strict lower bound .89777 there.
This proves the upper strip. Equation (5) proves the remaining upper
angles.

## Conclusion

Section 3 handles every lower axis-4 side state, sections 4--5 handle
every lower axis-3 side state, and section 6 handles both upper-strip
axes. The other axes are impossible before the direct tail (5).
Hence every stated core-side transition has cost greater than .89765.
The separately proved core-corner theorem covers the remaining target
arc, with the common side/corner join included in both proofs.

## Exact arithmetic convention

The checker verifies
\(3.141592653589793238<\pi<3.141592653589793239\) using Machin's
identity and alternating arctangent sums. It brackets every displayed
square root by integer squaring and every sine and cosine by alternating
Taylor sums. It reconstructs (16)--(18) from rational polynomial
arithmetic, checks the two stated tail allowances and every printed
coefficient, and checks the fixed scalar comparisons used above.
The checker performs no optimization, interval subdivision, or
proof search.
