# 0011011: the whole opposite-sign outer edge-2 quarter row

**Theorem.** For edge 2 with a negative outer source and positive outer
target, every retained separator and every
\[
 \pi/2-.7\le\phi\le\pi/2+.7
\]
give corrected cost \(C>.89777>\gamma=.89765\).
Reflected reversal gives the edge-6 partner.

The proof treats all eight half-axis regimes. Its nontrivial reductions
are monotone contact flows, a compact-minimum derivative argument, one
axial scalar with positive curvature, and four short tables evaluating
explicit one-variable derivative bounds. The companion uses fixed
rational arithmetic only.

## 1. Coordinates, labels, and elementary derivatives

All decimals are exact rationals. Write
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\tfrac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad a_0=a(0),
\]
\[
 b_1=\sqrt{Q-\tfrac94}-\tfrac12,\qquad a(b_1)=1,
 \qquad A=a(B),\quad 0\le b,B\le d.
\]
Thus \(.899<d<.9,\ .7905<b_1<.791,\ a_0<1.415\).
The exact labels and cost are
\[
\begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055a(b)b,\\
 R(B)&=-.01025A+.16031B+.63457AB,\\
 C&=\phi-P(b)-R(B).
\end{aligned}                                                     \tag{1}
\]
With \(s=\sin\phi,c=\cos\phi,W=(1+s+|c|)/2\), the four projections are
\[
 -b+As-Bc,\quad -ac-bs+A,\quad as-bc-B,\quad a-Ac-Bs.               \tag{2}
\]
At least one is at least \(W\).

For \(F(b)=c_0+pa+qb+rb^2+tab\), put
\(u=a+1/2,\rho=(b+1/2)/u\). Then
\[
\begin{aligned}
 F'&=-p\rho+q+2rb+t(a-b\rho),\\
 F''&=2r-2t\rho-(p+tb)Q/u^3,\\
 F'''&=-3Q\{tQ+(p-t/2)(b+1/2)\}/u^5.
\end{aligned}                                                     \tag{3}
\]
These formulas and endpoint comparisons give
\[
 .773<P'<.973,\quad P''>0,\quad P''(.415)<.197,\quad P''(b_1)<.345,
                                                                    \tag{4}
\]
\[
 R'>0,\quad R''<0,\quad R'''<0,\quad
 R'<1.061,\quad R'(.415)>.82.                                     \tag{5}
\]
The derivative \(P''\) increases. Its third derivative also increases,
as follows from \(Q\{5(b+1/2)-1/2\}-2(b+1/2)^2>0\).
For (5), the brace in the final formula of (3) is positive.
A direct global bound
\(-2(.63457)(.261)+.01025Q/(d+1/2)^3<0\) proves \(R''<0\).
Positivity of \(R'(d)\) and its maximum at zero give the other claims.

It is useful to regard the negative source label as a function of the
primary coordinate:
\[
 M(a)=-P\!\left(\sqrt{Q-(a+\tfrac12)^2}-\tfrac12\right).
\]
Writing \(u=a+1/2,\ w=\sqrt{Q-u^2}\), one obtains
\[
 M''=.04726+\frac{Q(.961795-.11055u)}{w^3}-.2211\frac u w,
 \quad
 M'''=\frac{3Q(.961795u-.11055Q)}{w^5}>0.
\]
Consequently
\[
 M''>.979,\qquad M'>.972,\qquad 1.083<M'(1)<1.084.                 \tag{6}
\]
Both \(M\) and \(M'\) increase.

The corresponding function \(N(A)=-R(B(A))\) also increases and is convex.
Indeed, writing \(r_B=(B+1/2)/(A+1/2)\),
\[
 N'=\frac{R'}{r_B},\qquad
 \frac{N''}{N'}=-\frac{R''}{R'r_B}+\frac{r_B'}{r_B^2}>0.           \tag{7}
\]

## 2. The two aligned contacts

Axes 1 and 2 at \(\phi=\pi/2\) require \(A-b\ge1\).
Since both labels increase, reduce to \(b=A(B)-1\), \(0\le B\le b_1\).
For
\[
 H(B)=\pi/2-P(A(B)-1)-R(B)
\]
one has
\[
 H''=-P''r_B^2+P'r_B'-R''
 >-.197+.773\,Q/(a_0+1/2)^3>.2.
\]
At \(B=.6581\), \(H>.9091246,\ |H'|<10^{-5}\).
Completing a square therefore gives
\[
 H>.9091246-\frac{10^{-10}}{.4}>.9091.                            \tag{8}
\]
The axial endpoint separately satisfies
\(\pi/2-P(0)-R(b_1)>.9278\).

Axes 3 and 4 at alignment require \(a-B\ge1\).
Their contact cost, in the target variable, is
\[
 \pi/2+M(1+B)-R(B),\qquad0\le B\le a_0-1.
\]
It increases, because \(M'(1+B)>1.083>1.061>R'(B)\).
Thus
\[
 \pi/2-P(b_1)-R(0)>.8977861.                                    \tag{9}
\]

## 3. A common axial contact curve

Several boundary flows below use
\[
 (a(z)-\tfrac12)\cos x-(z+\tfrac12)\sin x=\tfrac12.
\]
Define
\[
 Z=\tfrac12+\cos x,\quad Y=\sqrt{Q-Z^2},\quad
 U=Z\cos x+Y\sin x,\quad V=Y\cos x-Z\sin x,\quad z=V-\tfrac12.
\]
Then \(U=a(z)+1/2\) and
\[
 f=1-\frac{\sin x}{Y},\qquad
 U'=Vf,\quad V'=-Uf,\quad
 f'=\frac{\tfrac12+(1.25-Q)\cos x+\tfrac12\cos^2x}{Y^3}<0.        \tag{10}
\]
The curve starts at \(z=b_1,x=0\) and decreases to \(z=0\) before
\(x=.571\). Here \(f>0\).
The magnitude \(-f'\) decreases with \(x\): its positive numerator
\((Q-1.25)\cos x-\tfrac12-\tfrac12\cos^2x\) decreases, while \(Y\)
increases.

For
\[
 J(x)=\pi/2-x-P(0)-R(z(x)),
\]
the following three fixed bounds hold:
\[
\begin{array}{c|r}
 x\text{ interval}&\text{lower bound for }J''\\ \hline
 [0,.1]&2.25\\
 [.1,.2]&1.39\\
 [.2,.3]&.66
\end{array}.                                                       \tag{11}
\]
They follow directly from
\[
 z'=-Uf,\quad z''=-Vf^2-Uf',\quad J''=-R''(z)(z')^2-R'(z)z''.
\]
For a row \([l,h]\), use the lower speed \(U(l)f(h)\), the upper second
derivative \(-V(h)f(h)^2-U(h)f'(l)\), and the endpoint label derivatives
at \(z(h)\). The latter point gives the smallest \(-R''\) and the largest
\(R'\). These substitutions are exactly the three rational rows (11).

At \(x=.15017\),
\[
 J>.8977853,\qquad |J'|<10^{-5}.
\]
Thus throughout \([0,.3]\),
\[
 J>.8977853-\frac{10^{-10}}{1.32}>.89778.                          \tag{12}
\]
For \(x\ge.3\), the fixed bounds
\[
 U>1.786,\quad V<.851,\quad f<.78,\quad -f'>.45
\]
give \(z''>1.786(.45)-.851(.78)^2>0\).
Hence \(Uf=-z'\) decreases and remains greater than its value at
\(.571\), which exceeds \(1.203\). Also
\(R'(z)\ge R'(z(.3))>.875\), so
\[
 J'=-1+R'(z)Uf>-1+.875(1.203)>0.                                \tag{13}
\]
Equations (12)--(13) bound the complete axial curve.

## 4. A common upper-angle zero-coordinate exit

For \(b_1\le z\le d\), consider
\[
 (a(z)-\tfrac12)\cos x+(z-\tfrac12)\sin x=\tfrac12,
 \qquad0\le x\le.7.                                             \tag{14}
\]
Any such root has \(x<.4\).
Indeed the left side is concave separately in \(z\) and \(x\);
at \(z=b_1,d\) and \(x=.4,.7\), all four endpoint values exceed \(1/2\).
Implicit differentiation at a root gives
\[
 x_z=
 \frac{r_z\cos x-\sin x}
      {(z-\tfrac12)\cos x-(a(z)-\tfrac12)\sin x}>1.                \tag{15}
\]
For this last estimate, \(r_z>.86,\ \cos x>.921,\ \sin x<.39\).
The denominator is positive, since it exceeds
\(.2905(.921)-.5(.39)>0\), and is at most \(.4\).
The numerator exceeds \(.86(.921)-.39>.4\).

Therefore both \(x-P(z)\) and \(x-R(z)\) increase along (14):
\(P'<.973<1\), while \(R'(z)\le R'(b_1)<.4\).
Any exit cost of these two forms is bounded by its aligned endpoint
\(z=b_1,x=0\).

## 5. Axis 1

Put \(\phi=\pi/2-x\) on the lower half.
This axis requires
\[
 b\le (A-\tfrac12)\cos x-(B+\tfrac12)\sin x-\tfrac12.              \tag{16}
\]
Since \(P\) increases, maximize \(b\) to equality. In particular
\(b\le A-1<a_0-1<.415\).
For the contact speed
\(v=(A-\tfrac12)\sin x+(B+\tfrac12)\cos x\),
\[
 v^2=Q-2A-(b+\tfrac12)^2
       \le Q-(b+\tfrac32)^2.
\]
The function \(P'(b)\sqrt{Q-(b+3/2)^2}\) decreases on this interval:
its derivative has the sign of
\[
 P''\{Q-(b+\tfrac32)^2\}-P'(b+\tfrac32)
 <.197(Q-2.25)-.773(1.5)<0.
\]
Its value at \(b=0\) is less than 1.
Thus the contact cost has \(C_x=-1+P'v<0\).
Increasing \(x\) lowers the cost until \(b=0\); (16) reaches that boundary
before \(.571\). The complete boundary is Section 3, proving the lower
half.

On the upper half, the contact is
\[
 b=(A-\tfrac12)\cos x+(B-\tfrac12)\sin x-\tfrac12.
\]
It is always below \(d\), since it is at most
\(\sqrt{Q-2a_0}-1/2<d\). Its height above \(-1/2\) is positive
throughout the interval: for \(B\ge1/2\) both coefficients are positive;
for \(B\le1/2\), it exceeds \(.7\cos(.7)-.5\sin(.7)>0\).
The contact derivative satisfies
\(C_x=1-P'b_x>1-.973(.4)>0\).
The nonnegative contact set is an interval, by concavity in \(x\).
Decreasing \(x\) therefore reaches alignment or \(b=0\).
Alignment is (8); if \(B>b_1\), the axial exit is (14) and is bounded by
its aligned endpoint by (15). This completes axis 1.

## 6. Axis 2 on the lower half

The least target primary coordinate is
\[
 A=\tfrac12+(a+\tfrac12)\sin x+(b+\tfrac12)\cos x.                 \tag{17}
\]
It increases with \(x\), so \(A\ge1+b\) and \(b<.415\).
Write \(Y=(a+1/2)\cos x-(b+1/2)\sin x>0\).
For the contact cost \(\pi/2-x-P(b)+N(A)\),
\[
 C_b=-P'+N'Y/(a+1/2),\qquad C_x=-1+N'Y.
\]
At a stationary source coordinate,
\[
 C_x=-1+(a+\tfrac12)P'>-1+1.75(.773)>0.                          \tag{18}
\]
On the target endpoint \(A=a_0\), implicit differentiation gives
\(b_x=-(a+1/2)\), hence the same positive derivative.
The source diagonal is impossible because \(A\ge1+b\le a_0\).
Consequently a compact minimum reduces to alignment or the axial source
\(b=0\).

On that axial source, \(A=\tfrac12+(a_0+\tfrac12)\sin x+\tfrac12\cos x\).
For \(x\le.02\),
\[
 C\ge\pi/2-.02-P(0)-R(b_1)>.9078.
\]
For \(x\ge.02\), let \(Y=\sqrt{Q-(A-.5)^2}\).
On the relevant range \(1\le A\le a_0\), (7) gives
\[
 N''/N'>\frac Q{1.915(1.291)^2}>1.22.
\]
Thus \(N'Y\) increases in \(A\), because
\(1.22\{Q-(.915)^2\}-.915>0\).
Its value at \(x=.02\) exceeds 1, so the axial cost thereafter increases.
This proves the entire lower half.

## 7. Axis 2 on the upper half

The active contact is
\[
 A=\tfrac12+(b+\tfrac12)\cos x-(a-\tfrac12)\sin x.                 \tag{19}
\]
If the right side is below \(d\), the minimizing target is \(A=d\).
Such an inactive part can be reduced to contact by increasing \(b\):
the cost decreases, and the right side is strictly increasing in \(b\)
and exceeds \(d\) at \(b=d\).

Put \(u=a+1/2,r=(b+1/2)/u\),
\[
 k=\cos x+r\sin x,\qquad
 v=(b+\tfrac12)\sin x+(a-\tfrac12)\cos x.
\]
The following uniform bound will control all possible minima:
\[
 P'(b)\frac vk<1.                                                \tag{20}
\]
Indeed \(v/k=u-\cos x/(\cos x+r\sin x)\), which increases in \(x\).
At \(x=.7\), five fixed endpoint substitutions give
\[
\begin{array}{c|r}
 b\text{ interval}&\text{upper bound for }P'v/k\\ \hline
 [0,.3]&.966\\
 [.3,.5]&.973\\
 [.5,.7]&.993\\
 [.7,.8]&.933\\
 [.8,.9]&.924
\end{array}.
\]
For each row, use the values of \(P'\) and \(r\) at the right \(b\)
endpoint, and the value of \(u\) at the left \(b\) endpoint, in
\(P'\{u-\cos(.7)/(\cos(.7)+r\sin(.7))\}\).

At an interior source stationary point,
\(C_b=-P'+N'k=0\), so \(C_x=1-N'v=1-P'v/k>0\).
At the endpoint \(b=d\), a minimizing point has \(C_b\le0\), giving the
same strict inequality.
On either target endpoint \(A=d\) or \(A=a_0\), the contact has
\(b_x=v/k\), so its cost derivative is again positive by (20).

Only the axial source \(b=0\) remains.
Its active target coordinate is at most 1.
Convexity of \(N\) gives \(N'\le N'(1)<.44\), and
\(v<\sqrt{(a_0-.5)^2+.25}<1.043\).
Thus \(C_x>1-.44(1.043)>0\); the inactive clamped portion has derivative 1.
Every potential minimum therefore reduces to alignment, proving this
half by (8).

## 8. Axis 3 on the lower half

Here
\[
 B\le (a-\tfrac12)\cos x-(b+\tfrac12)\sin x-\tfrac12.              \tag{21}
\]
Use equality because \(R\) increases. Always \(b\le b_1\) and
\(B<a_0-1<.415\).

First consider \(0\le x\le.01\).
Writing \(k=r_b\cos x+\sin x\), the second source derivative of the
contact cost is
\[
 C_{bb}=-P''-R''k^2+R'r_b'\cos x
 >-.345+.82\,Q\cos(.01)/(a_0+.5)^3>.1.
\]
At the largest feasible \(b\), the target is \(B=0\), and Section 3's
curve gives \(b>.775\).
There \(P'>.9269\), \(r_b<.861\), and
\[
 C_b=-P'+R'(0)k<-.9269+1.061(.871)<0.
\]
Thus the cost decreases throughout its source interval and its minimum
is on \(B=0\).
On that boundary, \(-b'=Uf>1.488\), so
\(C_x>-1+.9269(1.488)>0\).
The short strip therefore reduces to (9).

For \(.01\le x\le.7\), use
\[
 P(b)\le P(0)+g b,\quad g=.83829,
 \qquad R(B)\le R(0)+h B,\quad h=1.061.
\]
The first inequality is the chord on \([0,b_1]\);
the second follows from concavity and \(R'(0)<h\).
Substitution of (21) followed by the full-circle support inequality gives
\[
 C\ge F(x):=
 \pi/2-x-P(0)-R(0)
 -\sqrt Q\sqrt{g^2+h^2-2gh\sin x}
 +h\cos x+\tfrac12(g+h).                                        \tag{22}
\]
Put \(n=\sqrt{g^2+h^2-2gh\sin x}\).
The exact second derivative is
\[
 F''=-h\cos x-\frac{\sqrt Q\,gh\sin x}{n}
                   +\frac{\sqrt Q\,g^2h^2\cos^2x}{n^3}.
\]
Seven fixed endpoint bounds prove concavity:
\[
\begin{array}{c|r}
 x\text{ interval}&F''\text{ upper bound}\\ \hline
 [.01,.1]&-.33\\
 [.1,.2]&-.31\\
 [.2,.3]&-.29\\
 [.3,.4]&-.25\\
 [.4,.5]&-.19\\
 [.5,.6]&-.11\\
 [.6,.7]&-.015
\end{array}.                                                       \tag{23}
\]
For a row \([l,h]\), use \(\cos h\) in the first negative term,
\(\sin l/n(l)\) in the second, and \(\cos^2l/n(h)^3\) in the positive
term. These are the displayed rational comparisons.
Finally \(F(.01)>.8982,\ F(.7)>.986\), so (22) proves the whole tail.

## 9. Axis 3 on the upper half

The contact is
\[
 B=(a-\tfrac12)\cos x+(b-\tfrac12)\sin x-\tfrac12.
\]
As in Section 5, it is below \(d\) and is concave throughout the angle
interval, so its nonnegative domain is an interval.
Since \(B_x\le.4\), its cost derivative satisfies
\(C_x>1-1.061(.4)>0\).
Decreasing \(x\) reaches alignment, bounded by (9), or the zero target.
The latter is the common curve (14), with label \(P\); (15) reduces it
to the same aligned endpoint. This covers the upper half.

## 10. Axis 4 on the lower half

The least source primary coordinate is
\[
 a=\tfrac12+(A+\tfrac12)\sin x+(B+\tfrac12)\cos x.
\]
It increases with \(x\), starts at \(1+B\), and has
\[
 a_x^2=Q-(a-\tfrac12)^2>Q-(.915)^2.
\]
By (6),
\[
 C_x=-1+M'a_x>-1+.972\sqrt{Q-(.915)^2}>0.
\]
Decreasing \(x\) stays feasible and reaches alignment, proving this
half by (9).

## 11. A uniform target-ratio lemma

The last half-axis uses the following one-variable bound.
For a target state \(A=a(B)\), put
\[
 u=A+\tfrac12,\quad v=B+\tfrac12,\quad
 q=Q+1-2u,\quad z=d-\tfrac12,\quad K=\sqrt{q-z^2},
\]
and
\[
 \mathcal F(B)=\frac{Q-u}{u q}+\frac{vz}{u qK}.
\]
Then
\[
 \mathcal F(B)>R'(B)\qquad(0\le B\le d).                         \tag{24}
\]
At zero, \(\mathcal F(0)-R'(0)>.001\).
To verify that the difference increases, let \(r=v/u\).
Direct differentiation gives
\[
 \mathcal F'
 =-r\,\frac{4Qu-2u^2-Q(Q+1)}{u^2q^2}
   +\frac z{qK}\left\{\frac Q{u^3}-\frac{2r^2}q-\frac{r^2}{K^2}\right\}.
                                                                    \tag{25}
\]
Five endpoint interval substitutions give
\[
\begin{array}{c|r}
 B\text{ interval}&\text{lower bound for }\mathcal F'-R''\\ \hline
 [0,.2]&.05\\
 [.2,.4]&.21\\
 [.4,.6]&.47\\
 [.6,.8]&.89\\
 [.8,.9]&1.65
\end{array}.                                                       \tag{26}
\]
For each row, enclose \(u,r,q,K\) by their endpoint intervals.
The numerator \(4Qu-2u^2-Q(Q+1)\) increases in \(u\).
Use the left endpoint value of the decreasing function \(R''\)
as its upper bound. Formula (25) then yields exactly the five positive
rational comparisons (26). This proves (24).

## 12. Axis 4 on the upper half

The active source coordinate is
\[
 a_*=\tfrac12+(B+\tfrac12)\cos x-(A-\tfrac12)\sin x,
 \qquad a=\max(d,a_*).                                          \tag{27}
\]
It increases with \(B\), and its value at \(B=d\) is greater than \(d\)
even at \(x=.7\). On an inactive part \(a_*<d\), increasing \(B\)
decreases the cost until contact. Thus it suffices to consider the
active contact and its boundary.

Write
\[
 k=\cos x+r_B\sin x,\qquad
 v=(B+\tfrac12)\sin x+(A-\tfrac12)\cos x.
\]
For every active contact,
\[
 R'(B)\frac vk<1.                                                \tag{28}
\]
To see this, \(v/k=u-\cos x/(\cos x+r_B\sin x)\) increases with \(x\).
Its largest allowed value occurs no later than the contact \(a_*=d\).
At that contact, \(v=K=\sqrt{q-z^2}\), and solving the two rotated
coordinate equations gives \(k/K=\mathcal F(B)\).
Equation (24) proves (28). This argument remains valid when the
comparison contact \(a_*=d\) lies beyond \(x=.7\), since it only enlarges
the upper bound.

For an interior stationary target coordinate,
\(C_B=M'k-R'=0\), so \(C_x=1-M'v>0\) by (28).
At the endpoint \(B=d\), a minimizing point has \(C_B\le0\), which gives
the same conclusion.
On either source endpoint \(a=d\) or \(a=a_0\), implicit differentiation
gives \(B_x=v/k\); its boundary cost derivative is positive by (28).

The final endpoint \(B=0\) can be handled directly.
Its active source primary coordinate lies in \([d,1]\).
Let \(q_0=Q-2a_0\); the speed obeys
\(v^2\le q_0-(a-1/2)^2\).
Using (6), the product \(M'(a)\sqrt{q_0-(a-1/2)^2}\) increases, since
\[
 .67(q_0-.25)-1.084(.5)>0.
\]
At \(a=1\), its value is \(M'(1)(a_0-.5)<1\).
Thus the endpoint cost increases with \(x\), including the inactive
clamped part, whose derivative is 1. It reduces to (9).

The compact-minimum argument now covers every contact and all its
boundary components, including the upper angle endpoint. This completes
the last half-axis and the whole row.

All scalar reference points and table entries are enclosed using
integer-square bounds and adjacent alternating Taylor sums.
The companion derives its \(\pi/2\) interval directly from the Machin
identity. Every final lower bound is strict.

