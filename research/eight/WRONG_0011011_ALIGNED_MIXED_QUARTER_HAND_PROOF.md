# The aligned mixed quarter-one transitions for 0011011

## Scope

This is a hand proof at the exact relative-frame angle \(\phi=\pi/2\).
It covers every mixed core/outer transition of edges 2 and 3, with the
permitted signs, and hence their reflected reverse transitions at edges 5
and 6. It proves the stronger strict bound
\[
 \phi+\sigma L_i^\sigma(a,b)-\tau L_{i+1}^\tau(A,B)>.89777>.89765.
\tag{1}
\]
It is **not** a proof for the nonaligned angle range.

All labels are exactly those in
\`proof_integration/wrong_0011011_labels.json\`, with denominator 100000.
No optimized or sampled value enters the proof. The accompanying checker
performs 85 fixed rational comparisons, including the displayed radical
brackets and the calculus bounds below.

Set
\[
 Q=9789/2500,\quad c=7/12,\quad
 d=\sqrt{Q/2}-1/2,\quad c_C=1/2+1/(12\sqrt2).
\]
An outer state is \((a(b),b)\), where
\[
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad 0\le b\le d.
\]
A core state lies on \(a=c,\ 0\le b\le1/2\), or on
\((a-1/2)^2+(b-1/2)^2=1/144,\ 1/2\le b\le c_C\).
Actual signed own-frame centers are \((a,-\sigma b)\).

## 1. Elementary bounds and aligned axis cover

Write
\[
 r=(b+1/2)/(a+1/2),\qquad r'=Q/(a+1/2)^3.
\]
Then \(a'=-r\), \(r''=3rr'/(a+1/2)\), and
\[
 .261<r\le1,\qquad r'>.557,\qquad
 .899<d<.9,\quad c_C<.559,\quad a(0)<1.415.
\tag{2}
\]
Let \(b_0=\sqrt{Q-9/4}-1/2\), so \(a(b_0)=1\). In particular
\[
 .790<b_0<.791,\quad a(0)-1<.415.
\tag{3}
\]

At \(\phi=\pi/2\), the two source/target secondary/primary axis pairs
coincide. The four retained separating projections are exactly
\[
 \sigma b+A-1,\quad \sigma b+A-1,\quad
 a-\tau B-1,\quad a-\tau B-1.
\tag{4}
\]
Thus all four signed-axis cases are included whenever both alternatives in
(4) are covered. A core coordinate is below .584, so several alternatives
are impossible immediately.

We repeatedly use the following elementary lemma. If \(f''\ge m>0\) on an
interval and \(x_0\) belongs to that interval, integration of the second
derivative gives
\[
 f(x)\ge f(x_0)+f'(x_0)(x-x_0)+\tfrac m2(x-x_0)^2
 \ge f(x_0)-f'(x_0)^2/(2m).
\tag{5}
\]
A concave function takes its minimum at an endpoint. If \(f'\) is concave
and positive at the left endpoint, \(f\) takes its minimum at one of the
two endpoints: its derivative can change from positive to negative at
most once.

The numerical brackets used below are proved by squaring:
\[
\begin{array}{c|cc}
\text{quantity}&\text{strict lower}&\text{strict upper}\\ \hline
a(0)&1.41457567100&1.41457567101\\
d&.89921406510&.89921406512\\
c_C&.55892556509&.55892556511\\
b_0&.79058126439&.79058126440\\
a(.898)&.90042707771&.90042707772\\
a(.5725)&1.16293227462&1.16293227464\\
a(.63)&1.12440758432&1.12440758433\\
a(.604)&1.14218878330&1.14218878331\\
a(.575)&1.16131724845&1.16131724846
\end{array}
\tag{6}
\]
The common \(\pi\) bound is \(\pi>3.14159\). For completeness it follows
from Machin's identity
\(\pi=16\arctan(1/5)-4\arctan(1/239)\): use the degree-seven alternating
lower sum for the first arctangent and \(1/239\) as the upper bound for
the second. The rational comparison with 3.14159 is strict.

## 2. Edge 2: outer source

The source sign is negative. Its unsigned outer label is
\[
 L(b)=.02478+.93015b+.02363b^2-.11055a(b)b.
\]
It satisfies
\[
 L'=.93015+.04726b-.11055(a-rb)>.773,\qquad
 L''=.04726+.11055(2r+br')>0.
\]
A useful global monotonicity is
\[
 (L'/r)'<0.
\tag{7}
\]
Indeed, multiplication by \(r^2\) gives
\[
 .04726(r-br')+.22110r^2-(.93015-.11055a)r'
 \le .04726+.22110-(.93015-.11055\cdot1.415).557<0.
\]
At \(b_0\), the brackets (6) give \(L'/r>1.08\).

The first alternative in (4), \(-b+A\ge1\), is impossible for a core
target. It remains to treat \(a-\tau B\ge1\).

### 2.1. Positive core target

The constraint \(a-B\ge1\) forces \(0\le B\le a-1<.415\), so the target
is on the core side and its label is
\[
 C_3^+(B)=-.01449+1.04240B.
\]
The cost decreases as \(B\) increases; choose \(B=a-1\).
Along this contact, its derivative with respect to \(B\) is
\(L'/r-1.04240>0\), because \(b\le b_0\). The minimum is therefore
\(B=0,\ a=1,\ b=b_0\). Its cost is
\[
 \pi/2-.01029-.81960b_0-.02363b_0^2>.89777.
\tag{8}
\]

### 2.2. Negative core target

The target label is
\[
 C_3^-(A,B)=.22042-.34492A+.98439B-.05334B^2.
\]
It is strictly increasing along the whole core boundary: on the side its
derivative exceeds \(.98439-.10668/2>0\), and on the corner the extra
term \(-.34492A'\) is nonnegative.

At each source state, minimize at \(B=\max(0,1-a)\). Since
\(1-d<.101\), this minimizer is on the side \(A=c\). Put
\[
 c_-:=.22042-.34492c.
\]
For \(b\le b_0\), the cost is \(\pi/2-L(b)+c_-\), decreasing to \(b_0\).
For \(b_0\le b\le d\), it is
\[
 G(b)=\pi/2-L(b)+c_-+.98439(1-a)-.05334(1-a)^2.
\]
Its second derivative is
\[
 G''=r'[\,.98439-.10668(1-a)-.11055b\,]
       -.22110r-.10668r^2-.04726.
\]
Here \(r'>1.16\), \(1-a<.101\), \(b<.9\), and \(r\le1\). Hence
\[
 G''>
 1.16[.98439-.10668(.101)-.11055(.9)]
 -.22110-.10668-.04726>.6.
\]
At \(b=.898\), (6) gives
\[
 G(.898)>.89778,\qquad |G'(.898)|<.0001.
\]
Consequently (5) gives
\[
 G>.89778-(.0001)^2/1.2>.89777.
\tag{9}
\]
This includes \(b_0\), the minimum of the first piece.

## 3. Edge 2: core source

The negative source label is
\[
 C_2^-(a,b)=.00125+1.03981b.
\]

### 3.1. Positive outer target

The second alternative in (4), \(a-B\ge1\), is impossible.
The first gives \(A-b\ge1\). Thus \(A\ge1\), \(b\le A-1<.415\), and
the core source is on the side. Its negative contribution is minimized
by \(b=A-1\).

The target label is
\[
 O_3^+(A,B)=-.01025A+.16031B+.63457AB.
\]
For \(0\le B\le b_0\), the contact cost is
\[
 H_2(B)=\pi/2+1.03856-1.02956A-.16031B-.63457AB.
\]
In outer coordinates,
\[
 H_2'=r(1.02956+.63457B)-(.16031+.63457A),\quad
 H_2''=r'(1.02956+.63457B)+1.26914r>.5.
\]
At \(B=.5725\),
\[
 H_2>.89778,\qquad |H_2'|<.0001.
\]
Equation (5) proves \(H_2>.89777\).

### 3.2. Negative outer target

No separating-axis information is required. The target label is
\[
 O_3^-=\ .01670+B[\,2.42322-.91744B-.95769A\,]\ge .01670,
\]
since its bracket is positive for \(B<.9,A<1.415\).
Also \(C_2^-<.583\). Therefore
\[
 \pi/2-C_2^-+O_3^->3.14159/2-.583+.01670>.89777.
\tag{10}
\]

## 4. Edge 3: direct cases and label monotonicity

Use the notation
\[
\begin{aligned}
 C_3^+&=-.01449+1.04240b,\\
 C_3^-&=.22042-.34492a+.98439b-.05334b^2,\\
 O_3^+&=-.01025a+.16031b+.63457ab,\\
 O_3^-&=.01670+2.42322b-.91744b^2-.95769ab,\\
 C_4^+&=.04970+.94831B,\qquad C_4^-=.16823+.62312B,\\
 V(B):=O_4^+&=.03965+3.85510B-1.49748B^2-1.89442AB,\\
 O_4^-&=-.02112A+.29090B+.44642AB.
\end{aligned}
\]

The elementary bounds
\[
 C_3^-<.58,\quad C_3^+>-.0145,\quad
 O_3^+>-.01451,\quad C_4^+<.58,\quad O_4^->-.03
\tag{11}
\]
follow immediately from (2). Thus all core-source cases with negative
outer target and all positive-outer-source cases already exceed .89777,
regardless of the separating axis.

We also need that \(O_3^-\) and \(V\) increase on the whole outer arc.
For \(T(B)=C+qB-DB^2-eAB\), the derivative is
\[
 T'=q-2DB-e(A-rB).
\]
Integrating \(r'>.557\) and using \(r(0)>.261\), \(a(0)<1.415\) gives
\[
 A-rB<1.415-.522B-\tfrac32(.557)B^2.
\]
Consequently
\[
 T'>q-1.415e+(.522e-2D)B+\tfrac32(.557)eB^2.
\tag{12}
\]
The minimum of this explicit quadratic is greater than .5 for
\(O_3^-\), and greater than .53 for \(V\). These are two exact rational
square-completion comparisons. At the diagonal \(O_3^-(d,d)<.68\).
Thus the negative-outer-source/negative-core-target case also has
\[
 \pi/2-O_3^-+C_4^->3.14159/2-.68+.16823>.89777.
\]

Only three aligned contact functions remain.

## 5. Edge 3: positive core source, positive outer target

The second alternative in (4) is impossible. The first is \(A+b\ge1\).
Since \(C_3^+\) increases, choose \(b=\max(0,1-A)\); this is always on
the side because \(1-d<.101\).

For \(B\le b_0\), the cost is \(\pi/2-.01449-V(B)\), decreasing by
(12), so its minimum is at \(b_0\). For \(B\ge b_0\), put
\[
 J(B)=\pi/2-.01449+1.04240(1-A)-V(B).
\]
Then
\[
 J''=2.99496-3.78884r+r'[1.04240-1.89442B].
\]
For \(B\ge b_0\), \(r>.86,\ r'>1.16,\ B>.790\), and the square bracket
is negative. Therefore
\[
 J''<
 2.99496-3.78884(.86)+
 1.16[1.04240-1.89442(.790)]<0.
\]
Endpoint evaluation by (6) gives
\[
 J(b_0)>.9025,\qquad J(d)>.89779.
\]
Concavity covers the whole interval and proves (1).

## 6. Edge 3: negative core source, positive outer target

Again only \(A-b\ge1\) is possible. Since \(C_3^-\) increases on the
core boundary, maximize \(b=A-1\); this forces the core side and
\(0\le B\le b_0\). The contact cost is
\[
 H_3(B)=\pi/2-c_--.98439(A-1)+.05334(A-1)^2-V(B).
\]
Set \(T=1.09107-.10668A-1.89442B\). Direct differentiation gives
\[
\begin{aligned}
 H_3'&=-3.85510+2.99496B+1.89442A+rT,\\
 H_3''&=2.99496-3.78884r+.10668r^2+r'T,\\
 H_3'''/r'&=-5.68326+.32004r+\frac{3rT}{A+1/2}.
\end{aligned}
\]
Since \(r\le1,\ T\le1.09107,\ A+1/2>1.399\),
\[
 H_3'''/r'<-5.68326+.32004+\frac{3(1.09107)}{1.399}<0.
\tag{13}
\]
Thus \(H_3''\) decreases. At the fixed point \(B=.63\), (6) gives
\[
 H_3''(.63)>.2,\qquad H_3'(.63)>0.
\]
On \(0\le B\le.63\), apply (5) with \(m=.2\) and \(B=.604\):
\[
 H_3(.604)>.897788,\qquad |H_3'(.604)|<.000013.
\]
Its resulting lower bound exceeds .89777.
On \([.63,b_0]\), (13) says that \(H_3'\) is concave and positive at
the left endpoint; the endpoint-minimum observation after (5) applies.
The left endpoint is already covered, while
\(H_3(b_0)>.8978\). This proves the complete interval.

## 7. Edge 3: negative outer source, positive core target

The first alternative in (4), \(-b+A\ge1\), is impossible. The second
forces \(B\le a-1<.415\), so the core target is on the side. The cost
decreases in \(B\), hence choose \(B=a-1\), with \(0\le b\le b_0\):
\[
 K(b)=\pi/2+.89861-.94831a-O_3^-(a,b).
\]
Differentiation yields
\[
 K''=1.83488-1.91538r+r'(.94831-.95769b).
\]
On this interval \(r<.861,\ b<.791,\ r'>.557\); the last factor is
positive. Hence
\[
 K''>1.83488-1.91538(.861)+
 .557[.94831-.95769(.791)]>.29.
\]
The fixed test \(b=.575\) gives
\[
 K>.9008,\qquad |K'|<.003.
\]
Equation (5) gives a uniform lower bound
\(.9008-.003^2/.58>.89777\).

## 8. Coverage

For edge 2 the source sign is negative: sections 2.1, 2.2, 3.1 and 3.2
cover both kinds and both target signs. For edge 3, section 4 covers
the two core-source/negative-target cases, the two positive-outer-source
cases, and the negative-outer-source/negative-target case. Sections 5,
6 and 7 cover the remaining three cases. Formula (4) either identifies
the chosen contact or makes the other two axes impossible. Thus all
twelve permitted mixed kind/sign combinations, each with all four
retained separating axes, are covered at \(\phi=\pi/2\).

Reflection followed by source/target reversal preserves both the
relative frame angle and the corrected cost and maps these transitions
to their partners at edges 5 and 6. No symmetry of an individual role's
positive and negative labels is assumed.
