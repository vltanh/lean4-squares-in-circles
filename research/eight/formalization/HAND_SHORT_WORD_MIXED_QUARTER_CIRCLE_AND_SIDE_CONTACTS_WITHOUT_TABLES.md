# Mixed quarter-one circle supports and positive-core contacts without tables

This note replaces Sections 3.2 and 6 of
../SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md. It proves their complete
continuous domains: every positive-target core-to-outer secondary row,
and every positive-core-target outer-to-core primary row, on both entire
angle halves. The exact labels, weak original separators, both core
pieces, and the parent's pointwise source-sign dominance are retained.

All terminating decimals are exact rationals. Row indices refer to the
explicit normalized coefficient definitions in Section 1 of the parent;
they are intrinsic signed role cases, not coordinate cells. No scalar
angle table, coefficient-sign appendix, or verifier status is a premise.

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad
 a_c=7/12,\quad d_c=1/2+\sqrt2/24.
\]
The angle is \(\phi=\pi/2\pm x\), \(0\le x\le.7\).
We use \(\cos x>.764\), \(\sin x<.645\), \(R<1.978788\), and
\(d_c<.559\), each proved by the ordinary positive-square or alternating
Taylor comparisons.

## 1. Core-to-positive-outer secondary rows

The normalized cost and original source-secondary separator are
\[
 C=\phi+c+\sigma gb-pA-qB,\qquad
 \sigma b+A\sin\phi-B\cos\phi\ge W,
 \quad W=(1+\sin\phi+|\cos\phi|)/2.
\tag{1}
\]
The source lies on either core piece; the target lies on the outer arc.
Use the following single constant multiplier for each intrinsic row:
\[
\begin{array}{c|rrrrrrr}
 i&1&2&3&5&6&7&10\\ \hline
 \lambda_i&.6275&1.13855&1.115&.95269&1.04073&1.0853&.58829
\end{array}
\]
\[
\begin{array}{c|rrrrrrr}
 i&13&14&15&18&20&21&22\\ \hline
 \lambda_i&.99173&.95269&.95324&.99195&1.1014&1.1274&.95324.
\end{array}
\tag{2}
\]
The source remainder after subtracting the separator is
\(\sigma(g-\lambda)b\ge0\). Whole-circle target support therefore gives,
with \(s=\sin x,k=\cos x\),
\[
\begin{aligned}
 C&\ge F_-(x)=\pi/2-x+c+(\lambda+p+q)/2+\lambda k-RN_-(x),\\
 C&\ge F_+(x)=\pi/2+x+c+(\lambda+p+q)/2+\lambda(k+s)-RN_+(x),\\
 N_\pm^2&=p^2+q^2+\lambda^2+2\lambda(pk\pm qs).
\end{aligned}
\tag{3}
\]
Let \(N_0^2=(p+\lambda)^2+q^2\). All fourteen tuples satisfy
\(p+.764\lambda>.38\), so both norms are strictly positive.
Define the constant
\[
 D=\begin{cases}N_0^2-\lambda p,&p\ge0,\\
 N_0^2+2\lambda|p|/1.764,&p<0.\end{cases}
\]
Direct substitution of the exact parent coefficients and (2) proves
\[
\begin{gathered}
 2\lambda q-.645D>.31,\qquad4\lambda-RN_0>.27,\\
 .764N_0^2-\lambda q-
   \lambda\max(0,-p)\frac{.645}{1.764}>.09.
\end{gathered}
\tag{4}
\]
These are fixed coefficient comparisons, not angle or state values.
The first and third are rational; the second follows by positive squaring.

The exact identity
\[
 N_-^2-N_0^2k^2=N_0^2s^2-2\lambda p(1-k)-2\lambda qs
\]
and \(1-k\ge s^2/2\) for the nonnegative-p case, or
\(1-k=s^2/(1+k)<s^2/1.764\) for the negative-p case, imply
\[
 N_-^2-N_0^2k^2\le s(Ds-2\lambda q)\le0,\qquad N_-\le N_0k.
\tag{5}
\]
Similarly,
\[
 N_+^2-N_0^2(k+s)^2
 =2\lambda p(k-1)+2\lambda qs-2N_0^2ks.
\]
The first term is nonpositive when \(p\ge0\). Otherwise it is at most
\(2\lambda|p|s^2/1.764\). The last comparison in (4) proves
\[
                              N_+\le N_0(k+s).
\tag{6}
\]
For either norm, direct differentiation gives
\[
 N_\pm''+N_\pm/4=
   \frac{(p^2+q^2-\lambda^2)^2}{4N_\pm^3}\ge0.
\]
Consequently both entire angle halves have strictly concave supports:
\[
 F_-''\le k(-\lambda+RN_0/4)<0,\qquad
 F_+''\le(k+s)(-\lambda+RN_0/4)<0.
\tag{7}
\]

For a negative source on the lower half, its actual separator forces
\(\phi>1\): its margin is at most
\((a_0-1/2)\sin\phi-(1/2)\cos\phi-1/2\), which increases and is
negative at 1. A positive source uses the whole lower half.
Thus its original lower angular endpoint is 1 or \(\pi/2-.7\), respectively.
Substitution in (3) gives \(F_\pm(0)>.89809\); every applicable lower-half
terminal value exceeds .9065, and every upper-half terminal value
\(F_+(.7)\) exceeds 1.19. These are endpoints of functions already
proved concave over their full domains. Hence every row in (2) has
\(C>.898\) throughout, without any intermediate-angle concavity test.

## 2. Outer-to-positive-core primary contacts

After the parent's pointwise source-sign comparison, the eight required
rows have negative source sign, with cost and stipulated separator
\[
 C=\phi+c+pa-qb-gB,\qquad
 a-A\cos\phi-B\sin\phi\ge W.
\tag{8}
\]
The source is outer and the target core. The exact \((i;c,p,q,g)\) data are
\[
\begin{aligned}
 &(2;-.06772,.09133,.88074,1.04729),\\
 &(3;.80483,-.51554,1.19909,1.13855),\\
 &(6;-.25931,.19335,.76744,.99195),\\
 &(7;.01449,0,.86884,1.04073),\\
 &(14;.20507,-.20967,.83048,.95324),\\
 &(15;.21731,-.21826,.83472,.95269),\\
 &(20;-.21837,.18602,.80996,1.08816),\\
 &(21;.07651,0,.94766,.99173).
\end{aligned}
\tag{9}
\]
All have \(p/q<.253\), \(q\ge.76744\), and \(g\le1.13855\).
The source label in primary coordinates is
\[
 M(a)=pa-q\left(\sqrt{Q-(a+1/2)^2}-1/2\right),
\]
\[
 M'=p+q\frac{a+1/2}{\sqrt{Q-(a+1/2)^2}}>0,\qquad
 M''=\frac{qQ}{[Q-(a+1/2)^2]^{3/2}}>0.
\tag{10}
\]
Here positivity holds on the source range used below, in particular
\(a\ge1\) on every lower-half contact.

### 2.1. The whole lower-half contact domain

Write \(\phi=\pi/2-x\). A core-corner target, including the side join,
would force
\[
 a\ge1/2+(d_c+1/2)\sin x+\cos x\ge3/2>a_0.
\]
The middle inequality follows from concavity and its two endpoints on
\([0,.7]\). Thus every feasible target is on the side \(A=7/12\).
Put \(c_0=13/12\). Reducing the increasing source cost gives contact
\[
 a=1/2+c_0\sin x+(B+1/2)\cos x\ge1>d.
\tag{11}
\]
The angle ends at the unique axial event \(x_m\), where (11) with
\(B=0\) reaches \(a_0\). This height increases with \(x\), and its
value at .442 exceeds \(a_0\). Thus \(x_m<.442\).
Every feasible lower-half contact therefore has
\[
 k=\cos x>.903,\quad s=\sin x<.428,\quad h=c_0k-s/2>.764.
\]
At fixed angle its cost is strictly convex in \(B\):
\[
 C_B=M'(a)k-g,\qquad C_{BB}=M''(a)k^2>0.
\tag{12}
\]
The upper target endpoint is \(a=a_0\), not the infeasible side join
\(B=1/2\). At that endpoint, its target derivative is positive because
\[
 [p+2q(a_0+1/2)]k-g
 >[-.51554+2(.76744)(1.914)](.903)-1.139>0.
\]
Thus the contact minimum is axial or is the unique interior solution
of \(M'(a)k=g\).

### 2.2. Uniform axial curvature

On the axial target put
\[
 U=1+c_0s+k/2,\quad V=\sqrt{Q-U^2},\quad
 K(x)=\pi/2-x+c+p(U-1/2)-q(V-1/2).
\]
Then \(U'=h>0\), \(h^2=J-(U-1)^2\), \(J=205/144\), and
\(1.5\le U\le a_0+1/2\). Its curvature is
\[
 K''=qQh^2/V^3-(p+qU/V)(U-1).
\tag{13}
\]
Differentiate its right side in \(U\) and multiply by \(V^5/q>0\).
The result is
\[
 3QE(U)-UV^4-(p/q)V^5,\qquad
 E(U)=U^2-(Q+1-J)U+Q.
\]
A completed square proves \(E(U)>.867\) for every real \(U\).
Using \(U<1.915,V^2<1.666,V<1.291\), the displayed derivative is
positive by
\[
 3Q(.867)-1.915(1.666)^2-.253(1.291)^5>3.9.
\]
Thus (13) has its least value at \(U=1.5\). With
\(T_0=\sqrt{Q-9/4}\), positive square comparisons give
\[
 K''\ge.76744\left[\frac{Q(169/144)}{T_0^3}
                 -\frac{1.5/T_0+.253}{2}\right]>1.09.
\tag{14}
\]
For indices 2,6,7,20,21, the explicit initial derivative
\(K'(0)=-1+(p+3q/(2T_0))(13/12)\) is positive, and \(K(0)>.89810\).
For the other three, a single reference in each exact formula gives
\[
\begin{aligned}
 K(.025)-K'(.025)^2/2.18&>.9115 &&(i=3),\\
 K(.118)-K'(.118)^2/2.18&>.89856 &&(i=14),\\
 K(.11945)-K'(.11945)^2/2.18&>.89847 &&(i=15).
\end{aligned}
\]
Integration of (14) and a square completion prove \(K>.898\) on the
entire axial domain for every tuple, not only near the references.

### 2.3. One intrinsic interior/axial event

At the axial target define \(H(x)=M'(U-1/2)k-g\). This function increases
strictly. After multiplying its derivative by \(V^3/q\), the expression is
\[
 Qhk-[UV^2+(p/q)V^3]s
 >Q(.764)(.903)-[1.915(1.666)+.253(1.291)^3](.428)>1.1.
\]
For indices 2,6,20,21, \(H(0)>0\), so the minimum is always axial.
For indices 3,7,14,15, \(H(0)<0\) and \(H(.11)>.004\).
Hence each of these four cases has exactly one transition
\(x_t\in(0,.11)\): its minimum is interior before that event and
axial afterwards.

On the interior branch let \(U=a+1/2\) and
\[
 X=B+1/2=\frac{U-1-c_0\sin x}{\cos x}\ge1/2.
\]
The actual stationarity equation gives
\[
 M'(a)=g/\cos x,\qquad
 U'=\frac{g\sec x\tan x}{M''}>0,\qquad
 X'=U'/\cos x-c_0+X\tan x\ge-c_0.
\]
The reduced cost \(F\) has, by differentiation at its minimizing target,
\[
 F'=-1+c_0g-gX\tan x,\qquad
 F''=-g(X'\tan x+X\sec^2x)
       \le g[c_0\tan x-(1/2)\sec^2x]<0.
\tag{15}
\]
The last inequality uses \(x<x_t<.11\), so
\(c_0\tan x-(1/2)\sec^2x<(13/12)(.111)-1/2<0\).
This is a concavity proof on the whole interior contact branch.
Its terminal value equals \(K(x_t)>.898\). At zero it is exactly
\[
 F(0)=\pi/2+c+g+(g-p+q)/2
                   -R\sqrt{(g-p)^2+q^2}>.89809
\tag{16}
\]
for all four applicable tuples. These four fixed aligned evaluations
and concavity prove the entire branch, completing the lower half.

### 2.4. One aligned tangent on the whole upper half

Define the constant support geometrically by
\[
 \lambda=\max\{g,M'(1)\}=\max\{g,p+3q/(2T_0)\},
\qquad
 S(\lambda)=(\lambda-p+q)/2-R\sqrt{(\lambda-p)^2+q^2}.
\]
The exact coefficients give \(g\le\lambda<1.14\).
On \(\phi=\pi/2+x\), subtract \(\lambda\) times the original
separator in (8). Whole-circle source support is \(S(\lambda)\).
Using \(A\le7/12\), \(0\le B\le d_c\) on both core pieces yields
\[
 C\ge G(x):=\pi/2+x+c+S(\lambda)+\lambda/2
  +(\lambda/2)\cos x-(\lambda/12)\sin x
  -d_c\max\{0,g-\lambda\cos x\}.
\tag{17}
\]
Every one-sided derivative of this continuous function is at least
\(1-1.14[1.059(.645)+1/12]>0\).
At zero, when \(\lambda=M'(1)\), the source circle support is attained
at \(a=1\), and (17) equals \(K(0)\). When \(\lambda=g>M'(1)\),
it equals (16). Therefore \(G(0)>.898\), and monotonicity proves
its entire upper half, including the side/corner join and support kink.

## 3. Scope and exact arithmetic

Section 1 replaces every angle-concavity subdivision in the positive-target
core-source secondary class. Section 2 replaces every lower-half multiplier
interval in the positive-core-target primary class and gives its full
upper continuation from the aligned source tangent. The parent's source-sign
comparison restores the positive-source primary cases pointwise; it does
not change a vertex label in the cycle sum. Its exact reflection restores
the original target-owned axes.

The fixed arithmetic inputs are the parent's normalized coefficients,
(2), (3), (9), (13), and (16). Positive square comparisons and alternating
sine/cosine series at the named reference points suffice; the bound
\(\pi/2>1.570795\) suffices for the quoted endpoint reserves.
All continuous claims follow from (5)--(7), (12)--(15), and (17).
No finite angle cover or coefficient-sign table is a premise.
The negative-core primary rows and the other analytic parent classes
are assembled in HAND_SHORT_WORD_MIXED_QUARTER_NEGATIVE_CORE_WITHOUT_TABLES.md.
