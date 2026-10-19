# Mixed quarter-one circle supports and positive-core contacts without tables

This note replaces Sections 3.2 and 6 of
../SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md. It proves their complete
continuous domains: every positive-target core-to-outer secondary row,
and every positive-core-target outer-to-core primary row, on both entire
angle halves. The original normalization, exact affine labels, weak
separators, core side/corner, and source-sign dominance are retained.

All terminating decimals are exact rationals. Indices below refer to the
explicit normalized coefficient definitions in Section 1 of that parent
note; they are intrinsic signed role cases, not coordinate cells.
No scalar angle table, Bernstein row, or verifier status is a premise.

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad
 a_c=7/12,\quad d_c=1/2+\sqrt2/24.
\]
The angle is \(\phi=\pi/2\pm x\), \(0\le x\le .7\).
We use \(\cos x>.764\), \(\sin x<.645\), \(R<1.978788\),
\(d_c<.559\), and the ordinary positive-square bounds for these radicals.

## 1. Core-to-positive-outer secondary rows: global norm inequalities

The normalized cost and original source-secondary separator are
\[
 C=\phi+c+\sigma gb-pA-qB,
 \qquad \sigma b+A\sin\phi-B\cos\phi\ge W,
 \quad W=\frac{1+\sin\phi+|\cos\phi|}{2}.                 \tag{1}
\]
Here the source is on either core piece and the target is on the outer
arc. Take the following constant multipliers, in the indicated intrinsic
row order:
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
\end{array}                                                \tag{2}
\]
These constants define one support for each full role case; none changes
with the angle. The source remainder after subtracting the separator is
\(\sigma(g-\lambda)b\ge0\). Enlarging the target to its whole circle
therefore gives, with \(s=\sin x,k=\cos x\),
\[
\begin{aligned}
 C&\ge F_-(x)=\pi/2-x+c+(\lambda+p+q)/2+\lambda k-RN_-(x),\\
 C&\ge F_+(x)=\pi/2+x+c+(\lambda+p+q)/2+\lambda(k+s)-RN_+(x),\\
 N_\pm(x)^2&=p^2+q^2+\lambda^2+2\lambda(pk\pm qs).
\end{aligned}                                               \tag{3}
\]
Let \(N_0^2=(p+\lambda)^2+q^2\). Every row in (2), with its explicit
parent coefficients, has \(p+.764\lambda>.38\), so both norms stay
strictly positive.

Define
\[
 D=\begin{cases}N_0^2-\lambda p,&p\ge0,\\
 N_0^2+2\lambda|p|/1.764,&p<0.\end{cases}
\]
The following **constant** inequalities hold for all fourteen tuples:
\[
\begin{gathered}
 2\lambda q-.645D>.31,\qquad 4\lambda-RN_0>.27,\\
 .764N_0^2-\lambda q-
       \lambda\max(0,-p)\frac{.645}{1.764}>.09.             \tag{4}
\end{gathered}
\]
They are direct substitutions into (2) and the printed coefficient
triples. The first and third are rational inequalities; the second
follows by positive squaring. They do not evaluate any moving state or
angle. We now derive their whole-angle consequences.

The exact lower-half identity is
\[
 N_-^2-N_0^2k^2=N_0^2s^2-2\lambda p(1-k)-2\lambda qs.
\]
For \(p\ge0\), use \(1-k\ge s^2/2\); for \(p<0\), use
\(1-k=s^2/(1+k)<s^2/1.764\). Thus (4) gives
\[
 N_-^2-N_0^2k^2\le s(Ds-2\lambda q)\le0,
 \qquad N_-\le N_0k.                                      \tag{5}
\]
For the upper half,
\[
 N_+^2-N_0^2(k+s)^2
 =2\lambda p(k-1)+2\lambda qs-2N_0^2ks.
\]
The first term is nonpositive if \(p\ge0\); otherwise bound it above
by \(2\lambda|p|s^2/1.764\). The last inequality of (4) proves
\[
                              N_+\le N_0(k+s).             \tag{6}
\]
For either norm, direct differentiation gives the exact identity
\[
 N_\pm''+N_\pm/4
   =\frac{(p^2+q^2-\lambda^2)^2}{4N_\pm^3}\ge0.
\]
Equations (3)--(6) consequently imply on each whole angle half
\[
 F_-''\le k(-\lambda+RN_0/4)<0,\qquad
 F_+''\le(k+s)(-\lambda+RN_0/4)<0.                          \tag{7}
\]
No intermediate-angle concavity tests are necessary.

For a negative source, the original separator on the lower half forces
\(\phi>1\): its largest possible margin is bounded by
\((a_0-1/2)\sin\phi-(1/2)\cos\phi-1/2\), which increases and is still
negative at 1. A positive source uses the whole lower half.
Thus the lower endpoint in the original \(\phi\) variable is 1 or
\(\pi/2-.7\), respectively. The explicit functions (3) have
\[
 F_\pm(0)>.89809,
\]
while all their applicable lower-half terminal values exceed .9065 and
all upper-half terminal values \(F_+(.7)\) exceed 1.19.
These are substitutions at the endpoints of already proved concave
functions. Equations (2)--(3), the radical circle bounds, and alternating
sine/cosine series reproduce them directly.
It follows that all fourteen complete original row families have
\(C>.898\), replacing all four angle ranges formerly used for each.

## 2. Outer-to-positive-core primary contacts: exact continuous minimum

After the parent's source-sign comparison, the required eight rows have
negative source sign. Their cost and stipulated source-primary separator
are
\[
 C=\phi+c+pa-qb-gB,
 \qquad a-A\cos\phi-B\sin\phi\ge W.                       \tag{8}
\]
Here the source is outer and the target core. The explicit
\((i;c,p,q,g)\) data are
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
\end{aligned}                                               \tag{9}
\]
All have \(p/q<.253\), \(q\ge .76744\), \(g\le1.13855\).
Their source cost in primary coordinates is
\[
 M(a)=pa-q\left(\sqrt{Q-(a+1/2)^2}-1/2\right),
\]
\[
 M'=p+q\frac{a+1/2}{\sqrt{Q-(a+1/2)^2}}>0,
 \qquad M''=\frac{qQ}{[Q-(a+1/2)^2]^{3/2}}>0.              \tag{10}
\]
Positivity holds on the source range used below; in particular its
primary coordinate is at least 1 on every lower-half contact.

### 2.1. The lower half has only a side target and one contact interval

Write \(\phi=\pi/2-x\). A target corner, including the side/corner join,
would force
\[
 a\ge1/2+(d_c+1/2)\sin x+\cos x\ge3/2>a_0.
\]
The middle inequality follows from concavity and the two endpoints on
\([0,.7]\). Thus the entire feasible target is on the side \(A=7/12\).
Let \(c_0=13/12\). Reducing the increasing source cost gives the exact
contact
\[
 a=1/2+c_0\sin x+(B+1/2)\cos x.                            \tag{11}
\]
In particular \(a\ge1>d\). The angle ends at the unique axial event
\(x_{max}\) where (11) with \(B=0\) reaches \(a_0\).
The contact height increases with \(x\), and substitution shows
\(x_{max}<.442\). Consequently every feasible lower-half contact has
\[
 k=\cos x>.903,\quad s=\sin x<.428,
 \quad h=c_0k-s/2>.764.
\]
At fixed \(x\), its cost is strictly convex in \(B\):
\[
 C_B=M'(a)k-g,\qquad C_{BB}=M''(a)k^2>0.                   \tag{12}
\]
The upper target endpoint is the source-axis endpoint \(a=a_0\), not
\(B=1/2\), which is infeasible as just shown. At that endpoint the
derivative in (12) is positive, since
\[
 [p+2q(a_0+1/2)]k-g
 >[-.51554+2(.76744)(1.914)](.903)-1.139>0.
\]
Thus the minimum is either the axial target \(B=0\) or the unique
interior solution of \(M'(a)k=g\).

### 2.2. A uniform curvature bound for the whole axial reference

On the axial target define
\[
 U=1+c_0s+k/2,\quad V=\sqrt{Q-U^2},\quad
 K(x)=\pi/2-x+c+p(U-1/2)-q(V-1/2).
\]
Here \(U'=h>0\), \(h^2=J-(U-1)^2\), \(J=205/144\), and
\(1.5\le U\le a_0+1/2\). Its curvature is
\[
 K''=qQh^2/V^3-(p+qU/V)(U-1).                              \tag{13}
\]
To control it without a contact-range table, differentiate the right
side with respect to \(U\). Multiplication by \(V^5/q>0\) gives
\[
 3Q E(U)-UV^4-(p/q)V^5,
 \quad E(U)=U^2-(Q+1-J)U+Q.
\]
Completing a square gives \(E(U)>.867\) for every real \(U\).
Since \(U<1.915\), \(V^2\le Q-2.25<1.666\), and \(V<1.291\),
the displayed derivative is positive by
\[
 3Q(.867)-1.915(1.666)^2-.253(1.291)^5>3.9.
\]
Thus the least curvature in (13) is at \(U=1.5\). Put
\(T_0=\sqrt{Q-9/4}\). Direct positive squaring gives
\[
 K''\ge .76744\left[\frac{Q(169/144)}{T_0^3}
             -\frac{1.5/T_0+.253}{2}\right]>1.09.           \tag{14}
\]

For indices 2, 6, 7, 20, 21, the explicit initial derivative
\(K'(0)=-1+(p+3q/(2T_0))(13/12)\) is positive and \(K(0)>.89810\).
For the other three, one reference each in the same formula gives
\[
\begin{aligned}
 K(.025)-K'(.025)^2/2.18&>.9115 &&(i=3),\\
 K(.118)-K'(.118)^2/2.18&>.89856 &&(i=14),\\
 K(.11945)-K'(.11945)^2/2.18&>.89847 &&(i=15).
\end{aligned}
\]
Integrating (14) and completing a square proves \(K>.898\) on the
entire axial domain for every tuple, not just near these references.

### 2.3. The interior contact ends at one intrinsic event

At the axial target let
\(H(x)=M'(U-1/2)k-g\). It increases strictly. Indeed, after multiplying
its derivative by \(V^3/q\), the exact expression is
\[
 Qhk-[UV^2+(p/q)V^3]s
 >Q(.764)(.903)-[1.915(1.666)+.253(1.291)^3](.428)>1.1.
\]
For indices 2, 6, 20, 21, \(H(0)>0\), so the convex contact minimum is
always axial. For indices 3, 7, 14, 15, \(H(0)<0\) and \(H(.11)>.004\).
There is exactly one transition \(x_t\in(0,.11)\) for each of them.
Before it the unique contact minimum is interior; after it the minimum
is the axial reference already bounded above.

On the interior branch let \(U=a+1/2\) and
\[
 X=B+1/2=\frac{U-1-c_0\sin x}{\cos x}\ge1/2.
\]
Stationarity and strict source convexity give
\[
 M'(a)=g/\cos x,\qquad
 U'=\frac{g\sec x\tan x}{M''}>0,
 \qquad X'=U'/\cos x-c_0+X\tan x\ge-c_0.
\]
For the reduced cost \(F(x)\), differentiation at this actual stationary
contact eliminates the derivative of the minimizing target:
\[
 F'=-1+c_0g-gX\tan x,
\]
\[
 F''=-g(X'\tan x+X\sec^2x)
 \le g[c_0\tan x-\tfrac12\sec^2x]
 <g[(13/12)(.111)-1/2]<0.                                  \tag{15}
\]
We used only \(x<x_t<.11\), a consequence of the unique contact event.
The interior cost is therefore concave on its entire branch.
At \(x=x_t\) it equals \(K(x_t)>.898\). At zero it is exactly
\[
 F(0)=\pi/2+c+g+\frac{g-p+q}{2}
                          -R\sqrt{(g-p)^2+q^2}>.89809     \tag{16}
\]
for all four applicable tuples. These are four fixed aligned evaluations,
not a sequence of angle supports. Concavity proves the whole branch.
This completes every lower-half positive-core primary contact.

### 2.4. One aligned support continues over the whole upper half

Define the constant geometrically by its aligned source tangent:
\[
 \lambda=\max\{g,M'(1)\}
         =\max\{g,p+3q/(2T_0)\},
\quad
 S(\lambda)=\frac{\lambda-p+q}{2}
                    -R\sqrt{(\lambda-p)^2+q^2}.
\]
The explicit coefficients give \(g\le\lambda<1.14\).
On \(\phi=\pi/2+x\), subtract \(\lambda\) times the actual separator
in (8). The whole-circle source support is \(S(\lambda)\).
Using \(A\le7/12\), \(0\le B\le d_c\) on both core pieces gives
\[
 C\ge G(x):=\pi/2+x+c+S(\lambda)+\lambda/2
    +(\lambda/2)\cos x-(\lambda/12)\sin x
    -d_c\max\{0,g-\lambda\cos x\}.                       \tag{17}
\]
Each one-sided derivative of this continuous function is at least
\[
 1-1.14[1.059(.645)+1/12]>0.
\]
At zero its value is the aligned minimum already proved: when
\(\lambda=M'(1)\) the source circle support is attained at \(a=1\),
and (17) equals \(K(0)\); when \(\lambda=g>M'(1)\), it equals (16).
Thus \(G(0)>.898\), and monotonicity proves the entire upper half,
including the side/corner join and the nondifferentiable support transition.

## 3. Scope and remaining dependencies

Section 1 replaces every angle-concavity subdivision in the positive-target
core-source secondary class. Section 2 replaces every lower-half multiplier
interval in the positive-core-target primary class, and gives its whole
upper-half continuation with a geometrically defined aligned multiplier.
The parent's source-sign comparison restores the positive-source primary
cases pointwise; it does not alter a vertex's label in the cycle sum.
Its exact reflection/reversal restores each original target-owned axis.

The fixed arithmetic has explicit inputs: the normalized parent coefficients,
(2), (3), (9), (13), and (16). Positive rational square comparisons and
alternating sine/cosine series at the named reference points suffice;
\(\pi/2>1.570795\) already suffices for the quoted endpoint reserves.
All continuous claims follow from (5)--(7), (12)--(15), and (17).
There is no finite angle cover or coefficient-sign table in these proofs.

Negative-core-target primary rows, and the remaining parent classes that
already have whole-domain analytic arguments, are separate obligations
in the full mixed-quarter assembly.
