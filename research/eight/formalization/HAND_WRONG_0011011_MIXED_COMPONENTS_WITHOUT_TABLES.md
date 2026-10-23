# The mixed components of 0011011 without scalar tables

This note supplies analytic replacements for the remaining scalar tables
in the nineteen mixed reflection classes of
`../WRONG_0011011_WHOLE_WORD_HAND_PROOF.md`. The original geometric
reductions retain their original separating axes, core side and corner,
closed angle endpoints, and ties. All decimals below are exact rationals.

**Assembly status.** Sections 1–8 give all remaining analytic replacements.
Section 9 assembles the complete nineteen mixed reflection classes for
an actual seven-cycle after frame concentration and the zero-primary
cyclic exclusion. This is the mixed component of the whole-word proof;
the core/core and outer/outer components have separate proofs.

Throughout,
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad \gamma=.89765.
\]
Every numerical comparison in this note follows from its printed
expressions by positive squaring and alternating Taylor bounds at the
stated rational points. One may use
\[
 3.141592653589793238<\pi<3.141592653589793239.
\]
No verifier, coefficient list, or subdivision is a premise.

## 1. One support formula replaces nine squared-polynomial rows

### 1.1. Exact unsquared expressions and scope

For positive constants \(g,p\) and a constant \(C\), set
\[
 K=\pi/2+C+(g+p)/2-\gamma,\qquad
 N(x)=\sqrt{g^2+p^2\cos^2x},
\]
\[
\begin{aligned}
 F_-(x)&=(K-x)\cos x+g\{1+(13/12)\sin x\}-RN(x),\\
 F_+(x)&=(K+x)\cos x+g\{1-(1/12)\sin x\}-RN(x).
\end{aligned}                                                   \tag{1}
\]
These are exactly the original circle-support lower bounds minus
\(\gamma\), multiplied by the positive number \(\cos x\).
Proving their positivity therefore supplies the original desired
inequality with no squaring or Taylor-polynomial reduction.

The complete list of uses is as follows. The filenames in the first
column have prefix `WRONG_0011011_` and suffix `_HAND_PROOF.md`.

| Source and section replaced | Sign | \(g\) | \(p\) | \(C\) | Whole range |
|---|---:|---:|---:|---:|---:|
| `EDGE2_CORE_TO_POSITIVE_OUTER` §7 | − | 1.03981 | .670579666 | −.119683769 | [0,.7] |
| same | + | 1.03981 | .670579666 | −.119683769 | [0,.7] |
| `EDGE2_OUTER_TO_POSITIVE_CORE` §7 | − | 1.0424 | .8281 | −.01029 | [0,.7] |
| same | + | 1.0424 | .853 | −.01029 | [.02,.7] |
| `EDGE3_OUTER_TO_POSITIVE_CORE` §10 | − | .94831 | .62 | −.1606 | [0,.171] |
| same | + | .94831 | .633 | −.1606 | [.02,.7] |
| `EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER` §5.1 | − | 1.0424 | .643398450 | −.142806398 | [.11,.7] |
| `EDGE3_OUTER_TO_NEGATIVE_CORE` §3 | − | .62312 | .633 | .05733 | [.161,.7] |
| `EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER` §5.2 | + | .98439 | .73 | \(-.22042+.34492(7/12)-.108\) | [.3,.7] |

This is a map of intrinsic geometric cases to one formula, not a
continuous-domain partition.

### 1.2. Every upper-half support is strictly concave

Write \(s=\sin x,c=\cos x\). Direct differentiation gives
\[
 N''=-\frac{p^2(c^2-s^2)}N-\frac{p^4s^2c^2}{N^3}.
                                                               \tag{2}
\]
Consequently
\[
 F_+''=-(K+x)c-(2-g/12)s-RN''.
\]
On \([0,.7]\), \(N\ge g\), \(c\ge1-s^2\), and \(0\le s<.645\).
It follows that
\[
 F_+''\le Rp^2/g-K-(2-g/12)s+(K+Rp^4/g^3)s^2.                 \tag{3}
\]
For all four plus cases,
\[
 Rp^2/g-K<-.229,
 \qquad .645(K+Rp^4/g^3)-(2-g/12)<-.277.
                                                               \tag{4}
\]
Thus (3) is strictly negative on their entire ranges. Concavity reduces
each to its two endpoints. In the order of the four plus cases above,
their endpoint lower bounds are respectively
\[
 (.000137,.3025),\quad(.00582,.3202),\quad
 (.01365,.3226),\quad(.20000,.3006).
                                                               \tag{5}
\]
All eight comparisons are direct substitutions into (1). This proves
every upper-half support in the map.

### 1.3. The two full lower-half ranges follow from one square completion

For either of the first two minus cases, put
\[
 N_0=\sqrt{g^2+p^2},\qquad A=Rp^2/(2N_0).
\]
The tangent inequality for the square root gives, everywhere,
\[
 N(x)\le N_0-\frac{p^2}{2N_0}\sin^2x.                         \tag{6}
\]
Since \(K-x>0\), the elementary whole-range inequalities
\[
\begin{aligned}
 \cos x&\ge1-x^2/2+x^4/24-x^6/720,\\
 \sin x&\ge x-x^3/6+x^5/120-x^7/5040,\\
 \sin^2x&\ge x^2-x^4/3
\end{aligned}
\]
give
\[
\begin{aligned}
 F_-(x)\ge F_-(0)
 &+(13g/12-1)x+(A-K/2)x^2\\
 &+(1/2-13g/72)x^3+(K/24-A/3)x^4\\
 &+(13g/1440-1/24)x^5-Kx^6/720\\
 &+(1/720-13g/60480)x^7.                                    \tag{7}
\end{aligned}
\]
The last coefficient is positive; the fourth- and fifth-degree
coefficients are negative. As \(0\le x\le.7\), this yields
\[
 F_-(x)\ge F_-(0)+x(a-bx+ex^2),                              \tag{8}
\]
where
\[
\begin{aligned}
 a&=13g/12-1,\qquad b=K/2-A,\\
 e&=1/2-13g/72+.7(K/24-A/3)\\
  &\hspace{12mm}+.49(13g/1440-1/24)-.343K/720.
\end{aligned}
\]
For the first minus case,
\[
 F_-(0)>.000137,\quad a>.12646,\quad b<.34475,
 \quad e>.25295,\quad4(.12646)(.25295)-(.34475)^2>.009.
\]
For the second,
\[
 F_-(0)>.00615,\quad a>.12926,\quad b<.28942,
 \quad e>.22291,\quad4(.12926)(.22291)-(.28942)^2>.031.
\]
Each lower quadratic is strictly positive by completing a square.
Equation (8) therefore proves both whole ranges, including \(x=0\).

### 1.4. The short lower-half range is concave

For \(g=.94831,p=.62,C=-.1606\), equation (2) gives throughout
\(0\le x\le t=.171\)
\[
 F_-''\le(2-13g/12)\sin t-(K-t)\cos t
   +R\{p^2/g+p^4\sin^2t/g^3\}<-.131.                        \tag{9}
\]
The direction follows from the positive coefficients and
\(K-x\ge K-t\). The two endpoint values are
\[
 F_-(0)>.00304,\qquad F_-(.171)>.000185.
\]
Strict concavity proves this whole lower support.

### 1.5. The remaining tight lower support has increasing curvature

Take \(g=1.0424,p=.643398450,C=-.142806398\).
Direct differentiation of (2) gives
\[
 N'''=\frac{4p^2sc}N
      -\frac{3p^4sc(c^2-s^2)}{N^3}
      -\frac{3p^6s^3c^3}{N^5}
 \le4p^2sc/g,
\]
because \(0\le x\le.7<\pi/4\). Hence
\[
\begin{aligned}
 F_-'''&=(3-13g/12)c+(K-x)s-RN''',\\
 \frac{F_-'''}c
 &\ge3-13g/12-\{4Rp^2/g-(K-.7)\}\sin x\
 &>3-13g/12-.645\{4Rp^2/g-(K-.7)\}>.277.                    \tag{10}
\end{aligned}
\]
Thus \(F_-'\) is strictly convex and \(F_-''\) is increasing.
At the single reference \(x=.5\),
\[
 F_-(.5)>.00428,\quad F_-'(.5)<-.01449,\quad F_-''(.5)>.06.
\]
On \([.11,.5]\), convexity of \(F_-'\), together with its negative
right endpoint, forbids a negative-to-positive sign crossing. Therefore
\(F_-\) has no interior minimum there. Both endpoint values are positive,
the left one satisfying \(F_-(.11)>.00204\).

On \([.5,.7]\), equation (10) gives \(F_-''>.06\).
At \(x=.62\),
\[
 F_-(.62)>.00326,\qquad |F_-'(.62)|<.0004.
\]
Strong convexity and a completed square consequently give everywhere
on that whole range
\[
 F_-(x)>.00326-\frac{(.0004)^2}{.12}>0.                     \tag{11}
\]
These two derivative-covered ranges prove the entire requested
\([.11,.7]\); no mesh or local curvature enclosure is used.

### 1.6. The last lower support decreases on its whole range

For \(g=.62312,p=.633,C=.05733\), one has
\(N(x)\ge N(.7)>.789\). From (1),
\[
 \frac{F_-'(x)}{\cos x}
 =13g/12-1-(K-x)\tan x+Rp^2\sin x/N(x).
\]
Using \(\tan x\ge\sin x\), \(K-x\ge K-.7>0\), and the
positive coefficient in the next line, we obtain throughout
\([.161,.7]\)
\[
 \frac{F_-'(x)}{\cos x}
 \le13g/12-1+.645\{Rp^2/.789-(K-.7)\}<-.101.                \tag{12}
\]
Thus \(F_-\) decreases. Its final value satisfies
\(F_-(.7)>.000216\), which finishes the ninth support in the map.

## 2. The complete same-sign mixed zero component

In `../WRONG_0011011_SAME_SIGN_MIXED_ZERO_HAND_PROOF.md`, Families I
and II already use full-domain geometric and derivative reductions.
Family IV requires a primary zero-quarter separator. The table-free
whole-cycle theorem `HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md` excludes
that separator after G1, before any wrong-word cuts or mismatch bound.
Thus Family IV is absent in the present seven-cycle application. This
is an explicit use of the stronger global hypothesis; it is not a new
claim about arbitrary independent pairs.

Only the eight curvature intervals for Family III need replacement.
We give one bound on the whole contact arc.

### 2.1. A uniform curvature ratio for the circle contact

Use the exact contact variables from §6 of the cited note:
\[
\begin{gathered}
 s=\sin\phi,\quad c=\cos\phi,\quad m=s+c,\quad n=c-s,\\
 Z=1/2+m,\quad Y=\sqrt{Q-Z^2},\quad
 U=Zs+Yc,\quad V=Zc-Ys,\quad B=V-1/2,\\
 f=1-n/Y,\quad N=m(Q-9/4)-m^2/2-1.
\end{gathered}
\]
On the enlarged whole range \(.3024\le\phi\le.7\),
\[
 U'=Vf>0,\quad V'=-Uf<0,\quad f'=N/Y^3>0.
\]
The endpoint comparisons consequently give everywhere
\[
 1.399<U<1.629,\quad V>1.124,\quad .624<B<.9,
 \quad1.252<m<1.41.                                         \tag{13}
\]
Put \(D=Q-9/4-m\) and \(\eta=Y-n\). Then
\(Y^2-n^2=D>0\), \(\eta>0\), and
\[
 -\frac{B''}{(B')^2}
 =\frac V{U^2}+\frac{N}{UY\eta^2}.                          \tag{14}
\]
We next prove \(N>4Y\eta^2\) on the entire range of \(m\).

This radical inequality has a convenient short algebraic proof. Write
\[
 y=Q-(m+1/2)^2,\quad z=2-m^2,
\]
so \(y=Y^2,z=n^2,y-z=D\), and define the single expression
\[
 P(m)=(16Ny)^2z-(16yD^2-N^2)^2.                              \tag{15}
\]
For \(t=1.41-m\), one has \(0<t<.158\).
Expanding the expression (15) and grouping like powers gives directly
\[
\begin{aligned}
 P(1.41-t)>
 &.003+5t+126t^2+459t^3\\
 &-t^4(5178+3848t+1784t^4+64t^6).                            \tag{16}
\end{aligned}
\]
For clarity, (16) is an ordinary polynomial inequality: subtract its
right side from the expression (15), and every power coefficient is
nonnegative, with a strictly positive constant. This can be checked by
expanding the two squares in (15); no Bernstein conversion is involved.
The parenthesis is less than 5790 on \([0,.158]\). Therefore
\[
 P(1.41-t)>.003+5t+t^2(126+459t-5790t^2)>0.                  \tag{17}
\]
The last quadratic is concave; its endpoint values exceed 53.

Since \(N,y,n\) are positive, (15)–(17) imply
\[
 16Nyn>|16yD^2-N^2|.
\]
Hence
\[
 (N+8yn)^2-\{4Y(y+n^2)\}^2
 =N^2+16Nyn-16yD^2>0.
\]
Both quantities being compared are positive. Taking their square roots
and rearranging proves \(N>4Y(Y-n)^2\), as asserted.
Equation (14) now gives the useful uniform bound
\[
 -\frac{B''}{(B')^2}
 >\frac{1.124}{1.629^2}+\frac4{1.629}>2.879.                 \tag{18}
\]

### 2.2. Both outer labels have a smaller logarithmic derivative

The two labels in this family are
\[
\begin{aligned}
 P_0(B)&=.02478+.93015B+.02363B^2-.11055(A(B))B,\\
 L(B)&=.03965+3.85510B-1.49748B^2-1.89442(A(B))B,
\end{aligned}
\]
where \(A(B)=\sqrt{Q-(B+1/2)^2}-1/2\).
The original whole-domain derivative formulas prove
\(P_0'>.773\), and \(P_0''\) increases. The endpoint bound
\(P_0''(.9)<.412\) therefore gives \(P_0''/P_0'<1\).

For \(L\), put \(v=1.49748,k=1.89442,\kappa=2.8\), and
\(C_0=3.85510+v+k/2\). On the circle \(U^2+V^2=Q\),
\[
\begin{aligned}
 L'&=C_0-2vV+kQ/U-2kU-kV/(2U),\\
 L''&=-2v+k\{2V/U+(V-1/2)Q/U^3\}.
\end{aligned}
\]
The coefficient of \(V\) in \(U^3(L''-\kappa L')\) is positive.
The circle tangent \(V\le2\sqrt{Q/2}-U<2.7986-U\) thus gives
\[
 U^3(L''-\kappa L')<q(U),                                    \tag{19}
\]
where the following single quartic is explicit:
\[
\begin{aligned}
 q(U)={}&(2.7986-U)
 \{2kU^2+kQ+2\kappa vU^3+\kappa kU^2/2\}\\
 &+2\kappa kU^4-(2v+\kappa C_0)U^3
       -\kappa kQU^2-kQ/2.
\end{aligned}
\]
Its fourth derivative is the positive constant 53.348736, and at
\(U=1.399\) its third and second derivatives exceed 52 and 16.
Thus \(q''>0\) on the full interval in (13). Moreover
\[
 q'(1.629)<-6.6,\qquad q(1.399)<-.057.
\]
The increasing derivative is negative everywhere, so \(q<0\).
As \(L'>0\) was already proved in the original note, (19) establishes
\[
                         L''/L'<2.8.                       \tag{20}
\]

### 2.3. Whole-arc concavity and complete coverage

For either label \(F=P_0,L\), the contact cost is
\(H(\phi)=\phi-c_0+F(B(\phi))\). Equations (18) and (20) give
\[
 H''=F'(B)(B')^2
       \left\{\frac{F''(B)}{F'(B)}+\frac{B''}{(B')^2}\right\}<0
\]
on the whole enlarged contact arc. The original two endpoint
comparisons, \(H(\phi_0)>.89773\) and \(H(.7)>1.04\), now prove
Family III without any curvature partition.

Families I and II, this argument for Family III, and the global absence
of Family IV cover every same-sign mixed zero case of the actual
seven-cycle. The reflected cases use the same original reflection
identity and require no new scalar estimates.

## 3. The complete edge-3 negative outer to negative core component

Section 1.6 replaces the sole squared-polynomial gate in
`../WRONG_0011011_EDGE3_OUTER_TO_NEGATIVE_CORE_HAND_PROOF.md`.
Its only other table consists of the three endpoint-angle monotonicity
intervals in §5. They admit one convex-product replacement.

Use the original height-coordinate label
\[
 M(u)=m_0-vu^2-ku/2-(V-ku)\sqrt{Q-u^2},
 \quad v=.91744,\quad k=.95769,\quad V=3.819505.
\]
The constant \(m_0\) is immaterial to the derivatives. On the whole
required height range \(1.4\le u\le1.7\), put
\(z=\sqrt{Q-u^2}\). Then
\[
 M'''=3Q(Vu-kQ)/z^5>0,
 \qquad\frac{M''''}{M'''}=\frac V{Vu-kQ}+\frac{5u}{z^2}>9/2.  \tag{21}
\]
Indeed \(u\ge z\), \(z<1.4\), and \(V(u-1)<kQ\).
Thus the two summands exceed 1 and \(25/7\), respectively.
At the left endpoint,
\[
 M'(1.4)<.774,\quad M''(1.4)<0,\quad M'''(1.4)>3.5.
\]
First \(M'''-2M''\) is positive and increasing, by (21).
It follows that the derivatives of both
\(M'''-3M'\) and \(M'''-3M'-3M''\) are positive.
Their left endpoint values are positive by the same displayed bounds.
Consequently
\[
               M'''>3M'+3\max(M'',0)                       \tag{22}
\]
throughout this whole interval. Here \(M'>.75>0\) was already
established by the original analytic height argument.

For either core endpoint let
\[
 K=(A_e+1/2)^2+(B_e-1/2)^2,
 \quad1.12479<K\le(13/12)^2<1.174,
\]
and define
\[
 v_0(u)=\sqrt{K-(u-1)^2},\qquad A(u)=M'(u)v_0(u).
\]
Writing \(h=u-1\), we have
\[
 A''=M'''v_0-2M''h/v_0-M'K/v_0^3.                           \tag{23}
\]
On the whole height range,
\[
 v_0^2>.63479,\quad3v_0^2>2h,\quad
 3v_0^4>K,
\]
the last inequality following already from
\(3(.63479)^2>1.174\). If \(M''\ge0\), (22) makes the right side
of (23) larger than
\[
 \frac{M'(3v_0^4-K)}{v_0^3}
       +\frac{M''(3v_0^2-2h)}{v_0}>0.
\]
If \(M''<0\), its term in (23) is positive, and \(M'''>3M'\)
gives the same conclusion. Hence \(A\) is strictly convex for both
core endpoints.

As \(A\) increases with \(K\), it suffices to evaluate the two
height endpoints using \(K=(13/12)^2\). Direct substitution gives
\[
 A(1.4)<.779,\qquad A(1.7)<.869.
\]
Convexity therefore gives \(A(u)<.869\) throughout.
On the original endpoint contact curve, \(-u_e'=v_0(u_e)\), so
\[
 H_e'=1-M'(u_e)(-u_e')=1-A(u_e)>.131.                       \tag{24}
\]
This proves both endpoint curves increase on their entire angle range,
with no subdivision. Their original initial values are
\(H_{\rm join}>.9196\) and \(H_{\rm diagonal}>.897784\).
The original strict concavity in the core coordinate then completes
every corner case. Together with Section 1.6 and the original remaining
analytic axis arguments, the full edge-3 negative outer to negative
core component is proved without scalar tables.

## 4. The complete opposite-sign mixed zero component

The remaining nonanalytic premises of
`../WRONG_0011011_OPPOSITE_MIXED_ZERO_HAND_PROOF.md` are the three
curvature intervals in §9, the side-loss ranges in §10.1, and the
degree-ten inequality in §10.2. The following whole-domain arguments
replace all three. Its other geometric and analytic endpoint reductions
remain applicable. Its primary-owner §3 may also be omitted in the
actual cycle, by the same global zero-primary exclusion used in §2.

### 4.1. The negative-angle \(P_0\) diagonal has decreasing curvature

On this core-diagonal contact,
\[
 B=1/2+(1/2-d_c)\cos x+(d_c+1/2)\sin x,
 \qquad w=B'>0.
\]
The useful exact identities are
\[
 w'=1/2-B,\quad w''=-w,\quad
 w^2=(d_c-1/2)^2+(d_c+1/2)^2-(B-1/2)^2<1.126.               \tag{25}
\]
The physical range, enlarged to \(0\le x\le.44152\), gives
\(1-d_c\le B<.9\). The cost
\(H(x)=-x+c_0+gd_c+P_0(B(x))\) satisfies
\[
 H'''/w=P_0'''w^2+3P_0''(1/2-B)-P_0'.                       \tag{26}
\]

The third derivative \(P_0'''\) is convex on this whole target range.
To check this directly, put \(V=B+1/2,U^2=Q-V^2,k=.11055\).
Then
\[
 P_0'''=3kQ(Q-V/2)/U^5,
\]
and its derivative has positive numerator
\(5QV-Q/2-2V^2\). That numerator itself has positive derivative
\(5Q-4V\), so differentiating once more proves convexity.
The two point bounds \(P_0'''(.5)<.306\) and
\(P_0'''(.9)<.781\) consequently give, for \(t=B-.5\ge0\),
\[
 P_0'''(B)<.306+1.188t.                                     \tag{27}
\]

For \(B\le.5\), monotonicity gives
\(P_0'''<.306,P_0''<.221,P_0'>.84\), and
\(0\le.5-B<.059\). Hence (26) is less than
\[
 .306(1.126)+3(.221)(.059)-.84<0.
\]
For \(B\ge.5\), the bounds \(P_0'>.852,P_0''>.220\), (25),
and (27) give
\[
 H'''/w<1.126(.306+1.188t)-.660t-.852<0
 \qquad(0\le t\le.4).                                     \tag{28}
\]
The last expression is affine and negative at both ends. These are the
two intrinsic signs of \(w'\); there is no angle subdivision.

Thus \(H''\) decreases on the entire contact arc. The original right
endpoint comparisons \(H''(.44152)>.0079\) and
\(H'(.44152)<-.044\) then give successively \(H''>0\) and
\(H'<0\) everywhere. The single final value
\(H(.44152)>.89779\) completes the whole \(P_0\) target row.

### 4.2. A uniform side-loss bound for the \(L\) row

Here \(g=.94831\), and the original side contact is
\[
 S(x,B)=-x+c_0+L(B)+g/2+g(1/2-B)\sec x+(13g/12)\tan x.
\]
Let \(A(B)=S(0,B)=c_0+g(1-B)+L(B)\), and put
\[
 n(B)=13g/12-1-g^2(B-1/2)^2/4.
\]
The original completed-square derivative gives
\(S_x\ge n(B)/\cos^2x\). If \(n(B)\ge0\), the already analytic
aligned bound gives \(S\ge A>.901\).

If \(n(B)<0\), then \(B>.84\), since \(B\ge.5\) and
\(n(.84)>0\). On the whole allowed angle range,
\(x<.442,\cos^2x>.81\), so integration gives
\[
 S(x,B)>A(B)+.546n(B),                                     \tag{29}
\]
using \(.442/.81<.546\) and the negative sign of \(n\).
The original whole-range strong convexity \(A''>.5\) and its
single reference \(B_*=.8216\) give
\[
 A(B)>.9010079-.0001(B-B_*)+.25(B-B_*)^2
 \qquad(B>.84).
\]
Thus the right side of (29) exceeds the explicit quadratic
\[
 K(B)=.9010079-.0001(B-.8216)+.25(B-.8216)^2+.546n(B).
\]
Its quadratic coefficient is .12724666164235, hence its derivative
increases; yet \(K'(.9)<-.059\). It therefore decreases throughout
\([.84,.9]\), and
\[
 S(x,B)>K(.9)=.897821530862776>.89765.                        \tag{30}
\]
This proves the full core side with one expression, without the three
former target-coordinate loss ranges.

### 4.3. The core-corner logarithmic derivative follows from one square

The scalar target previously proved by a degree-ten row is
\[
 L''(B)<\lambda(B-1/2)L'(B),\qquad
 \lambda=144/13,\quad1/2\le B\le.9.                         \tag{31}
\]
Put \(t=B-1/2,V=B+1/2,U^2=Q-V^2\), and define
\(D(B)=\lambda tL'(B)-L''(B)\).
Here \(L'''>5\), \(L''''>0\), and direct differentiation yields
\[
 \frac{L'''''}{L'''}
 =\frac5{U^2}+\frac{35V^2}{U^4}
       -\frac{10V}{U^2(2Q-V)}
 <\frac5{1.95}+\frac{35(1.4)^2}{1.95^2}<21.                 \tag{32}
\]
The lower bound \(U^2>1.95\) holds throughout this whole interval.
It follows that
\[
 D'''=3\lambda L'''+\lambda tL''''-L'''''
 >(3\lambda-21)L'''>60.                                    \tag{33}
\]
At the single reference \(B=.5\),
\[
 D(.5)>.031,\qquad D'(.5)>1.68,
 \qquad |D''(.5)|<9.
\]
Apply strong convexity to \(D'\) and complete a square:
\[
 D'(B)>1.68-\frac{9^2}{120}=1.005>0.                        \tag{34}
\]
Thus \(D\) increases from a positive initial value, proving (31)
on its whole domain.

The original core geometry has
\(B\le1/2+(13/12)\sin x\) and
\(-a''/(\cos x-a'\sin x)^2\ge12\). Equation (31) therefore gives
strict concavity of \(L(B(b))\) in the core coordinate, exactly as
required in the original §10.2. Its subsequent three geometric
endpoint alternatives and single strong-convexity reference finish
the corner.

The original source-transverse, nonnegative target-transverse, and
negative \(J\) arguments, together with §§4.1–4.3, cover all three
opposite-sign mixed zero reflection classes. Every final bound is
strictly larger than \(\gamma\), and no scalar table remains in this
component.

## 5. The complete edge-3 negative outer to positive core component

For the original EDGE3_OUTER_TO_POSITIVE_CORE hand note, Section 1
replaces its two squared-polynomial gates. We now replace the hidden
two-range ratio bound in its §1 and the eight early-angle tangents in
its §4.1. Its other contact, convexity, and endpoint arguments already
hold on their whole stated domains.

### 5.1. The high-source derivative ratio needs only convexity

For the original source label
\[
 T(b)=.01670+2.42322b-.91744b^2-.95769a(b)b,
\]
write \(u=a(b)+1/2\) and \(r=(b+1/2)/u\).
The height-coordinate function \(M\) of Section 3 satisfies
\(M'(u)=T'(b)/r\) and \(M'''>0\). Thus \(M'\) is convex.
For \(.7\le b\le d\), its height interval has endpoints
\(u=\sqrt{Q/2}\) and \(u=\sqrt{Q-1.44}\).
Direct substitution gives values below .774 and .816, respectively.
Consequently
\[
                    T'(b)/r<.816<.89                       \tag{35}
\]
on this entire source range. No source-coordinate subdivision is
necessary.

### 5.2. Actual feasibility resolves the early transverse contact

Put \(g=.94831\). On lower axis 3, the original target contact is
\[
 B=(a(b)-1/2)\sin\phi-(b+1/2)\cos\phi-1/2\ge0,
\]
and the cost at that contact is
\[
 F(b,\phi)=\phi-.0497-T(b)-gB.
\]
Its derivative is
\[
 F_b=g(r\sin\phi+\cos\phi)-T'(b),\qquad
 F_{bb}=gr'\sin\phi-T''(b)>0                               \tag{36}
\]
on the original early feasible range \(b<.6\), where \(T''<0\).

For \(\phi\le1.23\), feasibility gives \(\phi>1\): the largest
contact coordinate, at \(b=0\), is still negative at \(\phi=1\),
and it increases with \(\phi\). The endpoint where the target reaches
zero has the exact parametrization
\[
\begin{gathered}
 Z=1/2+\sin\phi,\quad Y=\sqrt{Q-Z^2},\quad
 U=Z\sin\phi+Y\cos\phi,\\
 V=Y\sin\phi-Z\cos\phi,\quad b_z=V-1/2,\quad
 f=1-\cos\phi/Y,\\
 b_z'=Uf,\quad U'=-Vf,\quad
 f'=\frac{-\sin^2\phi/2+(Q-1.25)\sin\phi-1/2}{Y^3}>0.
\end{gathered}                                               \tag{37}
\]
Both \(f\) and \(f'\) increase on \([1,1.23]\); for \(f'\),
its numerator increases while its denominator decreases.
Throughout the physical part of this whole arc, direct endpoint
bounds and these monotonicities give
\[
\begin{gathered}
 0\le b_z<.295,\quad1.812<U<1.915,\quad .5\le V<.795,\\
 Y>1.354,\quad .628<f<.754,\quad .451<f'<.631,\\
 .749<T'(b_z)<1.069,\qquad T''(b_z)<-.808.                  \tag{38}
\end{gathered}
\]
The last line uses the increasing \(T''\), its value at .295,
and the decreasing \(T'\) on this small source range.
Moreover
\[
 b_z''=-Vf^2+Uf'>1.812(.451)-.795(.754)^2>0.
\]
Since \(b_z'(1)>1.2\), this also proves \(b_z'>1.2\) everywhere
under consideration.

At the zero-target boundary, \(r\sin\phi+\cos\phi=Y/U\).
Write \(D(\phi)=gY/U-T'(b_z)\). Differentiating,
\[
 D'=g\left\{-\frac{Z\cos\phi}{UY}+\frac{YVf}{U^2}\right\}
                  -T''(b_z)Uf
 >-\frac{g(1.5)(.541)}{(1.812)(1.354)}+.808(1.2)>0.          \tag{39}
\]
The one right endpoint comparison is \(D(1.23)<-.040\).
Thus \(D<0\) on the whole early arc. Equations (36) and (39)
show that every feasible contact lowers its cost by increasing its
source coordinate until the target reaches zero. This deformation
stays on the target side and in \(0\le b\le b_z<.295\).

It remains to bound
\(K(\phi)=\phi-.0497-T(b_z(\phi))\).
Equations (37)–(38) give, uniformly,
\[
\begin{aligned}
 K''&=-T''(b_z)(Uf)^2+T'(b_z)Vf^2-T'(b_z)Uf'\\
 &>.808(1.2)^2+.749(.5)(.628)^2-1.069(1.915)(.631)>0.
\end{aligned}                                               \tag{40}
\]
At \(\phi=1.23\), direct substitution gives
\(K'<-.023\) and \(K>.89963\). The increasing derivative
is therefore negative throughout the earlier arc. Hence
\[
                          K(\phi)>.89963                   \tag{41}
\]
on every feasible angle through 1.23.

### 5.3. One tangent finishes the remaining early angles

On \(1.23\le\phi\le1.4\), the original geometric bound still gives
\(b<.6\), where \(T\) is concave. Its single tangent at \(b=.36\),
rounded upward, is
\[
 T(b)\le k+qb,\qquad
 q=.701150795,\quad k=.075705557.                            \tag{42}
\]
The original full-circle support then gives
\[
 F(\phi)=\phi-.0497-k+(g+q)/2+g\sin\phi
           -R\sqrt{g^2+q^2-2gq\cos\phi}.                   \tag{43}
\]
Its entire lower-half concavity follows from
\(N''+N/4\ge0\) and the original inequality
\(g\sin(\pi/2-.7)>R\sqrt{g^2+.85^2}/4\).
The two endpoint values in (43) are both greater than .89804.
Concavity proves the whole remaining range.

Equations (35), (41), and (43), Section 1's two support replacements,
and the cited note's remaining analytic arguments prove the complete
edge-3 negative outer to positive core class, including all four
original axes and both core pieces. The eight-angle tangent list
and the two source-coordinate ratio rows are unnecessary.

## 6. The complete edge-3 positive core to positive outer component

Use the original EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER hand note,
with \(g=1.0424\) and target label \(J=L\) from Section 2.2.
Section 1.5 already replaces its squared-polynomial gate.
The following three arguments replace its four early tangents,
five zero-contact derivative intervals, two further initial
zero-contact intervals, and thirty corner endpoint comparisons.

### 6.1. One quadratic support on the entire early angle range

On lower axis 1 the relaxed contact cost is
\[
 F(B,\phi)=\phi-.01449+g/2+g\sin\phi-J(B)
                    -gU(B)\sin\phi+gV(B)\cos\phi,
\]
where \(U=\sqrt{Q-(B+1/2)^2},V=B+1/2,r=V/U\).
This is a lower bound even when the relaxed source coordinate is
negative. The original derivative identity gives
\[
 F_B=g(r\sin\phi+\cos\phi)-J',\qquad F_{BBB}<0.               \tag{44}
\]
For \(\ell=\pi/2-.7\le\phi\le1.3\), \(F_B\) decreases with \(\phi\).
At \(\phi=1.3\), its values at \(B=.31,d\) exceed .012 and .121.
Its concavity in \(B\) therefore makes it positive on \([.31,d]\)
for every early angle. It suffices to bound \(0\le B\le.31\).

On this whole remaining range,
\[
 F_{BB}=gQ\sin\phi/U^3-J''>m,\qquad m=1.43.                  \tag{45}
\]
Indeed \(F_{BB}\) decreases with \(B\), by (44), and increases with
\(\sin\phi\); its value at \(B=.31,\phi=\ell\) exceeds 1.434.
Fix \(B_*=.24\), and let \(U_*,V_*,r_*,J_*,J_*'\) denote its exact
radical values. Strong convexity and a square completion give
\[
 F(B,\phi)\ge G(\phi)
 :=F(B_*,\phi)-\frac{\{g(r_*\sin\phi+\cos\phi)-J_*'\}^2}{2m}.
                                                               \tag{46}
\]
We prove \(G\) decreases on the whole early angle interval.
Its first derivative has just two harmonics:
\[
 G'=1+a_1\cos\phi+b_1\sin\phi+a_2\sin2\phi+b_2\cos2\phi,
                                                               \tag{47}
\]
where
\[
\begin{aligned}
 a_1&=-g(U_*-1)+gJ_*'r_*/m,&
 b_1&=-gV_*-gJ_*'/m,\\
 a_2&=g^2(1-r_*^2)/(2m),&
 b_2&=-g^2r_*/m.
\end{aligned}
\]
Both first-harmonic coefficients are negative. That harmonic is
convex on the angle range, and its two endpoint values are below
\(-1.43\). Moreover \(\sqrt{a_2^2+b_2^2}<.442\). Differentiating
(47) four times consequently gives the uniform bound
\[
                         G^{(5)}< -1.43+16(.442)=5.642.
                                                               \tag{48}
\]
At the single reference \(\phi_*=1.085\),
\[
 G'''(\phi_*)<-.2525,\qquad |G''''(\phi_*)|<.5241.
\]
Every angle in \([\ell,1.3]\) is within .215 of this reference.
Taylor's theorem with the global upper bound (48) therefore gives
\[
 G'''<-.2525+.5241(.215)+(5.642/2)(.215)^2<0.                 \tag{49}
\]
At the right endpoint, \(G''(1.3)>.025\) and \(G'(1.3)<-.042\).
Thus \(G''\) is positive, \(G'\) is increasing but negative, and
\(G\) decreases throughout. Finally,
\[
                         G(1.3)>.89864>\gamma.             \tag{50}
\]
Equations (44)–(50) prove the complete early axis-1 range with one
target-coordinate quadratic and one whole-angle derivative argument.

### 6.2. Whole-arc positivity at the zero-source contact

On \(1.3\le\phi\le\pi/2\), use the exact contact parametrization
(37), now writing its target coordinate as \(B_z=V-1/2\).
Define
\[
 D(\phi)=gY/U-J'(B_z).
\]
This is exactly the contact derivative whose positive sign is required
in the original §3.2. We show it is concave.
Monotonicity of \(U,V,Y,f,f'\), and the original radial derivatives,
give on the whole range
\[
\begin{gathered}
 1.5\le U<1.767,\quad .891<V<1.291,\quad1.29<Y<1.332,\\
 .799<f\le1,\quad .679<f'<.775,\quad B_z'=Uf>1.5(.799),\\
 -.273<B_z''=-Vf^2+Uf'<1.370,\\
 -.564<J''(B_z)<2.007,\qquad J'''(B_z)>4.47.
\end{gathered}                                               \tag{51}
\]
For the quotient \(q=Y/U\), differentiation gives
\[
 q''=Y''/U-2Y'U'/U^2-YU''/U^2+2Y(U')^2/U^3.
\]
Here \(Y',U'<0\), \(Y''\le Z\sin\phi/Y\), and
\(-U''=Uf^2+Vf'\). Hence
\[
 q''<
 \frac{1.5}{1.29(1.5)}
 +\frac{1.332}{1.5}
 +\frac{1.332(1.291)(.775)}{1.5^2}
 +\frac{2(1.332)(1.291)^2}{1.5^3}<3.58.                     \tag{52}
\]
The bounds in (51) also give
\(-J''B_z''<.78\): a positive product on the left requires opposite
signs, and the two possible products are bounded by
\(.564(1.370)\) or \(2.007(.273)\).
Consequently
\[
 D''=gq''-J'''(B_z')^2-J''B_z''
 <g(3.58)-4.47\{1.5(.799)\}^2+.78<0.                       \tag{53}
\]
The two endpoints satisfy \(D(1.3)>.128\) and
\(D(\pi/2)>.015\). Concavity proves \(D>0\) on the entire arc,
replacing all five former derivative intervals.

The initial zero-source cost
\(K_s(\phi)=\phi-.01449-J(B_z)\) also needs no two-interval argument.
On \([1.3,1.4]\), the same identities give
\[
 B_z''>1.686(.679)-1.036(.870)^2>0,
 \qquad B_z'(1.4)<1.467.
\]
Convexity of \(J'\), and its endpoint values at \(B_z(1.3)\) and
\(B_z(1.4)\), give \(J'<.659\) throughout. Therefore
\[
                  K_s'>1-.659(1.467)>0.                   \tag{54}
\]
The original endpoint \(K_s(1.3)>.9053\) finishes this initial part.
The original uniform concavity argument for \([1.4,\pi/2]\) remains
unchanged, as do its diagonal endpoint and upper-angle proofs.

### 6.3. One derivative shape proves both corner endpoint curves

The original strict concavity in the core coordinate reduces its last
corner case to the side join and the core diagonal, for
\(\ell\le\phi\le1.16\). For either fixed core endpoint write
\[
 u=1+(a_e+1/2)\cos\phi-(b_e-1/2)\sin\phi,\quad
 h=-u'>0,\quad K=(a_e+1/2)^2+(b_e-1/2)^2.
\]
Then \(h^2=K-(u-1)^2\),
\(1.12479<K\le(13/12)^2\), and \(1.368<u<1.7\).
The negative target label in height coordinates is
\[
 M(u)=m_0-1.49748u^2-.94721u
                 -(6.29979-1.89442u)\sqrt{Q-u^2}.
\]
The constant \(m_0\) has no effect on the next formulas. With
\(z=\sqrt{Q-u^2}\),
\[
 M'''=\frac{3Q(6.29979u-1.89442Q)}{z^5}>0,\qquad M''''>0.
                                                               \tag{55}
\]
Thus \(M'\) is convex and \(M''\), \(M'''\) increase.
For the endpoint cost \(H=\phi+M(u)+\text{constant}\),
\[
 H'''/h=-M'''h^2+3M''(u-1)+M'.                              \tag{56}
\]

Here are uniform bounds on the two height regimes. On
\(1.368\le u\le1.6\), the original radical formulas give
\[
 M''' >2.35,\quad M''<M''(1.6)<0,\quad M'<1.213.
\]
The bound on \(M'\) follows from convexity and its two height endpoints.
Since \(h^2>1.12479-.6^2\), (56) is strictly negative.
On \(1.6\le u\le1.7\), the same monotonicity and endpoint comparisons
give \(M'''>14,M''<2.26,M'<1.213\). Thus
\[
 H'''/h<
 -14(1.12479-.7^2)+3(2.26)(.7)+1.213<0.                    \tag{57}
\]
These height regimes use the change to a safely negative \(M''\);
they do not sample or partition the angle curve.

Both endpoint curves therefore have a concave first derivative.
Their left derivatives exceed .13. Such a curve first increases
and can subsequently decrease, so its minimum occurs at one of its
two angle endpoints. All four endpoint values exceed .918:
the side-join values exceed .91830 and .94110, and the core-diagonal
values exceed .91911 and .92854. This replaces all thirty former
endpoint-angle comparisons by whole-curve derivative coverage.

Together with Section 1.5 and the cited note's remaining analytic
arguments, §§6.1–6.3 prove the complete positive-core to positive-outer
edge-3 class, with its original axes, both core pieces, and all closed
boundaries.

## 7. The complete edge-2 negative outer to negative core component

This section replaces the scalar premises in the original
EDGE2_NEGATIVE_CORE_SIDE and EDGE2_NEGATIVE_CORE_CORNER hand notes.
It covers the full side and corner, including their common join.

### 7.1. The side discriminant has a whole-domain derivative proof

Keep the side note's valid quadratic minorant for the negative outer
label. Its remaining scalar target is positivity of
\[
\begin{aligned}
 E(x)={}&s^2(4kv-p^2)+2gps+4gkDs\\
        &-4\zeta(v+pD+kD^2)-g^2,\qquad0\le x\le.7,
\end{aligned}                                               \tag{58}
\]
where
\[
\begin{gathered}
 s=\cos x,\quad D=-.4+(13/12)\sin x+\tfrac12\cos x,\\
 p=.973417553,\quad k=.39,\quad g=.98439,\quad\zeta=.05334,\\
 v=v_0-x,\quad
 v_0=\pi/2-.790136935+.22042-.34492(7/12)-\gamma.
\end{gathered}
\]
This is the actual discriminant, before any Taylor-polynomial
substitution. Expanding its two harmonics and differentiating four
times gives exactly
\[
 E''''=A\cos x+B\sin x+16(C-.78x)\cos2x-12.372204\sin2x,
                                                               \tag{59}
\]
where
\[
\begin{gathered}
 A=1.2316256254413,\qquad B=-.15288005320042,\\
 C=2kv_0-p^2/2+gk-2\zeta k\{1/4-(13/12)^2\},
 \qquad -.12770<C<-.12769.
\end{gathered}
\]
On this entire range \(\sin2x,\cos2x\ge0\).
The positive function
\[
 h(x)=-16C\cos2x+12.372204\sin2x
\]
is concave, since \(h''=-4h<0\). Its two endpoint values exceed
2.04 and 12, respectively. Thus \(h>2.04\), and (59) gives
\[
                             E''''<1.232-2.04<0.           \tag{60}
\]

The following point bounds now suffice:
\[
\begin{gathered}
 E(0)>.000177,\quad E(.3)>.00339,\quad
 E(.5)>.00279,\quad E(.7)>.00389,\\
 E'''(.3)>1.4,\quad E'(.3)<-.013,\quad E''(.3)>.047,\\
 E'''(.5)<-1.1,\quad E'(.5)>.0086,\quad E''(.5)>.088,\\
 E(.426)>.00244,\qquad |E'(.426)|<.00004.
\end{gathered}                                               \tag{61}
\]
By (60), \(E'''\) decreases. On \([0,.3]\), \(E'\) is convex and
has a negative right endpoint; \(E\) has no interior minimum.
On \([.5,.7]\), \(E'\) is concave and has a positive left endpoint;
again \(E\) has no interior minimum.
On the middle range, \(E''\) is concave and both endpoints exceed
.047. The completed lower tangent quadratic at .426 therefore gives
\[
                   E>.00244-\frac{(.00004)^2}{.094}>0.      \tag{62}
\]
Together with the four endpoint bounds, this proves (58) everywhere.
The three derivative-covered ranges follow from one global fourth
derivative sign; there is no interval enclosure or coefficient row.
The original positive quadratic coefficient then proves every
lower-half axis-4 side state.

### 7.2. One height comparison replaces the five early corner rows

Use the common negative outer label in height coordinates:
\[
 M(u)=.369499372+.02363u^2-.055275u
                    -(.961795-.11055u)\sqrt{Q-u^2}.
                                                               \tag{63}
\]
Put \(k=.11055,V=.961795,z=\sqrt{Q-u^2}\).
Its first three derivatives are the original explicit formulas;
in particular
\[
 M'''=3Q(Vu-kQ)/z^5>0,\qquad
 q(u):=\frac{M''''}{M'''}=\frac V{Vu-kQ}+\frac{5u}{z^2}.
\]
On \(1.4\le u\le1.7\), this last function increases strictly:
\[
 q'=-\frac{V^2}{(Vu-kQ)^2}+\frac5{z^2}+\frac{10u^2}{z^4}
 >-1.11+2.55>0.                                            \tag{64}
\]
Define \(L(u)=M''-5.4M'+4.13904\).
Then \(L''=M'''(q-5.4)\), whose sign can change only from
negative to positive. Accordingly \(L'\) has no interior maximum.
Its two endpoint values are below \(-3.29\) and \(-.74\);
thus \(L'<0\) throughout. As \(L(1.4)<-.136\), we obtain
\[
                  M''<5.4M'-4.13904.                       \tag{65}
\]

On every early corner contact, \(\phi\le1.1\),
the actual height belongs to \((1.4,1.7)\) and \(\cos\phi>.45\).
Writing \(\delta=M'\cos\phi-.34492\), (65) gives
\(M''<12\delta\). The original radical derivatives give
\(M''>0\) on this height domain, so \(\delta>0\) as well.
The original exact core-coordinate formula is
\[
 f_{BB}=M''(\sin\phi+w\cos\phi)^2
       -12\delta(1+w^2)^{3/2}-.10668,\qquad0\le w\le1.
\]
Since the squared factor is at most \(1+w^2\), this is strictly
negative everywhere. The whole early corner therefore reduces to
its join and diagonal, without five angle ranges.

### 7.3. Uniform strong convexity of both endpoint curves

For either endpoint, write
\[
 u=1+A_*\cos\phi-B_*\sin\phi,\quad K=A_*^2+B_*^2>K_0=1.12479.
\]
The endpoint cost has curvature
\[
 H''=M''\{K-(u-1)^2\}-M'(u-1)\ge A(u),
\]
where
\[
 A(u)=M''J-M'(u-1),\qquad J=K_0-(u-1)^2,\quad1.33\le u\le1.7.
\]
We prove \(A''>.4\) on this whole height range.
With \(q_2=Q-u^2=z^2\), direct differentiation gives
\[
 A''=-.18904+\frac{\mathcal E(u)}{z^7},
\]
\[
\begin{aligned}
 \mathcal E(u)={}&3Q\bigl[
 \{V(Q+4u^2)-5kQu\}J-5(Vu-kQ)(u-1)q_2\bigr]\\
 &+8kuq_2^3-4Q(V-ku)q_2^2.                                \tag{66}
\end{aligned}
\]
For \(t=u-1.33\in[0,.37]\), expanding the single expression (66)
and grouping powers gives
\[
 \mathcal E(1.33+t)>
 9.4+t(52-81t-21t^4-9t^5-t^6)>9.4.                        \tag{67}
\]
The first inequality follows directly by subtracting its right
side: all power coefficients are nonnegative. The parenthesis
exceeds 21 on the full range, by replacing its negative powers
with their values at .37. As \(z<1.466\),
\[
 9.4>(.18904+.4)(1.466)^7
 \quad\Longrightarrow\quad A''>.4.                         \tag{68}
\]
At \(u=1.5\), \(A>.54319\) and \(|A'|<.046\).
One square completion yields everywhere
\[
 A(u)>.54319-\frac{.046^2}{.8}>.54>.4.                      \tag{69}
\]
Thus both endpoint curves have \(H''>.4\), replacing all three
former endpoint-curvature polynomials.
The original single reference for each endpoint consequently
gives \(H_{\rm diagonal}>.89777\) and \(H_{\rm join}>.9002\).

### 7.4. One whole late-corner bound replaces the remaining two ranges

For \(1.1\le\phi\le1.191\), use the same exact expression for
\(f_{BB}\). It increases with \(\phi\), at each fixed core coordinate.
To see this, put
\[
 L=\sin\phi+w\cos\phi,\quad
 h=-u_\phi=(A+1/2)\sin\phi+(B-1/2)\cos\phi.
\]
Differentiating gives
\[
\begin{aligned}
 \partial_\phi f_{BB}
 ={}&-M'''hL^2+2M''L(\cos\phi-w\sin\phi)\\
 &+12\{M''h\cos\phi+M'\sin\phi\}(1+w^2)^{3/2}.
\end{aligned}
\]
Here \(L^2\le1+w^2\), and
\(2L(\cos\phi-w\sin\phi)\ge-(1+w^2)\).
The whole late rectangle has
\[
 1.33<u<1.492,\quad M'>.909,\quad
 0<M''<1.22,\quad M'''<3.2,\quad h<1.09,\quad\sin\phi>.89.
\]
Discarding a positive term therefore gives
\[
 \partial_\phi f_{BB}>
 (1+w^2)\{-3.2(1.09)-1.22+12(.909)(.89)\}>0.                \tag{70}
\]
It suffices to bound the entire final-angle core at \(\phi=1.191\).
There \(u<1.402,M''<.986,\delta>-.0054\), and
\(\sin\phi+\cos\phi<1.3\). Since \(12(1+w^2)^{3/2}<34\),
\[
 f_{BB}<.986(1.3)^2+34(.0054)-.10668<7/4.                   \tag{71}
\]
This bound holds everywhere in the late rectangle by (70).

The core-corner length is less than .059. The usual chord correction
for \(f''\le7/4\) loses at most \((7/4)(.059)^2/8\).
Equation (69) and the original positive diagonal derivative at 1.1
show that both endpoint costs on the whole late range exceed .89849.
Consequently
\[
 f>.89849-\frac{(7/4)(.059)^2}{8}
   >.89772>\gamma.                                         \tag{72}
\]
The original two late angle ranges are unnecessary.

The original side and corner axis exclusions and support bounds,
combined with §§7.1–7.4, prove the complete negative-outer to
negative-core edge-2 class with no scalar polynomial or interval
table remaining.

## 8. The complete edge-3 negative core to positive outer component

We now replace the last scalar premises in
EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER: the three derivative
polynomials in its §2.2 and the four zero-contact angle intervals in
its §3.2. Its upper circle support is already covered by Section 1.2.
Write
\[
 g=.98439,\quad v=.05334,\quad e=.22042-.34492(7/12),
\]
\[
 J(B)=.03965+3.85510B-1.49748B^2-1.89442A(B)B,
 \qquad A(B)=\sqrt{Q-(B+.5)^2}-.5.
\]
The original bounds \(J'>0\) and \(J'''>1\) use only the explicit
radical derivatives and their whole-domain monotonicity.

### 8.1. One uniform derivative estimate replaces three polynomial rows

Keep the original exact angle minimization. With
\[
 U=A+.5,\quad V=B+.5,\quad P=U-1,\quad T=P^2+V^2,
 \quad S=\sqrt{h^2T-1},\quad\beta=\arctan(V/P),
\]
it gives the lower bound
\[
 E_h(B)=\beta+\arctan S-S-e-\frac{(g-h)^2}{4v}
                         +\frac h2-J(B),                   \tag{73}
\]
using \(h=g\) on \(0\le B\le.45\) and \(h=.975\) on
\(.45\le B\le.54\). The contact and all roots in (73) are in
the domains justified by the original geometric reduction.

For clarity, here are the exact derivative polynomials in the height
variable \(u=U\):
\[
\begin{gathered}
 T=Q+1-2u,\qquad W=Q-u^2,\qquad Z=h^2T-1,\\
 E_0=2u^2-4Qu+Q(Q+1),\qquad E_0'=4u-4Q,\\
 A_0=E_0u^2T-W\{E_0'uT-E_0(3T-4u)\},\\
 D_0=u^5T^3-A_0,
\end{gathered}
\]
\[
\begin{aligned}
 C_h={}&3h^2QuT^2Z-h^4Wu^2T^2-4h^2Wu^2TZ\\
       &+3QT^2Z^2-6QuTZ^2+8Wu^2Z^2.                       \tag{74}
\end{aligned}
\]
For \(G_h=\beta+\arctan S-S\), the original direct identity is
\[
 G_h'''=\frac{A_0S^3-VC_h}{u^5T^3S^3},                    \tag{75}
\]
where these derivatives are with respect to \(B\).

Put \(t=u-1.68\). On the entire range \(0\le t\le.235\),
expansion and grouping of the single polynomial \(D_0\) give
\[
 D_0(1.68+t)>
 27+t(76-206t-84t^5-49t^6-8t^7)>27.                       \tag{76}
\]
The difference in the first inequality has nonnegative power
coefficients and a strictly positive constant. The bracket in the
second inequality is positive by bounding each negative power by
its value at .235.

For every \(a=h^2\in[.95,.97]\), the polynomial (74) satisfies
the uniform bound
\[
 C_h'(1.68+t)\le-39+372t-1169t^2+333t^3
              \le-39+372t-1090t^2<0.                     \tag{77}
\]
Here the prime denotes the height derivative. To verify the first
inequality directly with the parameter still free, expand (74) in
\(t\) and \(a\). At \(a=.95\) the resulting derivative is bounded
above by
\[
 -39+342.84t-1169t^2+306.5t^3.
\]
Its derivative with respect to \(a\) is at most
\(1443t+1323t^3\) for \(.95\le a\le.97\):
its coefficients at degrees \(0,2,4,5\) in \(t\) are negative,
and the remaining two coefficients are increasing linear functions
bounded above by 1443 and 1323. Integrating over a length at
most .02 proves the first inequality in (77).
The second uses \(1169-333(.235)>1090\); the final quadratic is
strictly negative because \(4(39)(1090)>372^2\).
These are inequalities for one printed polynomial with a free
parameter, with no coefficient table or subdivision.

Thus each \(C_h\) decreases throughout the required height range.
The two right endpoint comparisons
\[
 C_g(1.915)>.05312,\qquad C_{.975}(1.74)>2.52              \tag{78}
\]
prove its positivity on \([1.68,1.915]\) and \([1.68,1.74]\),
respectively. These are the whole height ranges needed in (73).
Equations (75)–(78) imply \(G_h'''<1\); since \(J'''>1\),
\[
                              E_h'''<0.                  \tag{79}
\]

The original point comparisons now finish the whole target domain.
On \([0,.32]\), (79) and \(E_g''(.32)>.22\) give
\[
 E_g>.89776733-\frac{(.000006)^2}{.44}>\gamma
\]
by square completion at \(B=.3035\).
On \([.32,.4]\), the concave derivative \(E_g'\) has positive
endpoints. On \([.4,.45]\), \(E_g''<0\) and the two cost endpoints
exceed .8985. Finally \(E_{.975}''(.45)<0\); (79) makes the whole
last range concave, with both cost endpoints exceeding .89807.
These derivative-covered ranges finish every lower axis-1 contact.

### 8.2. One whole zero-curve derivative replaces four angle intervals

The original lower axis-2 reduction is decreasing in the angle
along each fixed-target contact. Its only remaining middle zero-source
curve is contained in \(1.32\le\phi\le1.48\). On that whole
enlarged interval, put
\[
\begin{gathered}
 m=\tfrac12\sin\phi+\tfrac{13}{12}\cos\phi,\qquad
 w=\tfrac{13}{12}\sin\phi-\tfrac12\cos\phi>0,\\
 U=1+m,\quad V=\sqrt{Q-U^2},\quad B_z=V-\tfrac12,\qquad
 K(\phi)=\phi-e-J(B_z).
\end{gathered}                                             \tag{80}
\]
Here
\[
 U'=-w,\quad U''=-(U-1),\quad
 w^2=\frac{205}{144}-(U-1)^2,\qquad1.59<U<1.76.             \tag{81}
\]
Use the same negative-label height function as in §6.3:
\[
 M(U)=m_0-1.49748U^2-.94721U
                 -(6.29979-1.89442U)\sqrt{Q-U^2}.
\]
Then \(K=\phi+M(U)+\text{constant}\).
With \(z=\sqrt{Q-U^2}\), its explicit third derivative is
\[
 M'''=\frac{3Q(6.29979U-1.89442Q)}{z^5}>0,
\]
and its logarithmic derivative has the whole-domain lower bound
\[
 \frac{M''''}{M'''}
 =\frac{6.29979}{6.29979U-1.89442Q}+\frac{5U}{Q-U^2}
 >1.7+5.7>7.                                             \tag{82}
\]
The first summand decreases, so its lower bound is checked at
1.76; the second increases, so its lower bound is checked at 1.59.
At \(U=1.59\),
\[
 .96<M'<1,\qquad -.234<M''<0,\qquad M'''>13.
\]
In particular \(M''\) increases and
\(M'>.96-.234(.17)>.92>0\) on the entire height range.

For completeness, (82) gives the required stronger comparison
without enclosing these derivatives separately on short intervals.
First \(M'''-M''\) is positive and increasing, since its derivative
is greater than \(6M'''>0\). Therefore \(M'''-2M'\) is positive
and increasing: its derivative is greater than
\(7M'''-2M''>5M'''>0\).
Finally \(M'''-5M''-2M'\) is positive at 1.59 and has derivative
greater than \(2(M'''-M'')>0\). These three facts imply
\[
                   M'''>2M'+5\max(M'',0).                 \tag{83}
\]

Differentiating the whole curve (80) gives
\[
 \frac{K'''}w=-M'''w^2+3M''(U-1)+M'.                      \tag{84}
\]
Throughout (81), \(2w^2>1\) and \(5w^2>3(U-1)\).
As \(M'>0\), (83) proves that (84) is strictly negative,
whether \(M''\) is positive or negative. Thus
\[
                         K'''<0
       \quad\hbox{on all of }[1.32,1.48].                 \tag{85}
\]

Only one strong-convexity reference is now needed. The exact
trigonometric and radical comparisons give
\[
 \begin{gathered}
 K''(1.4)>.77,\qquad K(1.387)>.89995,\qquad
 |K'(1.387)|<.0003,\\
 K'(1.4)>.011,\qquad K'(1.48)>.008.
 \end{gathered}
\]
On \([1.32,1.4]\), (85) implies \(K''>.77\), so
\[
                 K>.89995-\frac{(.0003)^2}{1.54}
                         >.89994>\gamma.                 \tag{86}
\]
On \([1.4,1.48]\), \(K'\) is concave with positive endpoints.
The cost therefore increases from its already bounded value at
1.4. This proves the whole zero curve and replaces all four
former midpoint intervals.

The original small-target branch reduces to the axis-1 estimate
already proved in §8.1. Its large-target branch imports the
positive-core zero curve from the original
EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER §5.2; that branch was already
table-free and is retained, with its exact label difference
\(e-.01449=709/150000\).
The original upper axis-1 deformation and upper axis-2 strip
use monotonic contacts with all exits included. The remaining upper
axis-2 support is Section 1.2, and upper axis 4 uses its original
whole-interval concavity bound. Axis 3 was excluded by the original
norm inequality.
Thus §§8.1–8.2 and Section 1 complete this last mixed class,
including all four original signed axes and both core pieces.

## 9. Complete nineteen-class assembly and dependency scope

We use the exact states, labels, signs, and reflection identity in
WRONG_0011011_WHOLE_WORD_HAND_PROOF. Let the seven boundary states
come from an actual packing after the central-core and fixed-axis
boundary reductions and the complete frame-concentration theorem.
The physical frame lifts then lie in a common interval of length
less than .7, and the ordered center gaps exceed \(19/25\).
Apply HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION to this same cycle before
any wrong-word or candidate-word cut. It excludes the primary
separator branches of every zero-quarter edge.

This last input is essential to the stated scope of Section 2:
its original Family IV is absent in the actual cycle.
We do not assert that this omitted primary branch satisfies the
same label inequality for an unrestricted isolated pair.
The zero-primary exclusion uses frame concentration and the
closed-tour geometry, so this assembly does not depend on
wrong-word exclusion, candidate capture, or a mismatch threshold.

Here is the entire mixed reflection cover. A section number refers
to this note and replaces precisely the scalar premises in the
original whole-family proof. “Original” means that the indicated
whole-family proof already has no continuous interval or coefficient
table. All manuscript stems below have the prefix
WRONG_0011011 and suffix HAND_PROOF.md.

| Edge | Signs | Core to outer | Outer to core |
|---:|:---:|---|---|
| 0 | \(++\) | §2 + SAME_SIGN_MIXED_ZERO | §2 + SAME_SIGN_MIXED_ZERO |
| 0 | \(+-\) | §4 + OPPOSITE_MIXED_ZERO | §4 + OPPOSITE_MIXED_ZERO |
| 2 | \(--\) | Original EDGE2_NEGATIVE_CORE_TO_OUTER | §7 + EDGE2_NEGATIVE_CORE_SIDE and EDGE2_NEGATIVE_CORE_CORNER |
| 2 | \(-+\) | §1 + EDGE2_CORE_TO_POSITIVE_OUTER | §1 + EDGE2_OUTER_TO_POSITIVE_CORE |
| 3 | \(++\) | §§1,6 + EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER | Original EDGE3_FOUR_WHOLE_MIXED_FAMILIES |
| 3 | \(+-\) | Original EDGE3_FOUR_WHOLE_MIXED_FAMILIES | Original EDGE3_FOUR_WHOLE_MIXED_FAMILIES |
| 3 | \(-+\) | §§1,8 + EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER | §§1,5 + EDGE3_OUTER_TO_POSITIVE_CORE |
| 3 | \(--\) | Original EDGE3_FOUR_WHOLE_MIXED_FAMILIES | §§1,3 + EDGE3_OUTER_TO_NEGATIVE_CORE |
| 4 | \(++\) | §2 + SAME_SIGN_MIXED_ZERO | §2 + SAME_SIGN_MIXED_ZERO |
| 4 | \(+-\) | §4 + OPPOSITE_MIXED_ZERO | Reflection of the core-to-outer entry |

The table contains nineteen representatives: both radial orders
in its first nine rows and one in its final row.
Reflection of the plane followed by reversal of the center order
sends
\[
 (i,\sigma,\tau,K_s,K_t)
       \longmapsto(1-i,-\tau,-\sigma,K_t,K_s).
\]
The word and the corrected cost are invariant, by the exact label
identity \(L_{2-i}^{\sigma}=L_i^{-\sigma}\). The original signed
axes are permuted by \((1\ 3)(2\ 4)\).
Every mixed reflection class has two members, so the cover gives
all thirty-eight directed mixed cases and all 152 of their original
directed axis branches. The primary zero branches are geometrically
absent as just explained; every other branch has the strict cost bound.

Two shared imports require explicit mention. The original
ALIGNED_MIXED_QUARTER proves all its stated mixed cases exactly
at \(\phi=\pi/2\), by scalar derivative signs, concavity, and
one-point strong convexity. EDGE2_MIXED_QUARTER_STRIP continues the
relevant original separators throughout
\(|\phi-\pi/2|\le.02\), including each side/corner and zero-coordinate
exit. Both are already table-free. They are used only on their
stated closed domains, while their parent notes and the replacements
above cover all other angles.

The two “Original” whole-family imports in the cover have likewise
been read on their full domains: EDGE2_NEGATIVE_CORE_TO_OUTER
uses one strongly convex scalar and whole-axis monotonicity;
EDGE3_FOUR_WHOLE_MIXED_FAMILIES uses circular chords, whole-domain
monotonicity, and concavity. Neither contains a remaining continuous
interval enclosure, Bernstein row, or sampled-domain premise.

It follows that every mixed edge in an actual 0011011 boundary
cycle has
\[
 \phi_i+\sigma_iL_i^{\sigma_i}(a_i,b_i)
       -\sigma_{i+1}L_{i+1}^{\sigma_{i+1}}(a_{i+1},b_{i+1})
                         >.89765.                         \tag{87}
\]
This includes the complete core side and corner, their common join,
the full outer arc, closed angle endpoints, zero transverse
coordinates, and every nearest-axis tie.
At a zero coordinate or a tie, choose one signed representation
for the vertex and use it on both incident edges. The labels can
then telescope in the whole-word proof even when alternative signed
formulas have different values at the same geometric state.

Equation (87) is the complete mixed component. Combining it with
the separate core/core and outer/outer components gives the seven
strict edge inequalities used in the whole-word sum. No numerical
role-box exclusion, continuous mesh, or Bernstein coefficient row
from a mixed source note remains a premise of that sum.
