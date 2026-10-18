# Whole middle/middle boundary-pair inequality

## 1. Statement and exact conventions

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 \beta=\frac9{50},\qquad \gamma=\frac{557}{625}=.8912.
\]
A middle state has nonnegative local coordinates \((a,b)\) on the outer
boundary arc
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\qquad
 \frac14\le\frac ba\le\frac37.
\]
Its label is
\[
 M(b)=c_M+p\,a(b)+q\,b,\qquad
 c_M=-2.143075,\quad p=1.489593,\quad q=1.580219,
 \quad a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12.
\]
All terminating decimals in this note are exact rationals.

For signs \(\sigma,\tau\in\{-1,1\}\), the centers in their own square frames
are \((a,-\sigma b)\) and \((A,-\tau B)\). Put
\[
 \alpha_s=\sigma\arctan(b/a),\qquad
 \alpha_t=\tau\arctan(B/A),\qquad
 \phi=\delta+\alpha_t-\alpha_s,
\]
where \(\delta\) is the positive center-ray gap. Write
\[
 s=\sin\phi,\quad c=\cos\phi,\quad
 h=\frac{|s|+|c|-1}{2},\quad W=1+h.
\]
The corrected pair cost is
\[
 {\cal C}=\phi-\beta h+\sigma M(b)-\tau M(B).                 \tag{1}
\]

The hypotheses are those of the four-type hand frame theorem: the two
squares are an adjacent exterior boundary pair, their true interiors are
disjoint, and
\[
 .76<\delta<3\pi/4.
\]
The already proved cap and backward-axis exclusions leave the following
two source-owned separating inequalities, and their target-owned images:
\[
 \begin{array}{ll}
 {\mathsf F}:&\sigma b+A\sin\phi-\tau B\cos\phi\ge W,\\
 {\mathsf P}:&a-A\cos\phi-\tau B\sin\phi\ge W.
 \end{array}                                                \tag{2}
\]
Here \({\mathsf F}\) is the positive transverse source axis and
\({\mathsf P}\) is the inward primary source axis. Reflection followed by
reversal sends
\[
 (b,B,\sigma,\tau)\longmapsto(B,b,-\tau,-\sigma),
\]
preserves \(\phi\) and (1), and sends a target-owned inequality to one in
(2). Thus it suffices to prove the four sign cases for each source axis.

**Theorem.** Under these hypotheses,
\[
                         {\cal C}>.8912.                    \tag{3}
\]
The proof below covers all eight source/sign cases. It uses contact
concavity, two explicit polynomial rows, and rational endpoint estimates.
It has no numerical optimization or subdivision premise.

## 2. Bounds used throughout

Write the arc endpoints as \((a_l,b_l)\) and \((a_h,b_h)\), with
\(b_l=a_l/4\) and \(b_h=3a_h/7\). Squaring gives
\[
\begin{array}{c|cc}
 &\text{lower bound}&\text{upper bound}\\ \hline
a_l&1.298747247&1.298747249\\
a_h&1.199256060&1.199256062\\
M(b_l)&.3046&.30461\\
M(b_h)&.4555&.455511 .
\end{array}                                                 \tag{4}
\]
In particular
\[
 .3246<b_l<b_h<.513966884<.514.
\]
Set
\[
 r(b)=\frac{b+\tfrac12}{a(b)+\tfrac12}.
\]
Differentiation of the circle equation gives
\[
 a'=-r,\qquad r'=\frac{Q}{(a+\tfrac12)^3},\qquad
 M'=q-pr,\qquad M''=-pr'<0.
\]
The endpoint brackets imply
\[
 .458<r<.597,\qquad 0<r'<.8,\qquad
 .69<M'<.898,\qquad r(b_l)<.459.                              \tag{5}
\]
Consequently \(M\) is positive, increasing, and strictly concave.

Alternating arctangent sums give
\[
 \arctan(3/7)-\arctan(1/4)<.16,\qquad
 \arctan(3/7)<.405,\qquad \arctan(1/4)>.24.
\]
Hence
\[
\begin{array}{c|c}
(\sigma,\tau)&\text{necessary lower bound on }\phi\\ \hline
(+,+),(-,-)&\phi>.6\\
(+,-)&\phi>-.05\\
(-,+)&\phi>1.24 .
\end{array}                                                 \tag{6}
\]
Also \(0\le h<.21\), so \(\beta h<.0378\).
The elementary label bounds therefore give all of the following tails:
\[
\begin{array}{c|c|c}
\text{signs or lower cost used}&\text{range}&\text{lower bound}\\ \hline
\text{same signs}&\phi\ge1.09&
 1.09-.0378-.455511+.3046>.8912\\
(+,-)&\phi\ge.32&.32-.0378+2(.3046)>.8912\\
(-,+)&\phi\ge1.85&1.85-.0378-2(.455511)>.8912.
\end{array}                                                 \tag{7}
\]
The last row also applies after replacing a positive source label by its
negative, when this weakens a primary-axis cost.

## 3. The whole positive/negative transverse contact regime

This section proves (3) for \({\mathsf F}\), \((\sigma,\tau)=(+,-)\).
By (7), only
\[
                         -.05<\phi\le.32                  \tag{8}
\]
requires proof. The separating inequality is
\[
                         b+A\sin\phi+B\cos\phi\ge W.         \tag{9}
\]

### 3.1 Reduction to true contact and to an arc endpoint

The left side of (9) increases with \(b\) and with \(B\), since
\[
 D=\cos\phi-r(B)\sin\phi
 >1-\frac{.32^2}{2}-.597(.32)>.75.                           \tag{10}
\]
The point \(b=B=b_l\) is infeasible throughout (8). For negative \(\phi\)
its left side is at most \(2b_l<1\le W\). For nonnegative \(\phi\) its
left side minus \(W\) is
\[
 b_l-\tfrac12+(a_l-\tfrac12)\sin\phi+(b_l-\tfrac12)\cos\phi
 <-.175+.799(.32)-.175(1-.32^2/2)<0.
\]
Every feasible pair can therefore be moved down in one or both transverse
coordinates until equality holds in (9), while remaining on the middle
arcs. Since \(M'>0\), this does not increase its cost.

At contact solve for the source coordinate:
\[
 b(B,\phi)=W-a(B)\sin\phi-B\cos\phi,\qquad
 b_B=-D,\qquad b_{BB}=r'(B)\sin\phi.
\]
For fixed \(\phi\), its feasible \(B\)-set is a closed interval, because
\(b_B<0\). Its contact cost has second derivative
\[
 \frac{\partial^2{\cal C}}{\partial B^2}
 =M''(b)D^2+r'(B)\{M'(b)\sin\phi-p\}<0.                     \tag{11}
\]
Indeed the first term is negative; for \(\phi\le0\) the braces are
negative, and for \(\phi\ge0\) they are at most \(.898-p<0\).
A concave function on an interval is minimized at an endpoint.
Thus a minimum occurs when **at least one of \(b,B\) is an arc endpoint**.

### 3.2 The exact parallel endpoint value

At \(\phi=0\), contact is \(b+B=1\). The feasible interval is
\[
                 1-b_h\le B\le b_h,
\]
because \(b_l<1-b_h<b_h\). Concavity gives the two symmetric endpoints,
with common cost
\[
 E=2c_M+q+p\{a_h+a(1-b_h)\}.                                \tag{12}
\]
The following is a strict rational square check:
\[
 (1.215616124+\tfrac12)^2+
 \left(\tfrac32-\frac37(1.199256060)\right)^2<Q.
\]
Thus \(a(1-b_h)>1.215616124\), and (4) gives
\[
 E>
 2(-2.143075)+1.580219
 +1.489593(1.199256060+1.215616124)
 =.891245701181112>.89124>.8912.                             \tag{13}
\]

### 3.3 Negative angles deform toward the parallel minimum

At a negative-angle contact, (9) implies \(b+B>1\). Hence both
coordinates exceed \(1-b_h>.486\), so neither is the lower arc endpoint.
In the endpoint minimum from (11), one coordinate must therefore equal
\(b_h\). Along such a contact branch the other coordinate moves down to
\(1-b_h\) as \(\phi\) increases to zero, and stays inside the middle arc.

For \(\phi\le0\), put
\[
 N_-=(A+\tfrac12)\cos\phi+(\tfrac12-B)\sin\phi.
\]
Since \(b,B\in(.486,.514)\),
\[
 N_->1.699(1-.05^2/2)-.014(.05)=:n_->0.                     \tag{14}
\]
If \(B\) is fixed, then \(b_\phi=-N_-\) and
\[
 {\cal C}_\phi
 =1+.09(\cos\phi+\sin\phi)-M'(b)N_-
 <1.09-.69n_-<0.                                            \tag{15}
\]
If \(b\) is fixed, implicit differentiation gives
\(B_\phi=-N_-/D\), where \(D<1+.597(.05)\), and therefore
\[
 {\cal C}_\phi
 <1.09-\frac{.69n_-}{1+.597(.05)}<0.                         \tag{16}
\]
Both endpoint branches decrease in cost toward \(\phi=0\), proving
\({\cal C}\ge E\) for every negative-angle contact minimum.

### 3.4 Positive angles also deform toward the parallel minimum

For \(0\le\phi\le.32\), put
\[
 N_+=(A-\tfrac12)\cos\phi+(\tfrac12-B)\sin\phi .
\]
It satisfies
\[
 0<.699(1-.32^2/2)-.014(.32)<N_+
 <.799+.176(.32).                                           \tag{17}
\]
When \(B\) is fixed, \(b_\phi=-N_+\), so
\[
 {\cal C}_\phi
 =1-.09(\cos\phi-\sin\phi)-M'(b)N_+
 >.91-.898\{.799+.176(.32)\}>0.                              \tag{18}
\]

For fixed \(b\), put \(t=\tan\phi\). The Taylor estimates give
\(0\le t<.332\), and
\[
 \frac{N_+}{D}=J(B)
 =\frac{A-\tfrac12+(\tfrac12-B)t}{1-r(B)t}.
\]
At fixed \(t\), write its numerator and denominator as \(N_0,D_0\).
Then
\[
 N_0'=-r-t,\qquad D_0'=-r't,\qquad
 J'=\frac{(-r-t)D_0+N_0r't}{D_0^2}<0,                       \tag{19}
\]
because
\[
 D_0>.801,\quad 0<N_0<.858,\qquad
 .8(.332)(.858)<.458(.801).
\]
Both \(M'(B)\) and the positive function \(J(B)\) decrease with \(B\).
Their product is therefore largest at \(b_l\), where
\[
 M'(B)J(B)
 <\frac{.898\{.799+.176(.332)\}}{1-.459(.332)}
 <.91.                                                      \tag{20}
\]
The fixed-source derivative consequently satisfies
\[
 {\cal C}_\phi
 =1-.09(\cos\phi-\sin\phi)-M'(B)J(B)>0.                      \tag{21}
\]

Every endpoint branch can now be followed backward to zero with
nonincreasing cost. If the fixed coordinate is \(b_h\), the other one
increases to \(1-b_h\) and stays in its arc. If the fixed coordinate is
\(b_l\), the other one may first reach \(b_h\); switch there to the branch
with that upper coordinate fixed, then continue to zero. These are the
only possible obstructions, since both contact coordinates increase when
the positive angle decreases. Equations (18) and (21) apply on both sides
of the switch. This proves \({\cal C}\ge E\) on all of (8).

Together with (13) and the tail in (7), the **entire**
\({\mathsf F}(+,-)\) case is closed.

## 4. The other transverse source cases

### 4.1 Negative source signs are impossible before their direct tails

For \(\sigma=-1\), all relevant angles satisfy \(0<\phi<\pi\).
Irrespective of the target sign,
\[
\begin{split}
 -b+A\sin\phi-\tau B\cos\phi-W
 &\le-b-\tfrac12+(A-\tfrac12)\sin\phi
       +(B-\tfrac12)|\cos\phi|\\
 &<-.8246+.799\sin\phi+.014|\cos\phi|<0,
\end{split}
\]
where the last inequality follows from
\[
                         .799^2+.014^2<.8246^2.             \tag{22}
\]
Thus neither \({\mathsf F}(-,+)\) nor \({\mathsf F}(-,-)\) can separate
before the corresponding direct tail (7).

### 4.2 Positive source and positive target

Here \(\phi>.6\), and only \(\phi\le1.09\) remains. Apply the separating
inequality with multiplier \(\lambda=.87\). The source expression
\(M(b)-\lambda b\) is concave. The exact endpoint comparison
\[
 .87(b_h-b_l)>M(b_h)-M(b_l)
\]
puts its minimum at \(b_h\), so
\[
 M(b)-.87b\ge M(b_h)-.87b_h
 >.4555-.87(.513966884)=:m_F=.00834881092.                    \tag{23}
\]
For any coefficients \(U,V\), the whole-circle support bound is
\[
 UA+VB\ge-\frac{U+V}{2}-R\sqrt{U^2+V^2}.                    \tag{24}
\]
It is valid for every point of the restricted middle arc.

With \(U=-p-\lambda\sin\phi\) and
\(V=-q+\lambda\cos\phi\), (23) and (24) imply
\[
 {\cal C}\ge
 \phi+K_F+(\lambda-.09)\sin\phi-.09\cos\phi
 -R\sqrt{p^2+q^2+\lambda^2+2\lambda(p\sin\phi-q\cos\phi)},
                                                                    \tag{25}
\]
where
\[
 K_F=.09+m_F-c_M+(p+q+\lambda)/2,\qquad \lambda=.87.
\]
The first polynomial row in Section 6 proves that (25) exceeds .8912
on the whole interval \([.6,1.09]\). This finishes \({\mathsf F}(+,+)\).

## 5. The primary source cases

The primary separator is independent of \(\sigma\).
Because \(M>0\), replacing the source contribution \(+M\) by \(-M\)
only lowers the cost. It therefore suffices to treat the negative source
label for each target sign.

For multiplier \(\lambda=1\), the source function \(-M(b)-a(b)\)
is strictly decreasing:
\[
 \frac{d}{db}[-M-a]=(p+1)r-q
 <(p+1)(.597)-q<0.
\]
Its lower bound is consequently
\[
                  -M(b)-a(b)>-.455511-1.199256062=:m_P.      \tag{26}
\]

### 5.1 Negative target

For \(-.05<\phi<0\), the primary margin is at most
\[
 .799-1.699\cos(.05)<0.
\]
For \(0\le\phi\le1.05\), it is at most
\[
 .799-1.699\cos\phi+.014\sin\phi
 \le.799-1.699\cos(1.05)+.014<0.                             \tag{27}
\]
For \(\phi\ge1.09\), the same-sign lower-cost tail in (7) applies.

It remains to consider \([1.05,1.09]\). With \(\lambda=1\), the target
support coefficients are \(p+\cos\phi>0\) and \(q-\sin\phi>0\).
The target support function is concave in \(B\), so its minimum is
at one of the two middle endpoints \(j=l,h\). Using (26), each cost is
bounded below by
\[
 \phi+.59-.455511-1.199256062+M(b_j)
   +(.41-b_j)\sin\phi+(.41+a_j)\cos\phi.                     \tag{28}
\]
On this short interval use \(\phi\ge1.05\),
\(\cos\phi\ge C_{10}(1.09)\), and
\[
 (.41-b_j)\sin\phi\ge\min(0,.41-b_j).
\]
With the endpoint bounds (4), the resulting two rational numbers both
exceed \(1.07\). Thus (28) is greater than .8912 throughout the interval.

### 5.2 Positive target

The necessary angle is positive. On the entire first quadrant,
\[
 a-A\cos\phi-B\sin\phi-W
 <.799-1.699\cos\phi-.8246\sin\phi<0,                        \tag{29}
\]
since \(\sin\phi+\cos\phi\ge1\). No separator is possible there.
The negative/positive lower-cost tail applies from \(\phi=1.85\).

On \([\pi/2,1.85]\), use (26) and (24), now with
\[
 U=-p+\cos\phi,\qquad V=-q+\sin\phi .
\]
The result is
\[
 {\cal C}\ge
 \phi+K_P-.09\sin\phi-.91\cos\phi
 -R\sqrt{p^2+q^2+1-2(p\cos\phi+q\sin\phi)},                 \tag{30}
\]
where
\[
                       K_P=.09+m_P-c_M+(p+q+1)/2.
\]
The second polynomial row proves (30) greater than .8912 on
\([1.57,1.85]\), which includes the required interval because
\(1.57<\pi/2<1.58\). This closes both positive-target primary cases.

## 6. The two explicit polynomial rows

For \(0\le x\le1.85\), use the alternating Taylor polynomials
\[
 S_7\le\sin x\le S_9,\qquad C_{10}\le\cos x\le C_8,
\]
where
\[
 S_n(x)=\sum_{\substack{j\le n\\j\ {\rm odd}}}
       (-1)^{(j-1)/2}\frac{x^j}{j!},\qquad
 C_n(x)=\sum_{\substack{j\le n\\j\ {\rm even}}}
       (-1)^{j/2}\frac{x^j}{j!}.
\]

For row F, with the exact \(K_F,\lambda\) in (25), define
\[
\begin{split}
 T_F(x)&=x+K_F-\gamma+(\lambda-.09)S_7(x)-.09C_8(x),\\
 V_F(x)&=p^2+q^2+\lambda^2+
           2\lambda\{pS_9(x)-qC_{10}(x)\},\\
 P_F(x)&=T_F(x)^2-QV_F(x).
\end{split}                                                \tag{31}
\]
For row P, define
\[
\begin{split}
 T_P(x)&=x+K_P-\gamma-.09S_9(x)-.91C_8(x),\\
 V_P(x)&=p^2+q^2+1-2\{pC_{10}(x)+qS_7(x)\},\\
 P_P(x)&=T_P(x)^2-QV_P(x).
\end{split}                                                \tag{32}
\]
Every trigonometric replacement has the displayed lower-bound direction
for \(T\), and the upper-bound direction for the squared norm \(V\).

Here are strict lower bounds for the Bernstein coefficients of \(P\)
on the full displayed intervals. The denominator of every listed number
is \(10^6\).

| Row | Interval | Bernstein degree | Positive integer coefficient lower bounds |
|---|---|---:|---|
| F | \([.6,1.09]\) | 16 | 97837, 100029, 101671, 102928, 103966, 104945, 106025, 107361, 109106, 111414, 114433, 118313, 123199, 129239, 136578, 145361, 155733 |
| P | \([1.57,1.85]\) | 18 | 248977, 257702, 265257, 271671, 276972, 281190, 284354, 286491, 287630, 287799, 287024, 285333, 282752, 279306, 275022, 269924, 264037, 257385, 249991 |

Every Bernstein coefficient of \(T_F\), at degree 8 on its interval,
is greater than \(4\). Every Bernstein coefficient of \(T_P\), at degree
9 on its interval, is greater than \(3\). Thus \(T>0\) and \(P>0\).
Since \(V\) bounds a nonnegative squared norm from above,
\[
                      T>R\sqrt V
\]
proves the claimed strict cost inequalities.

For clarity, the coefficients can be reconstructed without a numerical
procedure. If \(P(x)=\sum_{i=0}^n p_i x^i\) and \(x=l+(r-l)y\), first put
\[
 d_j=\sum_{i=j}^n p_i\binom{i}{j}l^{\,i-j}(r-l)^j.
\]
Its degree-\(n\) Bernstein coefficient is
\[
                 B_k=\sum_{j=0}^k
                       d_j\frac{\binom{k}{j}}{\binom{n}{j}}.
\]
All quantities in (31), (32), and this formula are exact rationals.
The accompanying standalone checker reconstructs these rows and every
other rational comparison in this note. It performs **111 strict
comparisons**, with no sampled state, root solver, or subdivision tree.

## 7. Complete coverage

The whole source-axis cover is:

| Separator | Signs | Continuous argument | Tail |
|---|---|---|---|
| F | \(+,-\) | Contact concavity and endpoint deformation, Section 3 | \(\phi\ge.32\) |
| F | \(+,+\) | Single polynomial row F on \([.6,1.09]\) | \(\phi\ge1.09\) |
| F | \(-,+\) | Impossible by (22) | \(\phi\ge1.85\) |
| F | \(-,-\) | Impossible by (22) | \(\phi\ge1.09\) |
| P | either source sign, negative target | Exclusion (27), then two endpoint bounds (28) | \(\phi\ge1.09\) |
| P | either source sign, positive target | Exclusion (29), then row P | \(\phi\ge1.85\) |

These rows include all relevant angle endpoints. The reflection/reversal
argument in Section 1 supplies every retained target-owned axis.
Consequently the whole middle/middle entry is hand proved at
\(\gamma_{MM}=.8912\), with no additional orientation-concentration
hypothesis.
