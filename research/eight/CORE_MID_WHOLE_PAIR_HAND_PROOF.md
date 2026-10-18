# Whole core/middle boundary-pair inequality

This is a fresh reconstruction of the complete core/middle hand proof
after the workspace outage. It includes the preserved nonaligned scalar
argument, extended to its complete required interval, and every
surrounding source-axis case. The strict lower cost is **.9005**.
The accompanying checker performs 213 exact rational comparisons.

## 1. States, labels, and retained separators

Every terminating decimal below denotes an exact rational. Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 \beta=.18,\quad \gamma=.9005,\quad a_c=\frac7{12},
\]
\[
 K=7.506931,\quad g=1.077372,\quad
 c_M=-2.143075,\quad p=1.489593,\quad q=1.580219.
\]
The positive core boundary consists of
\[
 C_{\rm side}:\ a=a_c,\quad 0\le b\le\tfrac12
\]
and
\[
 C_{\rm corner}:\ (a-\tfrac12)^2+(b-\tfrac12)^2=\tfrac1{144},
 \quad \tfrac12\le b\le a.
\]
Its diagonal endpoint is
\(c_C=\tfrac12+1/(12\sqrt2)\).
The middle outer arc is
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\qquad
                     \frac14\le b/a\le\frac37.
\]
The unsigned labels are
\[
 L_C=K(a_c-a)+gb,\qquad L_M=M(b)=c_M+pa(b)+qb,
 \quad a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12.                 \tag{1}
\]

Use source and target signs \(\sigma,\tau\in\{-1,1\}\).
Their centers in their own square frames are \((a,-\sigma b)\) and
\((A,-\tau B)\), and their frame-to-center angles are
\(\alpha_s=\sigma\arctan(b/a)\),
\(\alpha_t=\tau\arctan(B/A)\). Put
\[
 \phi=\delta+\alpha_t-\alpha_s,\quad
 s=\sin\phi,\quad c=\cos\phi,\quad
 h=\frac{|s|+|c|-1}{2},\quad W=1+h.
\]
The corrected pair cost is
\[
 {\cal C}=\phi-\beta h+\sigma L_s-\tau L_t.                  \tag{2}
\]
Equivalently it is
\(\delta-\beta h+\psi_t-\psi_s\) for
\(\psi=\alpha-\operatorname{sgn}(\alpha)L\).

We work after the hand core, radial-boundary, cap, and common-point
reductions. In particular
\[
                         .76<\delta<3\pi/4.                \tag{3}
\]
No frame-concentration hypothesis is used.
The remaining source-owned separators are
\[
\begin{array}{ll}
 {\mathsf F}:&M_f=\sigma b+A\sin\phi-\tau B\cos\phi-W\ge0,\\
 {\mathsf P}:&M_e=a-A\cos\phi-\tau B\sin\phi-W\ge0 .
\end{array}                                                 \tag{4}
\]
They are the positive transverse and inward primary source axes.
Reflection followed by reversal sends
\((s,t,\sigma,\tau)\) to \((t,s,-\tau,-\sigma)\), preserves \(\phi\)
and (2), and sends the retained target axes to these source axes.
We therefore prove both orders \(C,M\) and \(M,C\), both axes in (4),
and all source/target signs.

**Theorem.** Every such disjoint boundary pair satisfies
\[
                              {\cal C}>.9005.               \tag{5}
\]

### 1.1 Exact bounds

Let \((a_l,b_l)\), \((a_h,b_h)\) be the middle arc endpoints, with
\(b_l=a_l/4\), \(b_h=3a_h/7\). Squaring gives
\[
\begin{array}{c|cc}
 &\text{lower bound}&\text{upper bound}\\ \hline
a_l&1.298747247&1.298747249\\
a_h&1.199256060&1.199256062\\
M(b_l)&.3046&.30461\\
M(b_h)&.4555&.455511\\
c_C&.5589255&.5589256 .
\end{array}                                                 \tag{6}
\]
On the middle arc
\[
 r=\frac{b+\tfrac12}{a+\tfrac12},\quad
 a'=-r,\quad .458<r<.597,\quad
 0<M'=q-pr<.898,\quad M''<0.                                \tag{7}
\]
On the core, \(L_C\) increases with \(b\) and
\[
            0\le L_C<.786,\qquad
            \sqrt{a^2+b^2}<.8.                              \tag{8}
\]
For the radius bound, the squared norm increases along the core side
and corner and is at most \(2c_C^2<.8^2\).
The middle squared norm decreases along its arc, since
\[
 \frac{d}{db}(a^2+b^2)=\frac{b-a}{a+\tfrac12}<0.
\]
Thus its center norm is less than
\(\sqrt{a_l^2+b_l^2}<1.34\).

The elementary angle estimates
\(\arctan(3/7)<.405\) and \(\pi/4<.786\) imply
\[
                              \phi>-.432.                   \tag{9}
\]
For every angle, \(0\le\beta h<.0378\).
Every sign pair is therefore covered directly when \(\phi\ge2.18\):
\[
 {\cal C}>2.18-.455511-.786-.0378=.900689>.9005.              \tag{10}
\]
All later arguments may be restricted to \(-.432<\phi<2.18\).

We use the already proved hand Machin bounds
\[
                 3.14159<\pi<355/113.
\]
All trigonometric endpoint bounds below follow from alternating Taylor
polynomials. The checker reconstructs them as rational comparisons.

## 2. Core source on the primary axis

No source sign occurs in the primary separator. Replacing \(+L_C\)
by \(-L_C\) can only lower the cost, so the following arguments cover
both source signs.

For \(-.432<\phi\le1.5\), \(c>0\) and
\[
 M_e\le\frac1{12}-(A+\tfrac12)c+(B-\tfrac12)|s|
 <\frac1{12}-1.699\cos(1.5)+.014<0.                         \tag{11}
\]
Hence separation requires \(\phi>1.5\).

If \(\tau=-1\), the label bounds already give
\[
 {\cal C}>1.5-.786-.0378+.3046=.9808>.9005.                  \tag{12}
\]

If \(\tau=+1\), the first quadrant is impossible because
\[
 M_e<\frac1{12}-1.699c-.8246s<0.
\]
In the second quadrant write \(d=-c>0\). The entire interval up to
\(2.18\) is also impossible:
\[
 M_e<\frac1{12}+.799d-.8246s
 \le\frac1{12}+.799(.573)-.8246(.820)<0.                     \tag{13}
\]
Here \(d\le-\cos2.18<.573\) and \(s\ge\sin2.18>.820\).
The tail (10) finishes every core-source primary case.

## 3. Core source on the transverse axis

A negative core source admitting a transverse separator must be on its
straight side. Indeed,
\[
 b\le A\sin\phi-\tau B\cos\phi-W
 \le\sqrt{A^2+B^2}-1<.34<\tfrac12.
\]
For a positive source,
\(L_C-gb=K(a_c-a)\ge0\); for a negative source this residual is zero
because it is on the side. Subtracting \(gM_f\) from (2) consequently
gives the same lower bound for both source signs:
\[
 {\cal C}\ge\phi-\beta h+gW-\tau c_M
 +\min_M\{(-\tau p-gs)A+\tau(gc-q)B\}.                      \tag{14}
\]
Put
\[
 A_*=\frac{g+\beta}{2}=.628686,\qquad
 C_*=\frac{g-\beta}{2}=.448686.
\]

### 3.1 Negative middle target

The target functional in (14) has coefficients
\(p-gs>0\) and \(q-gc>0\). Its dependence on \(B\) is concave, so
its minimum occurs at one of the two arc endpoints \(j=l,h\).

For \(0\le\phi\le\pi/2\), each endpoint cost is
\[
 F_j(\phi)=\phi+A_*+M(b_j)
 +(C_*-gb_j)\cos\phi-(ga_j-C_*)\sin\phi.                    \tag{15}
\]
The endpoint bounds imply
\[
 0<ga_j-C_*<.952,\qquad |C_*-gb_j|<.106,
 \qquad .952^2+.106^2<1.
\]
Thus \(F_j'>0\).
Its value at zero satisfies
\[
                      F_j(0)=g+M(b_j)-gb_j>.979.            \tag{16}
\]
In the second quadrant the cosine coefficient becomes
\(-C_*-gb_j<0\), and the sine coefficient remains negative.
The derivative is then greater than one, so the lower bound continues.

For a negative angle, write \(\phi=-z\), \(0\le z<.432\). The endpoint
cost is instead
\[
 -z+A_*+M(b_j)+(C_*-gb_j)\cos z+(C_*+ga_j)\sin z.
\]
Its derivative with respect to \(z\) is positive, because
\[
 C_*+ga_j>1.74,\qquad
 -1-.106(.432)+1.74(1-.432^2/2)>0.
\]
Its minimum is again at zero. This proves all negative-target
core-source transverse cases.

### 3.2 Positive middle target: the full-circle interval

No separator is possible for \(\phi\le0\), since its projection is
less than \(b<.56\). For \(0\le\phi\le.7\),
\[
 M_f<.059+.799\sin\phi-.8246\cos\phi
 \le.059+.799(.7)-.8246(1-.7^2/2)<0.                        \tag{17}
\]
We may therefore assume \(\phi>.7\).

For any coefficients \(U,V\), the complete-circle support inequality is
\[
 UA+VB\ge-\frac{U+V}{2}-R\sqrt{U^2+V^2}.                    \tag{18}
\]
Applying it in (14) gives, in the first quadrant,
\[
\begin{split}
 F(\phi)&=\phi+K_F+(g-.09)\sin\phi-.09\cos\phi-RN(\phi),\\
 K_F&=.09-c_M+(p+q+g)/2,\\
 N^2&=p^2+q^2+g^2+2g(p\sin\phi-q\cos\phi).
\end{split}                                                 \tag{19}
\]
Section 7 gives one fixed degree-16 polynomial proving
\[
                            F>.9005
              \quad\hbox{on }[.7,1.53].                    \tag{20}
\]

### 3.3 Positive middle target: the high endpoint continuation

For \(\phi\ge1.53\), the target functional in (14) decreases along
the middle arc. Its derivative is
\[
             (p+g\sin\phi)r(B)+g\cos\phi-q.
\]
At \(1.53\) it is negative even on replacing \(r\) by .597.
The resulting upper bound continues to decrease because
\(\sin\phi-.597\cos\phi>0\) through \(2.18\). Hence its minimum is
at \((a_h,b_h)\).

Before the quarter turn, the endpoint cost is
\[
 J(\phi)=\phi+A_*-M(b_h)
 +(C_*+gb_h)\cos\phi-(ga_h-C_*)\sin\phi.                    \tag{21}
\]
It decreases on \([1.53,\pi/2]\), since
\[
                       (C_*+gb_h)\sin(1.53)>1.
\]
At the quarter turn its value is
\[
 J(\pi/2)=\frac\pi2-M(b_h)+g(1-a_h)
 >\frac{3.14159}{2}-.455511+g(1-1.199256062)
 >.9006.                                                    \tag{22}
\]
After the quarter turn the cosine coefficient becomes
\(-C_*+gb_h<.11\). Since \(ga_h-C_*>0\) and \(c\le0\), the
derivative is greater than \(1-.11\).
Thus (22) continues through \(2.18\), completing the entire
core-source transverse entry.

## 4. Middle source on the transverse axis

A negative middle source cannot separate on this axis: its projection
is at most the core-center norm, which is less than .8.
We may assume \(\sigma=+1\).

### 4.1 Negative core target

For \(\phi\ge0\), use multiplier \(g\) in (4).
The source function \(M(b)-gb\) decreases, by (7), and its minimum
is at \(b_h\). The remaining core functional obeys
\[
 L_C-gA\sin\phi-gB\cos\phi
 =-ga_c\sin\phi+(K+g\sin\phi)(a_c-A)+gB(1-\cos\phi)
 \ge-ga_c\sin\phi .
\]
Thus
\[
 {\cal C}\ge
 \phi-\beta h+gW+M(b_h)-gb_h-ga_c\sin\phi.                   \tag{23}
\]
In the first quadrant this function increases because
\[
             C_*^2+(ga_c-C_*)^2<1.
\]
In the second quadrant its derivative is greater than one.
Its value at zero is the bound \(>.979\) from (16).

For \(\phi=-z<0\), put \(\lambda=g/\cos z\).
Since \(\lambda\ge g>.898\), the source function \(M-\lambda b\)
still decreases. The core \(B\)-coefficient cancels, and
\(K-g\tan z>0\), so the core is minimized at \(A=a_c\).
The lower cost becomes
\[
 F_-(z)=-z-\frac\beta2(\sin z+\cos z-1)+M(b_h)+\frac g2
 +g\,\frac{(1/2-b_h)+(13/12)\sin z}{\cos z}.                 \tag{24}
\]
Multiplication of its derivative by \(\cos^2z\) gives the lower bound
\[
 \frac{13g}{12}-1.09+1.09\sin^2z-.014g\sin z
 \ge\frac{13g}{12}-1.09-\frac{(.014g)^2}{4.36}>0.
\]
Thus (24) is minimized at zero, again giving \(>.979\).
This proves the whole negative-core-target case.

### 4.2 Positive core target

For \(\phi\le0\), the projection is less than \(b<.514\).
For \(0\le\phi\le1.2\),
\[
 M_f<.014+\frac{\sin\phi}{12}-\frac{\cos\phi}{2}
 \le.014+\frac{1.2}{12}-\frac{1-1.2^2/2}{2}<0.
\]
We therefore have \(\phi>1.2\).

Use multiplier one. The source function \(M-b\) decreases.
The target function \(-L_C-A\sin\phi+B\cos\phi\) also decreases
along the entire core boundary, since its derivative is
\[
 (K-\sin\phi)A'+\cos\phi-g<0.
\]
The minimum is at the diagonal \((c_C,c_C)\). It remains to bound
\[
 H(\phi)=\phi-\beta h+W+M(b_h)-b_h-L_C(c_C,c_C)
                         +c_C(\cos\phi-\sin\phi).           \tag{25}
\]
In the first quadrant its derivative is positive because
\[
             (.41+c_C)^2+(c_C-.41)^2<1.
\]
In the second quadrant its derivative is at least \(1-(c_C-.41)>0\).
Substituting (6) and Taylor bounds at \(1.2\) gives
\[
                              H(1.2)>1.15.
\]
This closes every middle-source transverse case.

## 5. Middle source on the primary axis

Again the separator is independent of the source sign, so use the
lower source contribution \(-M\). The core coordinates satisfy
\(A+\tfrac12>1.058\), \(B-\tfrac12<.059\).
For \(-.432<\phi\le.6\),
\[
 M_e<.799-1.058\cos\phi+.059|\sin\phi|
 \le.799-1.058(1-.6^2/2)+.059(.6)<0.                        \tag{26}
\]
Thus only \(.6<\phi<2.18\) remains.

First treat a negative core target on its whole boundary, or a positive
core target on its straight side. The positive-target corner is handled
in Section 5.4.

### 5.1 The \(g/\sin\phi\) cancellation

Put \(\lambda=g/\sin\phi\).
For a negative core target,
\[
 L_C+\lambda A\cos\phi-\lambda B\sin\phi
 =\lambda a_c\cos\phi+
       (K-\lambda\cos\phi)(a_c-A)
 \ge\lambda a_c\cos\phi.                                   \tag{27}
\]
The coefficient is positive on the intervals used below:
\(\sin\phi>.564\) and \(K>g/.564\).
For a positive core target on its side, its functional is exactly
\(\lambda a_c\cos\phi\), because the \(B\)-coefficient cancels.

On \([.6,1.2]\), enlarge the source middle arc to its full outer circle.
The support coefficients are \((-p-\lambda,-q)\). After collecting
terms, the pair cost is at least
\[
\begin{split}
 F(\phi)={}&\phi-\frac\beta2(s+c-1)-c_M+\frac{p+q+g}{2}
 +\frac g{s}+\frac{13g}{12}\frac c{s}
 -R\sqrt{(p+g/s)^2+q^2}.
\end{split}                                                 \tag{28}
\]
Section 6 proves
\[
                 F>.9005985>.9005
                   \quad\hbox{on }[.6,1.2].                \tag{29}
\]

### 5.2 The high source endpoint from \(1.2\) onward

On \([1.2,1.94]\), \(\sin\phi>.932\).
This follows from the two endpoint bounds and concavity of sine.
The source function \(-M-\lambda a\) therefore decreases:
\[
 \frac{d}{db}[-M-\lambda a]=(p+\lambda)r-q
 <(p+g/.932)(.597)-q<0.
\]
Its minimum is at \((a_h,b_h)\). Equation (27), or its exact side
counterpart, yields
\[
 G(\phi)=\phi-\beta h-M(b_h)
            +\frac g{\sin\phi}(W-a_h+a_c\cos\phi).           \tag{30}
\]

In the first quadrant put \(d_h=a_h-\tfrac12\), \(k=13/12\).
Then
\[
 G=\phi-\frac\beta2(s+c-1)-M(b_h)+\frac g2
                 +g\,\frac{kc-d_h}{s},
\]
\[
 G'=1+\frac\beta2(s-c)+g\,\frac{d_hc-k}{s^2},                \tag{31}
\]
and
\[
 G'''=\frac\beta2(c-s)
       +\frac g{s^4}\{d_hc(5+c^2)-2k(1+2c^2)\}<0.          \tag{32}
\]
For (32), use \(s>.932\), \(0\le c<.363\), \(d_h<.7\), and
\[
                  .7(.363)(5+.363^2)<13/6.
\]
Thus \(G'\) is concave on \([1.2,\pi/2]\).
The rational endpoint checks give
\[
 G'(1.2)>0,\qquad G(1.2)>.902,\qquad
 G(\pi/2)=J(\pi/2)>.9006.                                   \tag{33}
\]
A concave derivative that is positive at the left endpoint can cross
zero at most once from positive to negative. Consequently \(G\) has
no interior minimum on this interval. Its minimum is at one of the
two endpoints in (33).

In the second quadrant,
\[
 G'=1-\frac\beta2(s+c)
            +g\,\frac{d_hc-1/12}{s^2}.
\]
For \(\pi/2\le\phi\le1.94\), use \(s>.932\),
\(-c<.362\), and \(s+c\le1\):
\[
                  G'>.91-g\frac{.7(.362)+1/12}{.932^2}>0.   \tag{34}
\]
Thus the quarter-turn bound continues through \(1.94\).

### 5.3 The remaining side/negative-target tail

For a positive core target on its side, \(L_C\le g/2\).
For a negative core target, its signed contribution is \(+L_C\ge0\);
the same deliberately weaker bound \(-g/2\) is also valid.
Therefore, for both cases and all \(\phi\ge1.94\),
\[
 {\cal C}>1.94-.455511-g/2-.0378=.908003>.9005.               \tag{35}
\]
Equations (29), (33)--(35) complete these two target cases.

### 5.4 Positive core target on its corner

Here \(B\ge1/2\). The first quadrant is impossible because separation
would require
\[
                a\ge W+A\cos\phi+B\sin\phi
                    \ge\tfrac12+\sin\phi+\cos\phi
                    \ge\tfrac32>a_l.
\]
In the second quadrant, with \(d=-\cos\phi\), it requires
\[
                           a\ge\tfrac12+s-\frac d{12}.      \tag{36}
\]
The right side decreases with \(\phi\). At \(2.13\) it exceeds
\[
                  .5+.847-.532/12>a_l.
\]
Thus no such separator exists before \(2.13\).

On \([2.13,2.18]\), (36) gives
\[
                  a>.5+.820-.573/12=1.27225.
\]
The exact squared comparison
\[
                 (1.27225+.5)^2+(.381+.5)^2>Q
\]
forces \(b<.381\). Hence
\[
 M(b)<c_M+p(1.298747249)+q(.381)<.394,
\]
and
\[
                  {\cal C}>2.13-.0378-.786-.394
                              =.9122>.9005.                \tag{37}
\]
Together with (10), this finishes the last primary case.

## 6. The scalar curvature argument on the whole interval \([.6,1.2]\)

This section verifies (29) without a numerical minimization premise.
Write
\[
 X=p+g/s,\qquad N=\sqrt{X^2+q^2},\qquad Z=RX/N.
\]
Direct differentiation of (28) gives
\[
 F'=1+\frac\beta2(s-c)
             +\frac g{s^2}\left[c(Z-1)-\frac{13}{12}\right], \tag{38}
\]
\[
 F''=\frac\beta2(s+c)
 +\frac g{s^3}\left[(1+c^2)(1-Z)+\frac{13}{6}c\right]
 -\frac{Rq^2g^2c^2}{s^4N^3}.                               \tag{39}
\]
For example, these follow from
\(\lambda'=-gc/s^2\), \(\lambda''=g(1+c^2)/s^3\), and
\((X/N)'=q^2\lambda'/N^3\).

Both \(N\) and \(Z\) decrease on this interval, since \(s\) increases
and \(X\) decreases. The following endpoint table asserts
\(s^-<\sin x<s^+\), \(c^-<\cos x<c^+\), \(Z(x)<z^+\),
and \(N(x)>n^-\).
**Every integer after the first column is divided by \(10^5\).**

| \(x\) | \(s^-\) | \(s^+\) | \(c^-\) | \(c^+\) | \(z^+\) | \(n^-\) |
|---|---:|---:|---:|---:|---:|---:|
| .6 | 56464 | 56465 | 82533 | 82534 | 179424 | 374711 |
| .7 | 64421 | 64422 | 76484 | 76485 | 177007 | 353482 |
| .8 | 71735 | 71736 | 69670 | 69671 | 174969 | 338316 |
| .9 | 78332 | 78333 | 62160 | 62161 | 173272 | 327185 |
| 1 | 84147 | 84148 | 54030 | 54031 | 171878 | 318896 |
| 1.04 | 86240 | 86241 | 50622 | 50623 | 171398 | 316201 |
| 1.08 | 88195 | 88196 | 47132 | 47133 | 170961 | 313805 |
| 1.12 | 90010 | 90011 | 43568 | 43569 | 170563 | 311680 |
| 1.16 | 91680 | 91681 | 39933 | 39934 | 170204 | 309802 |
| 1.2 | 93203 | 93204 | 36235 | 36236 | 169882 | 308152 |

For the sine bounds use degrees 11/13 and for cosine degrees 10/12.
For the last two columns set \(X^+=p+g/s^-\), \(X^-=p+g/s^+\).
They follow from
\[
 (z^+)^2[(X^+)^2+q^2]>1.978788^2(X^+)^2,\qquad
                       (X^-)^2+q^2>(n^-)^2.               \tag{40}
\]
The function \(X/\sqrt{X^2+q^2}\) increases for \(X>0\), so (40)
has the required direction.

For consecutive rows \(j,j+1\), put
\[
 B_j=(1+(c_j^+)^2)(1-z_j^+)+\frac{13}{6}c_{j+1}^-.
\]
If \(B_j\ge0\), let \(d_j=(s_{j+1}^+)^3\); if \(B_j<0\), let
\(d_j=(s_j^-)^3\).
The denominator choice is essential for the last interval.
Also put
\[
 m_j=\min(s_j^-+c_j^-,\,s_{j+1}^-+c_{j+1}^-).
\]
Since \(s+c\) is positive and concave, its minimum on the interval
is at an endpoint. Thus \(s+c>m_j\), including the first intervals
that lie below or cross \(\pi/4\).

Formula (39) now has the strict rational lower bound
\[
 D_j=.09m_j+\frac{gB_j}{d_j}
 -\frac{1.978788\,q^2g^2(c_j^+)^2}
 {(s_j^-)^4(n_{j+1}^-)^3}.                                 \tag{41}
\]
Indeed, \(1-z_j^+<0\) must be multiplied by the upper bound
\(1+(c_j^+)^2\); the remaining denominator directions follow from
the sign of \(B_j\) and the explicit negative last term in (39).

Here are strict rational lower bounds for (41), again with common
denominator \(10^5\).

| Interval | lower numerator for \(B_j\) | lower numerator for \(D_j\) |
|---|---:|---:|
| \([.6,.7]\) | 32188 | 55193 |
| \([.7,.8]\) | 28895 | 46704 |
| \([.8,.9]\) | 23320 | 34899 |
| \([.9,1]\) | 15480 | 22276 |
| \([1,1.04]\) | 16819 | 30005 |
| \([1.04,1.08]\) | 12424 | 23091 |
| \([1.08,1.12]\) | 7672 | 16401 |
| \([1.12,1.16]\) | 2563 | 9851 |
| \([1.16,1.2]\) | −2891 | 3183 |

The last \(B_j\) is negative; the others are positive.
Every \(D_j>.03\), giving the whole-interval bound
\[
                              F''>.03.                      \tag{42}
\]

### 6.1 One rational test point

At \(x_0=1.08\), use these strict rational brackets, with denominator
\(10^9\):

| Quantity | lower numerator | upper numerator |
|---|---:|---:|
| \(\sin x_0\) | 881957806 | 881957807 |
| \(\cos x_0\) | 471328364 | 471328365 |
| \(R\) | 1978787507 | 1978787508 |
| \(N(x_0)\) | 3138070988 | 3138070991 |

Sine degrees 19/21 and cosine degrees 18/20 prove their rows;
the root rows follow by squaring. With superscripts \(-,+\) denoting
the lower and upper bounds, substitution in (28) gives
\[
\begin{split}
 F(x_0)\ &>
 x_0-.09(s^++c^+-1)-c_M+(p+q+g)/2\\
 &\quad+g/s^++(13g/12)c^-/s^+-R^+N^+
 >.9006.                                                    \tag{43}
\end{split}
\]
For (38), bound \(Z\) between
\[
        R^-(p+g/s^+)/N^+,\qquad R^+(p+g/s^-)/N^-.
\]
Then \(Z-1>0\), while \(c(Z-1)-13/12<0\).
Using these signs in the last term of (38) gives
\[
                           |F'(x_0)|<.0003.                 \tag{44}
\]
Integrating (42) and completing the square proves, for every
\(\phi\in[.6,1.2]\),
\[
 F(\phi)\ge F(x_0)-\frac{F'(x_0)^2}{2(.03)}
 >.9006-\frac{.0003^2}{.06}
 =.9005985>.9005.
\]
This proves the whole scalar assertion (29).

## 7. The one fixed polynomial row

Let \(S_j,C_j\) be sine and cosine Taylor polynomials truncated at
degree \(j\). On \([.7,1.53]\),
\[
       S_7\le\sin x\le S_9,\qquad C_{10}\le\cos x\le C_8.
\]
With the exact constant \(K_F\) in (19), put
\[
\begin{split}
 T(x)&=x+K_F-\gamma+(g-.09)S_7(x)-.09C_8(x),\\
 V(x)&=p^2+q^2+g^2+2g\{pS_9(x)-qC_{10}(x)\},\\
 P(x)&=T(x)^2-QV(x).
\end{split}                                                 \tag{45}
\]
Here \(T\) bounds the nonradical part of \(F-\gamma\) below,
and \(V\) bounds \(N^2\) above.

The following are strict lower bounds for the complete degree-16
Bernstein coefficient list of \(P\) on \([.7,1.53]\).
Every integer is divided by \(10^6\):
\[
\begin{gathered}
930757,\ 865698,\ 798263,\ 729205,\ 659251,\ 589108,\ 519469,\\
451021,\ 384457,\ 320478,\ 259803,\ 203178,\ 151376,\ 105205,\\
65512,\ 33176,\ 9117 .
\end{gathered}
\]
Every degree-8 Bernstein coefficient of \(T\) is greater than \(4\).
Hence \(T>0\), \(P>0\), and
\[
                            T>R\sqrt V\ge RN.
\]
This proves \(F>\gamma\) on the entire interval.

These coefficients have a direct rational definition. If
\(P(x)=\sum p_i x^i\), first expand
\(P(l+(u-l)y)=\sum d_j y^j\). Its degree-\(n\) Bernstein coefficient is
\[
                       B_k=\sum_{j=0}^k
                       d_j\frac{\binom{k}{j}}{\binom{n}{j}}.
\]
Thus the row can be verified from (45) using only rational arithmetic.
It is one fixed interval, with no selected-state or subdivision premise.

## 8. Full continuous cover

| Source, target | Source separator | Negative target sign | Positive target sign |
|---|---|---|---|
| C, M | F | Section 3.1, both source signs | Sections 3.2–3.3, both source signs |
| C, M | P | Section 2, both source signs | Section 2, both source signs |
| M, C | F | Section 4.1; negative source impossible | Section 4.2; negative source impossible |
| M, C | P | Sections 5.1–5.3, both source signs | Side: 5.1–5.3; corner: 5.4; both source signs |

All discarded angle ranges were explicitly excluded or covered by
the universal tail (10). Every side/corner junction and interval
endpoint belongs to at least one closed proof case.
The reflected reversal in Section 1 covers the retained target axes.
This proves the complete C/M entry at \(\gamma_{CM}=.9005\).

The optional standalone arithmetic replay,
\`verify_core_mid_whole_pair_hand.js\`, verifies **213 strict rational
comparisons**, including all 17 polynomial coefficients, the positive
\(T\) bounds, the nine curvature intervals, and the displayed root,
trigonometric, derivative, and endpoint estimates.
The continuous proof is the argument above.
