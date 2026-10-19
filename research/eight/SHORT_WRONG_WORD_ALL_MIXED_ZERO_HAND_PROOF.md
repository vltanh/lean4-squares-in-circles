# All mixed zero-quarter pairs for the wrong word 0010111

## Statement and proof status

This is a complete hand proof of the mixed core/outer part of the three zero-quarter edges of the cyclic word \(0010111\). Under the exterior geometry and sign premises below, every admissible mixed pair has corrected angular cost
\[
 C>\frac{449}{500}=.898>\frac{17953}{20000}.
 \tag{1}
\]
The proof covers all 56 signed, radial-kind, and separating-axis branches. It uses linear support of a circle, monotonicity, concavity, and a fixed list of 243 strict rational comparisons. It does not use an adaptive interval tree or a numerical minimum.

The companion arithmetic source is verify_short_all_mixed_zero_hand.js; its exact output is short_all_mixed_zero_hand_arithmetic.json. The earlier note SHORT_WRONG_WORD_MIXED_ZERO_FAMILIES_HAND_PROOF.md supplies the ten regimes recalled in Section 3. The new checker includes all 68 comparisons of that note as well as the comparisons below. This statement is one whole component of the wrong-word argument; mixed quarter-one and outer/outer pairs are separate components.

All terminating decimals in this note are exact rationals. Decimal lower bounds in tables are rounded down.

## 1. Geometry and complete branch inventory

Write
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-\frac12,\quad
 d_C=\frac12+\frac{\sqrt2}{24},\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad a_c=\frac7{12}.
\]
An outer state, denoted \(O\), has
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\qquad a\ge b\ge0.
\]
Thus \(0\le b\le d\), \(a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2\), and
\[
 a'=-r,\qquad r=\frac{b+1/2}{a+1/2}\in[r_0,1],
 \qquad r_0=\frac{1/2}{a_0+1/2}.
 \tag{2}
\]
The derivative \(r\) is increasing. A core state \(C\) lies either on the side
\[
 a=a_c,\quad 0\le b\le\tfrac12,
\]
or on the corner arc
\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},
 \qquad a\ge b\ge\tfrac12.
\]
In particular \(d_C\le a\le a_c\), \(0\le b\le d_C\), and every core center has norm \(<4/5\).

Let the source and target centers in their respective frames be
\((a,-\sigma b)\) and \((A,-\tau B)\), where \(\sigma,\tau\in\{-1,1\}\). Put
\[
 \phi=\theta_{\rm target}-\theta_{\rm source},\quad
 W=\frac{1+|\sin\phi|+|\cos\phi|}{2}.
\]
The exterior geometry used here is
\[
 |\phi|\le .7,\qquad \delta>.76
 \tag{3}
\]
on a zero-quarter edge. The already proved cap and forward-gap eliminations leave these four signed separating axes:
\[
\begin{array}{c|l}
1&\sigma b+A\sin\phi-\tau B\cos\phi\ge W\\
2&-a\cos\phi+\sigma b\sin\phi+A\ge W\\
3&a\sin\phi+\sigma b\cos\phi-\tau B\ge W\\
4&a-A\cos\phi-\tau B\sin\phi\ge W.
\end{array}
 \tag{4}
\]
They are, respectively, source \(+f\), target \(+e\), target \(+f\), and source \(-e\). Our angle range also implies \(\delta<.7+\pi/2<3\pi/4\), as required by the forward-gap elimination.

A signed role label is
\[
 \ell_i(a,\sigma b)=c_i+p_i a+\sigma q_i b,
 \qquad C=\phi+\ell_i-\ell_{i+1}.
 \tag{5}
\]
The exact coefficients below are those in short_hand_labels.json, reconstructed without a change from the rational candidate 0010111_affine_hand_candidate_v1.json.

The zero edges are \(0,1,3\). The two consecutive zero edges imply that role 0 is positive and role 2 is negative: their center gaps sum to \(>1.52\), their total lifted frame change is at most .7, and therefore
\(\alpha_0-\alpha_2>.82>\pi/4\). Also the sign pair \((-,+)\) is impossible on any zero edge, since then \(\delta\le\phi\le.7\). The remaining edge/sign classes are
\[
\begin{array}{c|c}
0&++,+-\\
1&--,+-\\
3&++,+-,--.
\end{array}
 \tag{6}
\]
There are seven such classes, two mixed radial orders, and four axes: 56 branches.

Reflection followed by reversal keeps \(\phi\) and \(C\) unchanged, interchanges the radial kinds, reverses both signs, and sends each coefficient triple to
\[
 (c,p,q)\longmapsto(-c,-p,q).
 \tag{7}
\]
It interchanges the two secondary axes and the two primary axes. The proof inventory after this exact identification is:
\[
\begin{array}{l|r}
C-\to O-\text{ source }+f\text{ and reflected cases, Section 3}&4\\
O-\to C-\text{ source }+f\text{ and reflected cases, impossible}&4\\
C+\to O+\text{ source }+f\text{ and reflected cases, Section 7}&4\\
O+\to C+\text{ source }+f\text{ and reflected cases, Section 6}&4\\
(+,-)\text{ mixed secondary cases, Sections 3--5}&12\\ \hline
\text{core source primary cases and reflected cases, impossible}&14\\
\text{outer source, positive core target primary cases, impossible}&4\\
\text{outer source, negative core target primary cases, Section 8}&10.
\end{array}
 \tag{8}
\]
The impossible negative/negative secondary cases satisfy
\(-b+A\sin\phi+B\cos\phi\le\sqrt{A^2+B^2}<4/5<W\).

We use the coarse strict bounds
\[
\begin{gathered}
 .8992140<d<.8992141,\quad .5589<d_C<.559,\quad
 1.414<a_0<1.415,\quad R<1.978788<2,\\
 \sin(.7)<.645,\quad \cos(.7)>.764.
 \tag{9}
\end{gathered}
\]

## 2. Elementary support rules

For real \(x,y\), enlarging the outer arc to its full circle gives
\[
 xa+yb\ge-\frac{x+y}{2}-R\sqrt{x^2+y^2}.
 \tag{10}
\]
If \(y\ge0\), its minimum on the actual arc is at the axial or diagonal endpoint: when \(x\ge0\) the function is concave in \(b\); when \(x<0\) it is increasing. If \(x<0\), its derivative is increasing in \(b\), so a nonnegative derivative at \(b=0\) identifies the axial minimum.

The scalar norms below have the form
\[
 N^2=p^2+q^2+\lambda^2+2\lambda(p\sin\phi-q\cos\phi).
\]
With \(L=\sqrt{p^2+q^2}\),
\[
 N''+\frac N4=\frac{(L^2-\lambda^2)^2}{4N^3}\ge0.
 \tag{11}
\]
Consequently \(\phi+C_0+\lambda(\sin\phi+\cos\phi)-RN\) is strictly concave on \([0,.7]\) whenever \(\lambda>L\): use \(N\le\lambda+L\), \(R<2\), and \(\sin\phi+\cos\phi\ge1\).

## 3. Previously proved ten regimes

The earlier ten-family note proves these normalized \(C-\to O-\) source-secondary cases on the whole \([-.7,.7]\):
\[
\begin{array}{c|rrrr}
 &c_*&p&q&g\\ \hline
1\text{ direct}&-.11418& .09133&.88074&.62095\\
3\text{ direct}& .07943& .19335&.76744&.62750\\
0\text{ reversed}&-.25648&0&.94766&.62095\\
3\text{ reversed}&-.94615&-.51554&1.19909&.58829.
\end{array}
 \tag{12}
\]
Here \(C=\phi+c_*-gb-pA+qB\), and
\(-b+A\sin\phi+B\cos\phi\ge W\). Feasibility forces \(\phi>.3024\). A positive SAT multiplier gives the concave envelope in (11). Six endpoint rows, and one axial/diagonal endpoint comparison, prove every cost \(>.898\).

The same note proves the negative-angle halves of the following six normalized \(O+\to C-\) source-secondary rows:
\[
\begin{array}{c|l|rrrr}
j&\text{original case}&c_*&p&q&g\\ \hline
0&0:O+\to C-& .14041&0&.94766&.62095\\
1&0:C+\to O-\text{ reversed}&-.21286& .13422&1.03828&1.08816\\
2&1:O+\to C-&-.05550&0&.99940&1.13855\\
3&1:C+\to O-\text{ reversed}& .28271&-.09133&.88074&.62095\\
4&3:O+\to C-&-.72700& .51554&1.19909&1.04073\\
5&3:C+\to O-\text{ reversed}& .27632&-.19335&.76744&1.04729.
\end{array}
 \tag{13}
\]
The cost and separation are
\[
 C=\phi+c_*+pa+qb+gB,\qquad
 b+A\sin\phi+B\cos\phi\ge W.
 \tag{14}
\]
Writing \(\phi=-x\), feasibility gives \(0\le x<.44152\). Four rows have an increasing explicit \(\sec x,\tan x\) envelope; row 0 has an endpoint minimum; row 3 has a decreasing exact diagonal-contact envelope. The least displayed lower bound among all six is \(>.898108332\). These analytic details and 68 fixed comparisons are in the earlier note and included in the present checker.

## 4. Complementary core-source (+,-) cases

Reversal/reflection of (13), including the other secondary owner, gives six \(C+\to O-\) source-secondary rows
\[
 C=\phi+c_*+gb-pA+qB,\qquad
 b+A\sin\phi+B\cos\phi\ge W,
 \tag{15}
\]
with the same \(c_*,q,g\) as (13) and \(p\) replaced by its negative. In this section only, \(p\) means that replaced coefficient.

### 4.1. The negative-angle half

Write \(\phi=-x\). The maximum possible SAT margin is at most
\[
 d_C-\tfrac12+(d-\tfrac12)\cos x-(d+\tfrac12)\sin x.
\]
This is strictly decreasing and negative at .32; hence \(0\le x<.32\).

For fixed \(x\), the smallest feasible core coordinate is
\[
 b=W+A(B)\sin x-B\cos x.
 \tag{16}
\]
It is positive, strictly decreasing in \(B\), and the feasible target interval is \([B_{\min},d]\), where (16) equals \(d_C\) at \(B_{\min}\). A minimum uses (16) with equality, since \(g>0\). Its derivative with respect to \(B\) is
\[
 q-g\cos x+r(p-g\sin x).
 \tag{17}
\]
When \(p\le0\), the objective is concave in \(B\), so an endpoint suffices. For row 3, \(p=.09133\), and (17) is bounded below by
\(q-g(\cos x+\sin x)>q-1.32g>0\).
For row 5, \(p=.19335\): if \(p-g\sin x\ge0\), (17) is at most
\(q+p-g(\cos x+\sin x)\le q+p-g<0\); otherwise it is at most
\(q-g\cos(.32)<0\). Thus endpoints suffice in every row.

At \(b=d_C\), put
\[
 Z=\cos x+\tfrac12-d_C,\quad Y=\sqrt{Q-Z^2},\quad
 U=\cos x\,Y-\sin x\,Z,\quad V=\sin x\,Y+\cos x\,Z.
\]
Then \(A=U-1/2,\ B=V-1/2\), and
\[
 H(x)=-x+c_*+gd_C-p(U-\tfrac12)+q(V-\tfrac12).
 \tag{18}
\]
We may continue this formula to all of \([0,.32]\), slightly beyond its feasible subinterval.

Let \(f=1-\sin x/Y\). Direct differentiation gives
\[
 U'=-Vf,\quad V'=Uf,\quad H'=-1+f(pV+qU).
\]
On this interval,
\[
 Y>1.74,\quad1.39<U<1.75,\quad .94<V<1.41,\quad
 \cos x>.949,\quad\sin x<.315,\quad Z<.942.
\]
The endpoint values and the rotation identities prove these bounds. Thus \(f>0\), and
\[
 \cos x\,Y^2-Z\sin^2x
 >.949(1.74)^2-.942(.315)^2>0
\]
proves \(f'<0\). Every row satisfies
\[
 pV+qU>.767(1.39)-.516(1.41)>0,
\]
and
\[
 (pV+qU)'=(pU-qV)f
 <\{.194(1.75)-.767(.94)\}f<0.
\]
Therefore \(H''<0\), so only \(H(0),H(.32)\) are needed.

At \(A=B=d\), the other endpoint is
\[
 G(x)=-x+c_*+(q-p)d+
 g\{\tfrac12+(\tfrac12+d)\sin x+(\tfrac12-d)\cos x\}.
 \tag{19}
\]
Its derivative is
\[
 G'=-1+g\{(\tfrac12+d)\cos x+(d-\tfrac12)\sin x\}.
\]
For the four \(g>1\) rows the braces exceed 1.399 and \(g>1.04\), so \(G'>0\). For the other two, \(g=.62095\), and the braces are at most \(\sqrt{1.4^2+.4^2}\), so \(G'<0\).

The endpoint lower bounds are:
\[
\begin{array}{c|rrr}
j&H(0)&H(.32)&\min G\\ \hline
0&.905463428&1.021327336&1.021034991\\
1&1.019823741&1.131293564&.951139714\\
2&1.021674492&1.161335541&.957924362\\
3&.904935107&1.021370796&1.021034365\\
4&1.023200498&1.077737423&.919710358\\
5&.960289172&1.059634310&.898101904.
\end{array}
 \tag{20}
\]

### 4.2. The positive-angle half

Subtract \(\lambda\ge g\) times the SAT margin in (15). The core contribution is at least \((g-\lambda)d_C\), and the outer coefficients are
\(-p-\lambda\sin\phi,\ q-\lambda\cos\phi\).
Three lower envelopes are
\[
\begin{aligned}
 F_N={}&\phi+c_*+(g-\lambda)d_C+\frac{\lambda+p-q}{2}
       +\lambda(\sin\phi+\cos\phi)-RN,\\
 F_D={}&\phi+c_*+(g-\lambda)d_C+(q-p)d+\frac\lambda2
       -\lambda(d-\tfrac12)(\sin\phi+\cos\phi),\\
 F_A={}&\phi+c_*+(g-\lambda)d_C-pa_0+\frac\lambda2
       +\frac\lambda2\cos\phi-\lambda(a_0-\tfrac12)\sin\phi.
\end{aligned}
 \tag{21}
\]
The norm is that in (11). The diagonal envelope is increasing because
\(F_D'>1-.4\lambda>0\).

These decisions cover the whole positive half:
\[
\begin{array}{c|c|c|l}
j&\text{interval}&\lambda&\text{support}\\ \hline
0&[0,.7]&q&\text{axial}\\
1,2&[0,.1]&g&\text{diagonal}\\
1,2&[.1,.4]&g&\text{full circle}\\
1,2&[.4,.7]&g&\text{axial}\\
3&[0,.1]&.93&\text{full circle}\\
3&[.1,.7]&.93&\text{axial}\\
4&[0,.7]&g&\text{both arc endpoints}\\
5&[0,.05]&g&\text{diagonal}\\
5&[.05,.7]&g&\text{full circle}.
\end{array}
 \tag{22}
\]
A negative secondary coefficient and
\(\lambda(\cos\phi-\sin\phi)>p+q\) force the diagonal minimum. The latter expression decreases with \(\phi\), so one right-endpoint comparison proves each diagonal row. When the primary coefficient is negative, the derivative at \(B=0\) is
\[
 r_0(p+\lambda\sin\phi)+q-\lambda\cos\phi.
 \tag{23}
\]
It increases with \(\phi\), so positivity at .4, or .1 for row 3, identifies every later axial minimum. Row 0's coefficients force the axial minimum directly. Row 4 has positive secondary coefficient, so the endpoint rule applies.

Each full-circle row has \(\lambda>\sqrt{p^2+q^2}\), so (11) gives concavity. Its endpoint lower bounds are
\[
\begin{array}{c|c|rr}
j&\text{interval}&\text{left}&\text{right}\\ \hline
1&[.1,.4]&.934852130&.993647681\\
2&[.1,.4]&1.013710594&1.023380433\\
3&[0,.1]&.904935007&.923484603\\
5&[.05,.7]&.926289896&.969677825.
\end{array}
 \tag{24}
\]
For rows 1 and 2, \(F_A'\) is convex and negative at both .4 and .7; the right endpoint suffices and is \(>.898\). For rows 0 and 3,
\(\lambda^2\{.25+.915^2\}<1\) implies \(F_A'>0\); their left endpoints are \(>.898\). For row 4, \(F_A(0)>1.04\) and the same amplitude bound with \(1.09^2\) gives \(F_A'>-.09\), so \(F_A>1.04-.7(.09)>.898\). Its diagonal value at zero is \(>.9197\). The zero-angle diagonal values for rows 1, 2, 5 are respectively \(>.951139714,\ .957924362,\ .898101904\).

## 5. Outer-source (+,-) positive angles

Use the coefficients of (13), without negating \(p\), and (14).

For rows 0 and 3 choose \(\lambda=q\) and \(\lambda=.93\), respectively. The source-circle support is the constant
\[
 S=-\frac{p+q-\lambda}{2}-R\sqrt{p^2+(q-\lambda)^2}.
\]
The core coefficients \(-\lambda\sin\phi\) and \(g-\lambda\cos\phi\) are nonpositive. Using \(A\le7/12,\ B\le d_C\),
\[
 C\ge \phi+c_*+S+\frac\lambda2+gd_C
       -\frac{\lambda}{12}\sin\phi
       +\lambda(\tfrac12-d_C)\cos\phi.
 \tag{25}
\]
Its derivative exceeds \(1-\lambda/12>0\); its values at zero exceed .905463428 and .904935007.

For rows 1, 2, 4, 5 take \(\lambda=g/\cos\phi\). The source functional \(pa+(q-\lambda)b\) is minimized at the diagonal. For rows 1, 2, 5 use its derivative. For row 4, if \(q-\lambda\ge0\), use the endpoint rule and the diagonal/axial comparison at the smallest multiplier \(g\); if \(q-\lambda<0\), the derivative is negative. The remaining core term is bounded using \(A\le7/12\):
\[
 C\ge F(\phi)=\phi+c_*+(p+q)d+\frac g2
       +g(\tfrac12-d)\sec\phi-\frac g{12}\tan\phi.
 \tag{26}
\]
It is increasing because
\[
 F'\ge1-\frac{1.14\{.4(.645)+1/12\}}{.58}>0.
\]
At zero its four values are the same \(>.898\) diagonal values above. This completes all twelve (+,-) secondary regimes.

## 6. Positive outer source and positive core target

The four normalized rows have
\[
 C=\phi+c_*+pa+qb-gB,\qquad
 b+A\sin\phi-B\cos\phi\ge W,
\]
and
\[
\begin{array}{c|rrrr}
 &c_*&p&q&g\\ \hline
0\text{ direct}&-.25648&0&.94766&.62095\\
1\text{ reversed}&-.11418&-.09133&.88074&.62095\\
3\text{ direct}&-.94615&.51554&1.19909&.58829\\
3\text{ reversed}&.07943&-.19335&.76744&.62750.
\end{array}
 \tag{27}
\]
Nonpositive \(\phi\) is impossible. Feasibility implies
\(d-\tfrac12+\sin\phi/12-\cos\phi/2\ge0\).
This is increasing and negative at .4, so \(\phi>.4\). A target on the core corner would imply
\[
 d-\tfrac12+\frac{\sin\phi}{12}-\cos\phi
 <.4+\frac{.645}{12}-.764<0.
\]
Thus \(A=7/12\).

Set \(b_0=W-(7/12)\sin\phi
=\tfrac12+\tfrac12\cos\phi-\sin\phi/12>.828\).
At contact \(B=(b-b_0)/\cos\phi\), and \(b\ge b_0,\ a<.97,\ r>.9,\ B<.1\). A minimum uses contact, since increasing \(B\) lowers the cost. One then minimizes
\[
 pa+\left(q-\frac g{\cos\phi}\right)b
\]
on \([b_0,d]\). For \(p\le0\), its derivative exceeds
\(q-g/.764-.9p>0\), giving \(B=0\), and
\[
 .4+c_*+.97p+.828q>.898.
 \tag{28}
\]
For \(p>0\) the function is concave. Its two endpoint lower bounds are
\[
 .4+c_*+.899p+.828q>.898,\qquad
 .4+c_*+.899(p+q)-.1g>.898.
 \tag{29}
\]

## 7. Positive core source and positive outer target

The four rows are
\[
\begin{array}{c|rrrr}
 &c_*&p&q&g\\ \hline
0\text{ direct}&-.02953&0&.99940&1.08816\\
1\text{ reversed}&.12783&.13422&1.03828&1.13855\\
3\text{ reversed}&.46969&.33147&1.13360&1.04073\\
3\text{ direct}&-.02145&0&.71553&1.04729.
\end{array}
 \tag{30}
\]
Here \(C=\phi+c_*+gb-pA-qB\) and
\(b+A\sin\phi-B\cos\phi\ge W\). Nonpositive \(\phi\) is impossible. The maximum margin for \(\phi\le.4\) is
\[
 d_C-\tfrac12+(a_0-\tfrac12)\sin\phi-\tfrac12\cos\phi,
\]
which is increasing and negative at .4. Therefore \(.4<\phi\le.7\).

Choose \(\lambda=g\), canceling the core coordinate. For the first three rows, full-circle support gives
\[
 C\ge F(\phi)=\phi+c_*+\frac{g+p+q}{2}
                    +g\sin\phi-RN(\phi).
 \tag{31}
\]
A norm of a rotating vector satisfies
\(|N'|\le\min\{g,\sqrt{p^2+q^2}\}\).
For the three rows use the respective bounds \(1,\ 1.047,\ g\). Each has
\(F(.4)>.98\) and \(F'>-.27\), using (9). Hence
\(F>.98-.3(.27)=.899>.898\).

For the fourth row, \(g\cos\phi-q>0\) and the primary coefficient is negative; the outer support is axial. Its value is \(F_A\) of (21) with \(p=0,\lambda=g\). It has \(F_A(.4)>1.01,\ F_A'>-.1\), so \(F_A>.98\). Every secondary branch in (8) is now closed.

## 8. All mixed primary axes

By (7), consider source \(-e\). A core source and outer target would have margin at most
\[
 \frac1{12}-1.399\cos\phi+.4|\sin\phi|
 <\frac1{12}-1.399(.764)+.4(.645)<0.
 \tag{32}
\]
So the source is outer and target core.

If the target sign and the sign of \(\phi\) are the same, the margin is at most
\[
 a_0-\tfrac12-(d_C+\tfrac12)\cos|\phi|
                   -\tfrac12\sin|\phi|.
 \tag{33}
\]
This is convex and negative at both endpoints of \([0,.7]\). With opposite signs the upper bound is
\[
 a_0-\tfrac12-(d_C+\tfrac12)\cos|\phi|
                   +(d_C-\tfrac12)\sin|\phi|.
 \tag{34}
\]
It is increasing and negative at .4; hence \(|\phi|>.4\). A positive core target would have \(\phi<-.4\), giving
\(\delta=\phi+\sigma\alpha-\beta<\pi/4-.4<.76\), impossible. Only a negative target with \(.4<\phi\le.7\) survives.

### 8.1. Negative outer source

The four costs \(C=\phi+c_*+pa-qb+gB\) have
\[
\begin{array}{c|rrrr|r}
 &c_*&p&q&g&\lambda\\ \hline
1\text{ direct}&.12783&-.13422&1.03828&1.13855&1.95\\
3\text{ direct}&.46969&-.33147&1.13360&1.04073&1.95\\
0\text{ reversed}&-.02953&0&.99940&1.08816&2.01\\
3\text{ reversed}&-.02145&0&.71553&1.04729&1.95.
\end{array}
 \tag{35}
\]
Subtract \(\lambda\) times the SAT margin
\(a-A\cos\phi+B\sin\phi-W\), and use source full-circle support.

For a target on the core corner, the functional
\(\lambda\cos\phi\,A+(g-\lambda\sin\phi)B\) is concave in \(B\), hence minimized at the join or diagonal endpoint. The diagonal is smaller because
\[
 \lambda\{\sin\phi+(\sqrt2-1)\cos\phi\}>g,
\]
as follows from \(1.95\{.389+.414(.764)\}>1.139\). Thus
\[
\begin{split}
 C\ge F_D={}&\phi+c_*+\lambda+\frac{-p+q}{2}+gd_C
 -R\sqrt{(\lambda-p)^2+q^2}\\
 &+\lambda(\tfrac12+d_C)\cos\phi
  +\lambda(\tfrac12-d_C)\sin\phi.
\end{split}
 \tag{36}
\]
This is strictly concave, since
\(1.0589(.764)-.059(.645)>0\). Its two endpoint values at .4 and .7 are \(>.898\) in all four rows.

On the core side take \(\lambda=g/\sin\phi\), canceling \(B\):
\[
\begin{split}
 C\ge H(\phi)={}&\phi+c_*+\frac g{\sin\phi}
 +\frac{-p+q+g}{2}+\frac{13g}{12}\cot\phi\\
 &-R\sqrt{\left(\frac g{\sin\phi}-p\right)^2+q^2}.
\end{split}
 \tag{37}
\]
Put \(X=g/\sin\phi-p,\ N=\sqrt{X^2+q^2},\ Z=RX/N\). Then \(Z\) decreases and
\[
 H'=1+\frac g{\sin^2\phi}
       \left\{\cos\phi(Z-1)-\frac{13}{12}\right\}.
 \tag{38}
\]
Fixed comparisons give \(Z(.4)<1.913,\ Z(.6)<1.85\). On \([.4,.6]\), \(\cos\phi>.825\); on \([.6,.7]\), \(\cos\phi>.764\). Since \(g>1.04\),
\[
\begin{aligned}
1-.825^2+1.04\{.913(.825)-13/12\}&<0,\\
1-.764^2+1.04\{.85(.764)-13/12\}&<0
\end{aligned}
\]
show \(H'<0\). The bounding quadratic decreases with the cosine on each interval. Finally \(H(.7)>.898\) for every row.

### 8.2. Positive outer source

Use exactly the six rows (13). Take \(\lambda=g/\sin\phi\). Since \(\lambda>p\), the source functional \((p-\lambda)a+qb\) is minimized at the axial state. The remaining core primary term is at least \(\lambda d_C\cos\phi\). Hence
\[
 C\ge F(\phi)=\phi+c_*+pa_0+\frac g2+
 \frac g{\sin\phi}
 \{(\tfrac12+d_C)\cos\phi-(a_0-\tfrac12)\}.
 \tag{39}
\]
With \(A=\tfrac12+d_C,\ B=a_0-\tfrac12\),
\[
 F''=g\frac{2A\cos\phi-B(1+\cos^2\phi)}{\sin^3\phi}>0.
\]
The numerator increases with the cosine and exceeds
\(2(1.0589)(.764)-.915(1+.764^2)>0\).
For every row, the single rational reference point .55 has
\[
 F(.55)>.98,\qquad |F'(.55)|<.4.
\]
The convex tangent bound gives
\(F(\phi)>.98-.15(.4)=.92>.898\) on the entire interval.

## 9. Exact arithmetic and scope

The checker uses rational BigInt arithmetic. Square roots at the finitely many displayed arguments are bracketed by integer-square comparisons; sine and cosine at fixed rational arguments are bounded by alternating Taylor sums. Every numerical assertion used here is a fixed rational comparison. The support rules, derivative signs, concavity, and the branch inventory supply continuum coverage.

The conclusion is the complete mixed \(C/O\) zero-quarter component:
\[
 \boxed{\text{Every mixed pair on edges }0,1,3
        \text{ under (3)--(6) has }C>.898>.89765.}
\]
The seven-role table may be summed only after its other components are proved. No unrestricted packing theorem or claim about those remaining components is made here.

