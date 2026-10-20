# The exceptional aligned-E contact with a negative T primary: the sharp strip

## 1. Actual domain and conclusion

Use \(q_L,Q_1,h,q_*\) and the exact supporting dual from
[the positive-T critical theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_CRITICAL_STRIP.md).
In particular \(q_L<q_*<Q_1\), \(R=\sqrt{q_*}\), and all decimals
below are exact rationals.

The sorted squares are contained at a common ceiling \(q\le q_*\).
T has the actual boundary classification used by the boundary
bridge: it lies either on the outer circle at q or on its true
core boundary. This classification is used only for the local
entry in Section 2; the subsequent stress needs just the stated
flat T contact.
H,A have positive signs, B,D negative signs, and G may have either
sign. Retain HG2, GA1, either AB owner, DE3 and EH0. Their two
nonnegative primary errors are
\[
              x=d_{GA}\ge0,\qquad e=d_{DE}\ge0,
              \qquad t=x+e\in[.1,.16].
\tag{1}
\]
E has \(y_E\ge0\), EH0 is aligned, and the actual contact is
\[
                              a_H+y_E=1.
\tag{2}
\]
The remaining actual T regime is either
\[
\begin{array}{c|c|c}
 &\text{owners}&\text{negative primary error}\\ \hline
 \mathrm{TD}&BT2,TD2&d_{TD}=-s<0\\
 \mathrm{BT}&BT3,TD0\text{ with TD aligned}&d_{BT}=-s<0.
\end{array}
\tag{3}
\]
All other errors are arbitrary, with the actual cyclic positive
and negative variations at most h.

**Theorem.** Every system (1)--(3) has \(x=0\). More precisely,
either the corresponding secondary T owner is already an actual
weak witness, and the original exceptional-E critical theorem
applies after that same-state reselection, or the system is
strictly impossible. The result includes both AB owners, every
ordinary error sign, weak ties, and either radial kind of E.

This is a sharp statement at \(q_*\); it does not remove the
actual hard-chain equality case by replacing the sharp radius
with the larger rational ceiling.

## 2. Entry to a flat secant and the exact gain

The entry comparisons in Sections 4--5 of
[the complete core-E positive-GA theorem](HAND_G5_POSITIVE_GA_HG2_CORE_E_COMPLETE_EXCLUSION.md)
are local to B,T,D and independent of E's radial kind or owners.
For negative TD2, either TD0 is already actual, or T is flat with
\[
                         a_T=7/12,\qquad 0<s<.3.
\tag{4}
\]
For negative BT3 with aligned TD0, either BT2 is already actual,
or T is flat with
\[
                   a_T=7/12,\quad 0<y_T<.156,
                          \qquad 0<s<.09.
\tag{5}
\]
The common-radius and signed projection hypotheses of those
comparisons are exactly the hypotheses here. If a secondary is
reselected, all actual frames and states stay fixed, and
[the original critical-strip theorem](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_SHARP_CRITICAL_STRIP.md)
already gives x=0. It remains to exclude (4) and (5).

Use the original exact dual \((k,l,c,\eta)\) at t, without the
positive-T adaptation. It satisfies
\[
\begin{gathered}
 .925<k<.985,\quad .925<c<1,\quad l<.67,\quad
 .27<\eta<.31,\quad 1<f(t)<1.04,\\
 l/k<.675,\quad .63<l/c<.68,
 \quad c-k<.02,\quad c-l>.296,
 \qquad f(a)=\cos a+\eta\sin a.
\end{gathered}
\tag{6}
\]
Give HG,GA,AB,DE,EH weights \((kf(x),k,l,1,f(e))\).
In the TD case give BT2,TD2 weights \((c,c\sec s)\);
in the BT case give BT3,TD0 weights \((c\sec s,c)\).
The actual signed T tangent cancels exactly. Put \(K=13/12\).
Relative to the baseline with equal T weights, the gains are
\[
\begin{aligned}
 G_D(s)&=c(\sec s+K\tan s-1)
    -R\{\sqrt{1+c^2\sec^2s}-\sqrt{1+c^2}\},\\
 G_B(s)&=c(\sec s+K\tan s-1)
    -R\{\sqrt{l^2+c^2\sec^2s}-\sqrt{l^2+c^2}\}.
\end{aligned}
\tag{7}
\]
The TD change is in the D pair \((1,c\sec s)\), which has
no ordinary angle because DE and TD are both primary. The BT
change is in the B pair \((l,c\sec s)\), which has only the
possible actual AB angle because TD is aligned.

## 3. Primary split and the ordinary-angle bounds

For fixed t,s the secant coefficient is fixed during the G/E
split \(x+e=t\). The proof of strict split concavity in the
original critical theorem therefore applies without change:
the changing EH weight multiplies the exact zero (2).
Only the E face \((x,e)=(0,t)\) and the G face \((t,0)\)
remain. Their baseline difference is
\[
 (1-k)(3-C_\eta(t))
 +R\{\sqrt{f(t)^2+k^2}-\sqrt{1+k^2f(t)^2}\}>0,
\tag{8}
\]
where \(C_\eta\) is defined in (29) of the positive-T critical
theorem. Thus it suffices to give a common lower envelope and
exclude the E face.

Use the ordinary functions \(H,V,U\) from that theorem. Put
\[
                      V_A(a)=V_{k,l}^{l}(a),
 \qquad V_B(a)=V_{l,c}^{c}(a).
\tag{9}
\]
The ordinary errors have signed sum \(s-t\), positive variation
at most \(h-t\), and negative variation at most \(h-s\).
The only potentially mixed block is B in the TD case. H and A
each have at most one ordinary argument, and D has none. In the
BT case even B has at most one argument.

### 3.1 If \(s\le t\), the envelope is at least
\(\min(V_A(t-s),V_B(t-s))\)

Let \(d=t-s\in[0,.16]\). Enlarge the ordinary positive budget
to h-d and its negative budget to h; this retains every actual
error list. The separately concave concentration reduces to
pure, same-block, and separated endpoints.

For d>0 the H pure charge is greater than 1.25d, while
\(V_B(d)<1.102d\), by the original critical bounds. At d=0
every pure charge vanishes. Keep both A and B as possible minima;
no A-versus-B comparison near d=0 is needed. At the far endpoint, H and A dominate \(V_B(h)\).
The same-block B comparison is valid throughout [0,.16], because
\[
 .63\{\cos(h-d)+\sin(h-d)-1\}-\cos d+\cos h>.011.
\tag{10}
\]
Indeed it has positive second derivative, negative first
derivative at .16, and value greater than .011 at .16.
For separated endpoints, the old chord proof also holds on
the larger interval [0,.16]:
\[
 V_B(h)-V_B(d)>.925(.7)(h-d),
 \qquad U_i(P)\ge-.545(1.04)P.
\tag{11}
\]
The difference of the two slopes is greater than .08.
This removes every separated saturation.

In the BT case the enlarged B coefficient satisfies
\(c\sec s<1.005<1.04\), its ratio is greater than
\(.63\cos(.09)>1/2\), and its actual negative coefficient is l.
Coordinate monotonicity of H and \(l<c\) imply
\[
                       V_{l,c\sec s}^{l}(a)\ge V_B(a)
                         \quad(0\le a\le h).
\tag{12}
\]
For completeness, the needed larger-coordinate monotonicity
follows by squaring its derivative comparison and using
\(\sin h<.8\le2r/(1+r^2)\) for \(1/2\le r\le1\).
There is no same-block B endpoint in this case, and the same
positive cost and far-index comparisons apply. This proves
the claimed envelope in both T regimes.

### 3.2 If \(s\ge t\), the envelope is at least
\(-.545(1.04)(s-t)\)

This case occurs only for negative TD. Write \(d=s-t\ge0\).
The pure positive terms satisfy the asserted bound. For a
separated positive/negative pair use concavity and
\[
                     V_j(h)\ge V_B(h)>.77h.
\tag{13}
\]
Thus \(V_j(N)>.77N\), whereas
\(U_i(P)\ge-.545(1.04)P\). Since \(P-N=d\), their sum is
greater than \(-.545(1.04)d\).

For the possible mixed B block, let \(P-N=d\), \(0\le N\le P\le h\),
and \(r=l/c>.63\). Its difference from the pure positive
charge \(U_{l,c}(d)\) is
\[
                    c\{r(\phi(P)-\phi(P-N))+\cos N-1\},
              \qquad \phi(a)=\cos a+\sin a.
\tag{14}
\]
With \(b=N/2\), its sign is that of
\(r\{\cos(P-b)-\sin(P-b)\}-\sin b\).
Since P≤h, this is at least
\(.63\{\cos(h-b)-\sin(h-b)\}-\sin b\).
After division by \(\cos b>0\), the latter is affine in
\(\tan b\), decreasing for \(0\le b\le h/2\); its far value
before division is
\[
             .63\{\cos(.35)-\sin(.35)\}-\sin(.35)>.032.
\tag{15}
\]
Hence (14) is nonnegative. This completes the full positive-net
envelope, including actual cancellation of both ordinary signs.

## 4. Negative TD: concavity and one strict secant endpoint

For \(0\le s\le t\le.16\), each function
\[
                  G_D(s)+V_i(t-s),\qquad i=A,B,
\tag{16}
\]
is strictly concave. Here is a uniform numerical reserve proved
only with rational Taylor bounds. If \(q=\sec s\), then
\[
 \frac{d^2}{ds^2}\sqrt{1+c^2q^2}
 \ge\frac{c^2}{\sqrt{1+c^2}}.
\]
Also
\[
 (\sec s+K\tan s)''
 =\sec s(2\sec^2s-1)+2K\sec^2s\tan s<1.425,
 \qquad \frac{Rc}{\sqrt{1+c^2}}>1.343.
\tag{17}
\]
Consequently \(G_D''<.082\). The standard negative-norm
curvature bound from the original critical proof gives
\[
 V_A'',V_B''<-(\cos(.16)-.762)l<-.131.
\tag{18}
\]
Thus the second derivative in (16) is below -.048.
It is enough to check the endpoints s=0,t. At s=0,
\(V_A(t)\ge V_B(t)\) by the original critical theorem.
At s=t, Section 6 proves
\[
                            G_D(t)>V_B(t).
\tag{19}
\]
Strict concavity now gives
\(G_D(s)+\min(V_A(t-s),V_B(t-s))>V_B(t)\) for every
\(0<s\le t\).

For \(t\le s<.3\), direct differentiation gives
\[
 G_D'(s)=c\sec^2s\left\{K+\sin s
       -\frac{Rc\sin s}{\sqrt{\cos^2s+c^2}}\right\}>.88.
\tag{20}
\]
Indeed the ratio in braces multiplying \(\sin s\) is less
than 1.432, so the braces exceed \(K-.432\sin(.3)\),
and \(c>.925\). This derivative exceeds .545(1.04).
Equations (19)--(20) and the positive-net envelope therefore
give the same strict lower bound \(>V_B(t)\) for every
\(s\ge t\). All negative TD magnitudes in (4) are covered.

## 5. Aligned negative BT: the two short secant endpoints

Here \(0<s<.09<t\), so only Section 3.1 is needed.
The gain \(G_B\) is strictly concave on [0,.09]. In fact
\[
 (\sec s+K\tan s)''<1.218,
 \qquad \frac{R}{\sqrt{1+(l/c)^2}}>1.63,
\tag{21}
\]
and the same norm-curvature calculation gives
\(G_B''/c<-.41\). Since both ordinary charges are concave,
the functions \(G_B(s)+V_i(t-s)\), i=A,B, are strictly
concave. It suffices to check s=0 and s=.09.

The zero endpoint is the old pure comparison. At s=.09,
Section 6 proves
\[
                 G_B(.09)+V_B(t-.09)-V_B(t)>.00123.
\tag{22}
\]
For \(d=t-.09\le.07\), the A comparison from the critical
theorem gives
\[
                  V_A(d)-V_B(d)\ge-.5(.02)d\ge-.0007.
\tag{23}
\]
If c≤k this difference is already nonnegative; otherwise
(23) is the integral bound with \(l/k<.675\).
The A endpoint therefore has reserve greater than .0005.
Strict concavity gives the required strict lower bound for
every genuine negative BT in (5).

## 6. Two rationalized whole-strip scalar certificates

Let \(S=\sin t\), \(C=\cos t\), and use the original exact
dual (6). Rationalizing the two norm differences in (19)
and factoring the positive quantity \(c\sin t\) gives
\[
 G_D(t)-V_B(t)=c\sin t\,J_D(t),
\tag{24}
\]
where
\[
\begin{aligned}
 J_D(t)={}&(S+K)/C\\
 &-R\left\{
 \frac{cS}{C^2(\sqrt{1+c^2/C^2}+\sqrt{1+c^2})}
 +\frac{2l}{\sqrt{l^2+c^2}+\sqrt{l^2+c^2-2lcS}}
 \right\}.
\end{aligned}
\tag{25}
\]
This factorization preserves the cancellation that would be
lost by separately bounding the unshifted radicals.

For (22) put \(b=.09\), \(s_b=\sin b\), \(c_b=\cos b\),
\(a_b=\tan(b/2)=s_b/(1+c_b)\), and
\(S_d=S c_b-C s_b=\sin(t-b)\). Then
\[
 G_B(b)+V_B(t-b)-V_B(t)=c\sin b\,J_B(t),
\tag{26}
\]
with
\[
\begin{aligned}
 J_B(t)={}&a_b(1/c_b-C)+K/c_b+S\\
 &-R\left\{
 \frac{cs_b}{c_b^2(\sqrt{l^2+c^2/c_b^2}+\sqrt{l^2+c^2})}
 +\frac{2l(C+Sa_b)}{
       \sqrt{l^2+c^2-2lcS_d}+\sqrt{l^2+c^2-2lcS}}
 \right\}.
\end{aligned}
\tag{27}
\]

Use the exact degree-10 polynomial-with-remainder arithmetic
in Section 7 of
[the positive-T critical theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_CRITICAL_STRIP.md).
Its starting models are exactly the same:
\[
 t=.13+.03X,\quad |X|\le1,\quad
 q_*\in[(q_L+Q_1)/2\ \pm\ (Q_1-q_L)/2],
 \quad u_0\in[1-.6375t\ \pm\ .00175].
\tag{28}
\]
Construct the chain and original dual, without any adaptation,
then substitute (25) and (27), using the rational degree-13/14
sine/cosine bounds and degree-12 binomial rules already specified
there. Use the displayed grouping of each sum and product.
Every binomial argument has coefficient norm plus remainder
less than .071. Each resulting polynomial is univariate of
degree at most 10, with eleven potential coefficients.

Writing \([P_D,E_D]\), \([P_B,E_B]\) for the two resulting
models, exact rational coefficient addition gives
\[
\begin{array}{c|ccc|c}
 &P(0)\text{ lower}&\sum_{j\ge1}|P_j|\text{ upper}
       &E\text{ upper}&P(0)-\sum_{j\ge1}|P_j|-E\text{ lower}\\ \hline
 J_D&.02428&.014528&.009058&.0006\\
 J_B&.02630&.002102&.009259&.0149.
\end{array}
\tag{29}
\]
The final lower quantities from the exact calculation begin
\(.00069568265427620\) and \(.01494069085077756\), respectively.
The rational inequalities in (29) are the proof bounds; no
sampled angle value enters. Thus \(J_D>.0006\), proving
(19), and
\[
 c\sin(.09)J_B>.925\sin(.09)(.0149)>.00123,
\tag{30}
\]
proving (22). The construction uses two full-interval coefficient
norms and no angle subdivision or coefficient-row inventory.

## 7. Completion at the original sharp radius

On the E face the baseline without a negative T gain, plus
\(V_B(t)\), is exactly the nonnegative supporting hard defect
\(N(N-R)/k_2\) from the original critical theorem.
Sections 4 and 5 show that every genuine flat negative T
magnitude adds a strictly positive amount even after minimizing
over every actual ordinary sign pattern. This contradicts the
sum of the weighted actual separation inequalities.
The G face is strictly stronger by (8), and strict split
concavity excludes every interior G/E allocation as well.
The only remaining possibility is same-state secondary T
reselection, which gives x=0 by the old sharp theorem.
No assumption on E's radial kind was used after (2).
