# The remaining canonical negative boundary has total hard error below 3/200

## 1. The exact five-anchor statement

Put
\[
 Q=\frac{1957767069}{500000000},\quad R=\sqrt Q,
 \quad K=\frac{13}{12},\quad r_0=\frac3{200},
 \qquad W(z)=\frac{1+\cos z+\sin z}{2}.
\tag{1}
\]
Let H, A, B and D have nonnegative sorted own-frame coordinates.
Write E's transverse magnitude as c_E, with its signed transverse
coordinate equal to -c_E in this reflected convention. Assume
\[
\begin{gathered}
 a_i\ge b_i\ge0,\quad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q
 \quad(i=H,A,B,D),\\
 a_E\ge c_E\ge0,\quad
 (a_E+1/2)^2+(c_E+1/2)^2\le q,\\
 t,u,e\ge0,\qquad\alpha=t+u+e\le27/100.
\end{gathered}
\tag{2}
\]
Retain the five necessary inequalities
\[
\begin{aligned}
 (\sec e)b_H+a_A\cos t-b_A\sin t
   &\ge W(t)+\frac12+\frac12\sec e+K\tan e,\\
 b_A+b_B&\ge1,\qquad b_A\ge\frac12,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 a_D+a_E\sin\alpha-c_E\cos\alpha&\ge W(\alpha),\\
 a_H+c_E&\ge1.
\end{aligned}
\tag{3}
\]
The first is the same-intermediate-circle negative HG0--GA0
composite after using its true core primary bound 7/12. The
opposite zero path is aligned. E is at the orientation endpoint
adjacent to H in these reflected coordinates.

**Capture theorem.** Every system (2)--(3) satisfies
\[
                              t+e<\frac3{200}.
\tag{4}
\]
This is a theorem about the displayed necessary five-anchor
system. It assumes no replacement G or T, physical angular gap,
unprinted G1 inequality, or small-mismatch condition. It does not
by itself assert the sharp radius bound after (4).

All terminating decimals below are exact rational numbers. The
proof uses two continuous cubic formulas and whole-polynomial
coefficient inequalities. No sampled angle, state cover, or
acceptance result is a premise.

## 2. One common stress on the truncated angular simplex

Suppose, for contradiction, that t+e>=r_0. Write
\[
 s=\sin\alpha,\quad c=\cos\alpha,\quad
 \eta=\frac3{500},\quad k=\frac{307}{1000}.
\tag{5}
\]
In particular
\[
 \frac{1499}{100000}<\sin(r_0)\le s\le\frac{27}{100}.
\tag{6}
\]
At fixed alpha choose positive weights a and f, and put
\[
                         \lambda=fc+ks.
\tag{7}
\]
Give the five inequalities in (3), in their displayed order,
weights 1,a,1,f,lambda. Add `eta*b_A>=eta/2`. The collected
forces on the same five actual centers are
\[
\begin{array}{c|cc}
 &F_x&F_y\\ \hline
 A&\cos t&a+\eta-\sin t\\
 B&\cos u&a-\sin u\\
 D&f&1\\
 H&\lambda&\sec e\\
 E&fs&ks.
\end{array}
\tag{8}
\]
The E coordinates in this force row are (a_E,c_E). The demand is
\[
 \mathcal D=W(t)+\frac12+\frac12\sec e+K\tan e
       +a+\frac\eta2+1+W(u)+fW(\alpha)+\lambda.
\tag{9}
\]
Circle support therefore gives the necessary inequality
\[
 N(t,u,e):=\mathcal D-
   \sum_{i=A,B,D,H,E}
       \left(R\lVert F_i\rVert-\frac{F_{ix}+F_{iy}}2\right)
 \le0.
\tag{10}
\]

Define
\[
 g_p(z)=\cos z-R\sqrt{1+p^2-2p\sin z},
 \qquad
 \Phi_\lambda(z)=\sec z+K\tan z
                     -R\sqrt{\lambda^2+\sec^2z}.
\tag{11}
\]
After collecting (8)--(9), the terms in N which depend on the
split t,u,e are exactly
\[
                  g_{a+\eta}(t)+g_a(u)+\Phi_\lambda(e).
\tag{12}
\]
All other terms depend only on alpha and its fixed weights.

The formulas below satisfy
\[
 .58<a<.69,\qquad .93<f<1.17,
 \qquad .93<\lambda<1.17.
\tag{13}
\]
The whole-interval calculation in Section 3 of
`HAND_G5_NEGATIVE_HG_LARGE_TRANSVERSE_DE_ALIGNMENT_EXCLUSION.md`
therefore applies unchanged:
\[
 g_p''(z)<-\frac25\quad(0<p<18/25),
 \qquad\Phi_\lambda''(z)<\frac{39}{100}
 \quad(0\le z\le27/100).
\tag{14}
\]
In particular a+eta<18/25. To recall the numerical-free scope of
(14), that proof uses
\[
 g_p''=-\cos z+R
 \frac{p(p-\sin z)(1-p\sin z)}{(1+p^2-2p\sin z)^{3/2}},
\]
the strict decrease of the fraction in sin z, and the rational
bounds `cos z>=24/25`, `tan z<=2/7`, `sec z<=25/24`.
For the H term it uses `R>989/500` and
`sec z/sqrt(lambda^2+sec^2 z)>50/77`. These hypotheses depend
only on (13), not on the placement of E's mixed edge.

Set r=t+e. At fixed r, (12) is strictly concave as t ranges over
`[0,r]`, because its second derivative is
`g_{a+eta}''(t)+Phi_lambda''(r-t)<0`. Its minimum is at t=0
or e=0. On those two sides, the functions of r are again
strictly concave, with second derivatives respectively
`g_a''(alpha-r)+Phi_lambda''(r)<0` and
`g_{a+eta}''(r)+g_a''(alpha-r)<0`.
Thus on `r_0<=t+e<=alpha`,
\[
 N(t,u,e)\ge\min_{0\le j\le3}N(V_j),
\tag{15}
\]
where the four intrinsic vertices are
\[
\begin{array}{c|ccc}
 j&t&u&e\\ \hline
 0&\alpha&0&0\\
 1&0&0&\alpha\\
 2&r_0&\alpha-r_0&0\\
 3&0&\alpha-r_0&r_0.
\end{array}
\tag{16}
\]
The weights are identical at all four vertices for each alpha.

## 3. Two explicit cubic formulas

Use the following rational polynomials:
\[
\begin{array}{c|l}
1499/100000\le s\le7/50&\\ \hline
a&.58266015+.49799768s+.01791176s^2+.01988864s^3\\
f&1.16228301-.98466323s+.67559020s^2-.53098860s^3
\end{array}
\tag{17}
\]
and
\[
\begin{array}{c|l}
7/50\le s\le27/100&\\ \hline
a&.54399682+1.06786562s-2.39861499s^2+1.24305637s^3\\
f&1.18077884-1.24066546s+1.71820838s^2-1.57930403s^3.
\end{array}
\tag{18}
\]
Either formula is allowed at their common endpoint.

Here is the elementary coefficient operation used throughout
the remaining arithmetic. If
`P(m+x)=sum_i p_i x^i`, put
\[
 \mathsf L(P;m,r)=p_0-
  \sum_{i\ {\rm odd}}|p_i|r^i+
  \sum_{i\ge2\ {\rm even}}\min\{p_i,0\}r^i.
\tag{19}
\]
Then P>=L on `|s-m|<=r`; its upper bound is `-L(-P;m,r)`.
Translation uses just
\[
              p_j=\sum_{i\ge j}\binom ij P_i m^{i-j}.
\tag{20}
\]
The two center/radius pairs used here are
\[
 (m_0,r_0^{\rm int})=(15499/200000,12501/200000),
 \qquad (m_1,r_1^{\rm int})=(41/200,13/200).
\tag{21}
\]
Applying (19) to (17)--(18) proves the a,f bounds in (13),
and gives `f+ks<1.17`. This proves the upper bound for lambda.
For its lower bound, use c>=24/25 and s<=27/100 to get
\[
 \lambda-f
 =s\left(k-\frac{fs}{1+c}\right)
 \ge s\left(\frac{307}{1000}
       -\frac{117}{100}\frac{27}{100}\frac{25}{49}\right)
 \ge0.
\tag{22}
\]
Thus lambda>=f>.93, completing (13).

## 4. Rational constants for the fixed angle

For the two vertices containing r_0, put
\[
 \sigma=\frac{14999437506}{10^{12}},\qquad
 \chi=\frac{999887502109}{10^{12}}.
\tag{23}
\]
Alternating Taylor bounds at r_0=3/200 give
\[
 |\sin r_0-\sigma|<10^{-12},\qquad
 |\cos r_0-\chi|<10^{-12},\qquad\chi>99/100.
\tag{24}
\]
For example use the seventh- and fifth-degree sine bounds and
the sixth- and fourth-degree cosine bounds. All four comparisons
in (24) are direct positive rational comparisons.

At vertices 2 and 3 replace the trigonometric constants by
\[
\begin{gathered}
 \sin r_0\rightsquigarrow\sigma,\quad
 \cos r_0\rightsquigarrow\chi,\quad
 \sec r_0\rightsquigarrow1/\chi,\quad
 \tan r_0\rightsquigarrow\sigma/\chi,\\
 \cos(\alpha-r_0)\rightsquigarrow c\chi+s\sigma,
 \quad\sin(\alpha-r_0)\rightsquigarrow s\chi-c\sigma.
\end{gathered}
\tag{25}
\]
Denote the resulting forces and demand by tildes. Vertices 0
and 1 are unchanged. For vertices 2 and 3, (24) bounds the
sum of all force-coordinate absolute changes by `6*10^(-12)`.
It also bounds the demand change by `6*10^(-12)`; in particular
the changes in secant and tangent are both less than `2*10^(-12)`.
The Euclidean norm is 1-Lipschitz with respect to Euclidean
distance, and R<2. Hence each exact endpoint scalar exceeds
the scalar with these rational constants minus `10^(-8)`.
This generous uniform error bound is independent of s and of
the two cubic families.

## 5. Explicit positive circle masses at the four vertices

For every positive mass m,
\[
 R\lVert F\rVert\le mQ+\frac{\lVert F\rVert^2}{4m}.
\tag{26}
\]
It follows by expanding the square
`(sqrt(m)*R-|F|/(2sqrt(m)))^2`.
The masses below may depend on the vertex, since they are used
only after the exact-norm reduction (15).

Each tuple lists the coefficients of `1,s,s^2,s^3`.
For the first interval use
\[
\begin{array}{c|rrrr}
A_{\rm rot}&.29321190&-.06437836&-.08548820&-.02487824\\
A_{\rm fixed}&.29321149&.06383697&.02230447&.00005344\\
A_{r_0}&.29128247&.06262238&.02265742&.00000092\\
B_{\rm fixed}&.29244531&.06335186&.02244512&.00003228\\
B_{\rm shift}&.29434761&-.06184228&-.08551134&-.02485409\\
D&.38742819&-.18856981&.16249805&-.12349400\\
H_{\rm fixed}&.38742971&-.12988701&.03634484&-.02886230\\
H_{\rm sec}&.38742821&-.12977080&.11595495&.02435946\\
H_{r_0}&.38744825&-.12988079&.03634516&-.02886114\\
M_E&.30376027&-.24055072&.17155095&-.13228033
\end{array}
\tag{27}
\]
and for the second interval use
\[
\begin{array}{c|rrrr}
A_{\rm rot}&.28814817&.01328081&-.44460217&.29999321\\
A_{\rm fixed}&.28783482&.14208751&-.29930677&.11781294\\
A_{r_0}&.28599173&.13958462&-.29326945&.11390367\\
B_{\rm fixed}&.28710297&.14108777&-.29689570&.11625249\\
B_{\rm shift}&.28923047&.01661368&-.44810167&.30220724\\
D&.39080192&-.23548383&.35513119&-.32128996\\
H_{\rm fixed}&.39095601&-.17973189&.24832696&-.27086828\\
H_{\rm sec}&.39075678&-.17590352&.30393360&-.16369759\\
H_{r_0}&.39097437&-.17972312&.24831665&-.27085564\\
M_E&.30824754&-.30272741&.42529811&-.38889082.
\end{array}
\tag{28}
\]
Use A_rot at vertex 0, A_r0 at vertex 2, and A_fixed otherwise.
Use B_fixed at vertices 0 and 1, and B_shift at 2 and 3.
Use H_sec at vertex 1, H_r0 at vertex 3, and H_fixed otherwise.
D always uses its displayed mass. The E mass is `s*M_E`.

The coefficient operation (19), with (21), gives on both
entire intervals
\[
 m_A,m_B>.26,
 \qquad m_D>.34,
 \qquad m_H>.35,
 \qquad M_E>.24.
\tag{29}
\]
Since s is positive by (6), all five masses are positive.

## 6. Eight explicit rational polynomials

Let J={A,B,D,H}, and let the tilde forces and demands at each
vertex have the precise meaning in (8)--(9), (16), (25).
Put
\[
 \delta_j=\begin{cases}0&j=0,1,\\10^{-8}&j=2,3,\end{cases}
 \quad v_j=\begin{cases}c&j=1,\\1&j=0,2,3,\end{cases}
 \quad D_j=4m_A m_B m_D m_H M_E>0.
\tag{30}
\]
Define a lower bound for the exact endpoint scalar by
\[
 \widehat N_j=\widetilde{\mathcal D}_j-\delta_j
 -\sum_i\left(m_iQ+
       \frac{\lVert\widetilde F_{ij}\rVert^2}{4m_i}
       -\frac{\widetilde F_{ij,x}+\widetilde F_{ij,y}}2\right).
\tag{31}
\]
The sum includes E with mass sM_E. Equations (24)--(26) imply
\[
                              N(V_j)\ge\widehat N_j.
\tag{32}
\]

Here are ordinary polynomial definitions of the cleared
expressions; all operations are in
`Q[s,c]/(c^2+s^2-1)`. Write `Fhat_ij=v_j*Ftilde_ij`, and put
\[
\begin{aligned}
 A_j(s)+B_j(s)c={}&
 D_jv_j^2\left[
  \widetilde{\mathcal D}_j-\delta_j
  -Q\left(\sum_{i\in J}m_i+sM_E\right)
  +\frac12\sum_{i\in J}
       (\widetilde F_{ij,x}+\widetilde F_{ij,y})
  +\frac{s}{2}(f+k)\right]\\
 &-\sum_{i\in J}\frac{D_j}{4m_i}\lVert\widehat F_{ij}\rVert^2
  -\frac{D_j}{4M_E}v_j^2s(f^2+k^2).
\end{aligned}
\tag{33}
\]
Every displayed quotient of D_j by a mass is a product of the
other four mass polynomials. At vertex 1 the factor c^2 clears
sec(alpha) and tan(alpha); the constants at vertex 3 are
rational by (23). Thus (33) defines rational polynomials with
no polynomial inversion. It gives exactly
\[
                       D_jv_j^2\widehat N_j=A_j+B_jc.
\tag{34}
\]

Use
\[
 C_6=1-\frac{s^2}{2}-\frac{s^4}{8}-\frac{s^6}{16},
 \qquad C_6-\frac{s^8}{20}\le c\le C_6
 \quad(0\le s\le27/100).
\tag{35}
\]
The positive-squaring proof is the one in Section 6 of the
large-transverse DE-alignment note. Define the one-sided
coefficient upper bound
\[
 \mathsf U(P;l,h)=\widetilde p_0+
      \sum_{i\ge1}\max\{\widetilde p_i,0\}(h-l)^i,
 \quad P(l+x)=\sum_i\widetilde p_i x^i.
\tag{36}
\]
Direct expansion of (33) gives, for every j,
\[
 \mathsf U(B_j;1499/100000,7/50)<3/50,
 \qquad
 \mathsf U(B_j;7/50,27/100)<1/20.
\tag{37}
\]
For clarity, all four upper bounds in the first family are
less than .053, and all four in the second are less than .044.
These are coefficient sums of the explicitly defined rational
polynomials, not estimates of sampled values.

Let M=3/50 in the first family and M=1/20 in the second, and put
\[
                     P_j=A_j+B_jC_6-Ms^8/20.
\tag{38}
\]
Equations (35)--(37) imply `A_j+B_jc>=P_j`, including when
B_j is negative. The polynomial degree is at most 24 for
j=0,2,3, and at most 26 for j=1.

## 7. Whole-interval positivity, with exact rational reserves

All the following comparisons are direct applications of the
finite coefficient formulas (19)--(20) to (33), (38).
They supply a short reproducible arithmetic specification for
the eight polynomials.

In the first family, for j=0,2,3,
\[
              \mathsf L(P_j'';m_0,r_0^{\rm int})>1/200.
\tag{39}
\]
The three left sides exceed .005711, .005673, and .006110,
respectively. At the respective rational pivots
\[
                 s_0=47/400,\quad s_2=233/2000,
                 \quad s_3=67/500,
\]
one has
\[
 P_j(s_j)>1/200000,
 \qquad |P_j'(s_j)|<1/100000.
\tag{40}
\]
Their values exceed .0000052755, .0000061699, and .0000069451,
and their derivative absolute values are less than .000007978,
.000009156, and .000009724. Consequently the quadratic lower
Taylor estimate, completed as one square, gives on the entire
first interval
\[
 P_j(s)>
 \frac1{200000}-\frac{(1/100000)^2}{2/200}
 =\frac{499}{100000000}>0
 \quad(j=0,2,3).
\tag{41}
\]
The remaining first-family polynomial has the direct bound
\[
                \mathsf L(P_1;m_0,r_0^{\rm int})>1/40000;
\tag{42}
\]
its left side exceeds .000028847.

For the second family, the corresponding three polynomials obey
\[
 \mathsf L(P_j';m_1,r_1^{\rm int})>-1/250000,
 \qquad P_j(7/50)>3/500000
 \quad(j=0,2,3).
\tag{43}
\]
The derivative lower bounds exceed .00009244, .00009638,
and -.000003553, respectively. The endpoint values exceed
.0000065716, .0000075809, and .0000075021. Integrating the
uniform derivative lower bound across an interval of length
13/100 yields
\[
 P_j(s)>\frac3{500000}-\frac1{250000}\frac{13}{100}
       =\frac{137}{25000000}>0.
\tag{44}
\]
Finally,
\[
                   \mathsf L(P_1;m_1,r_1^{\rm int})>1/100000;
\tag{45}
\]
the left side exceeds .000017139.
All finer terminating-decimal comparisons just displayed have
been rounded in their stated lower or upper directions.

Equations (39)--(45) prove all eight polynomials positive on
their full intervals. The comparisons involve ordinary rational
polynomial expansion, differentiation, translation and coefficient
sums. In particular none is a hypothesis about a numerical
minimum between test points.

## 8. Contradiction and the remaining local task

By (29)--(38) and the positivity just proved,
\[
                  N(V_j)\ge\widehat N_j
                    =\frac{A_j+B_jc}{D_jv_j^2}>0
                    \quad(j=0,1,2,3).
\]
The common-weight concavity comparison (15) therefore makes
N(t,u,e)>0 throughout the hypothesized truncated simplex.
This contradicts (10), and proves t+e<3/200.

The proof retained the five shared circle inequalities and the
same actual A transverse lower bound throughout. A later sharp
local terminal must justify its own hypotheses for (2)--(3), or
construct the omitted intermediate centers with the stated core
and circle bounds. Such applicability is not silently supplied
by this capture theorem. No Lean compilation or CI result is
used here.
