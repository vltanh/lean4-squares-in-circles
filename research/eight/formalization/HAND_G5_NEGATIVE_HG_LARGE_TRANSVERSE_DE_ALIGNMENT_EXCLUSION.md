# The large-transverse negative HG branch with DE aligned is excluded

## 1. The complete conditional statement

Set
\[
 Q=\frac{1957767069}{500000000},\qquad
 K=\frac{13}{12},\qquad
 W(z)=\frac{1+\cos z+\sin z}{2}.
\tag{1}
\]
Suppose H, A, B and D have nonnegative sorted own-frame
magnitudes and satisfy their actual circle inequalities
\[
 a_i\ge b_i\ge0\quad(i\ne E),\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{2}
\]
For E allow a signed transverse variable:
\[
 b_E\in\mathbb R,\qquad a_E\ge|b_E|,\qquad
 (a_E+1/2)^2+(|b_E|+1/2)^2\le q.
\tag{2E}
\]
Thus the theorem covers either sign of E. In the original normal
sign convention E has signed own-frame coordinate `y_E=-b_E`,
so its initially nonpositive sign corresponds to `b_E>=0`.
Let
\[
 t,u,e\ge0,\qquad \alpha=t+u+e\le\frac{27}{100}.
\tag{3}
\]
The following necessary system is impossible:
\[
\begin{aligned}
 (\sec e)b_H+a_A\cos t-b_A\sin t
 &\ge W(t)+\frac12+\frac12\sec e+K\tan e,\\
 b_A+b_B&\ge1,\qquad b_A\ge\frac12,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 a_D+b_E&\ge1,\\
 a_H+a_E\sin\alpha-b_E\cos\alpha&\ge W(\alpha).
\end{aligned}
\tag{4}
\]

In the original hard-owner chain, e is the negative HG0 error,
t is the remaining nonnegative GA0 tilt, u is the nonnegative
opposite BT2 tilt, and `delta=0` is DE alignment. The first line
is obtained by adding the **same original** HG0 inequality,
multiplied by `sec(e)`, to GA0, and using the already established
true core bound `a_G>=7/12`. The aligned TD path gives the third
line. Thus the statement applies before any choice of t, u or e;
it is not restricted to an angular endpoint.

The hypotheses (3), including the small total span, are supplied
by the shared-chain argument in
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md` in the
negative branch under discussion. This note proves exactly the
DE-aligned boundary exclusion (4). It does not assert that every
negative chain reaches DE alignment.

All terminating decimals below denote the displayed exact
rationals. The proof uses whole-interval derivative inequalities
and ordinary polynomial coefficient sums. No sampled angle or
state cover is a premise.

## 2. Keep one common stress throughout the angular simplex

Write
\[
 s=\sin\alpha,\quad c=\cos\alpha,\quad
 R=\sqrt Q,\quad \eta=\frac1{400},\quad k=\frac{307}{1000}.
\tag{5}
\]
At a fixed alpha choose positive weights a, beta and epsilon,
and put
\[
 d=\epsilon c+ks.
\tag{6}
\]
Multiply the first, AB, opposite-path, DE and EH inequalities in
(4) by `1,a,beta,d,epsilon`, respectively. Add also
`eta*b_A>=eta/2`. The five resulting forces are
\[
\begin{array}{c|cc}
 &F_x&F_y\\ \hline
 A&\cos t&a+\eta-\sin t\\
 B&\beta\cos u&a-\beta\sin u\\
 D&d&\beta\\
 H&\epsilon&\sec e\\
 E&\epsilon s&ks.
\end{array}
\tag{7}
\]
The demand, the weighted sum of the right sides, is
\[
 \mathcal D=W(t)+\frac12+\frac12\sec e+K\tan e
 +a+\frac\eta2+\beta(1+W(u))+d+\epsilon W(\alpha).
\tag{8}
\]

The same circle (2) at each of A, B, D and H gives
\[
 F_xa_i+F_yb_i
 \le R\sqrt{F_x^2+F_y^2}-\frac{F_x+F_y}{2}.
\tag{9}
\]
For E, its force in (7) has `F_y=ks>=0`. Therefore
`F_x*a_E+F_y*b_E<=F_x*a_E+F_y*|b_E|`, and (2E) gives the
identical upper bound (9). This is the only place that E's
transverse sign enters the stress, so all subsequent formulas
hold for the full signed domain (2E).
Consequently any feasible system (4) has
\[
 N(t,u,e):=\mathcal D-
 \sum_{i\in\{A,B,D,H,E\}}
 \left(R\lVert F_i\rVert-\frac{F_{ix}+F_{iy}}2\right)\le0.
\tag{10}
\]
There is one force for each actual center, after all its incident
inequalities have been collected.

The explicit weights used below satisfy throughout their stated
intervals
\[
 .58<a<.69,\qquad .99<\beta<1.03,\qquad .93<\epsilon<1.17.
\tag{11}
\]
At fixed alpha they are held fixed while t, u and e vary.

## 3. The entire angular simplex reduces to three intrinsic vertices

Define
\[
 g_p(z)=\cos z-R\sqrt{1+p^2-2p\sin z},
\qquad
 f_\epsilon(z)=\sec z+K\tan z
                     -R\sqrt{\epsilon^2+\sec^2z}.
\tag{12}
\]
After the cancellations in (7)--(8), all the angle-dependent
terms of (10) are exactly
\[
 g_{a+\eta}(t)+\beta g_{a/\beta}(u)+f_\epsilon(e).
\tag{13}
\]
The omitted term depends on alpha and the fixed weights only.

Here `0<a+eta<18/25` and `0<a/beta<18/25`. For
`0<=z<=alpha` one has
\[
 \sin z\le\frac{27}{100},\qquad
 \cos z\ge\frac{24}{25},\qquad
 \tan z\le\frac27,\qquad \sec z\le\frac{25}{24}.
\tag{14}
\]
For `x=sin(z)`, direct differentiation gives
\[
 g_p''(z)=-\cos z+R T_p(x),\qquad
 T_p(x)=\frac{p(p-x)(1-px)}{(1+p^2-2px)^{3/2}}.
\tag{15}
\]
Furthermore
\[
 T_p'(x)=
 -\frac{p[1-p^2+p^4-p(1+p^2)x+p^2x^2]}
        {(1+p^2-2px)^{5/2}}<0.
\tag{16}
\]
The bracket is at least
\[
 \frac34-\frac{18}{25}
       \left(1+\left(\frac{18}{25}\right)^2\right)
       \frac{27}{100}
 =\frac{710661}{1562500}>0.
\]
Thus `T_p(x)<=T_p(0)`. The function
`p^2/(1+p^2)^(3/2)` increases on `0<=p<=18/25`, and positive
squaring, even with the larger ceiling `9789/2500`, gives
\[
 R\frac{(18/25)^2}{[1+(18/25)^2]^{3/2}}<\frac{14}{25}.
\]
Equations (14)--(16) prove
\[
                         g_p''(z)<-\frac25.
\tag{17}
\]

For the last term in (13), put `x=sec(z)` and
`n=sqrt(epsilon^2+x^2)`. Then
\[
 n''=\frac{x}{n}x''+\frac{\epsilon^2(x')^2}{n^3}
      \ge\frac{x}{n}x'',
\qquad \frac{x}{n}>\frac{50}{77}.
\]
Since `R>989/500`, `x''>=1`, and (14) holds,
\[
 f_\epsilon''(z)
 \le-\frac{219}{770}
       +2\frac{13}{12}\left(\frac{25}{24}\right)^2\frac27
 =\frac{257659}{665280}<\frac{39}{100}.
\tag{18}
\]

First fix e. The function of t in (13), with
`u=alpha-e-t`, is strictly concave by (17), so its minimum is at
t zero or u zero. On either of those endpoint intervals, the
second derivative with respect to e is at most
\[
 -\frac25+\frac{39}{100}<0
 \quad\hbox{or}\quad
 -\frac25\beta+\frac{39}{100}<0,
\]
using `beta>99/100`. A second endpoint comparison therefore gives
\[
 N(t,u,e)\ge
 \min\{N(\alpha,0,0),N(0,\alpha,0),N(0,0,\alpha)\}.
\tag{19}
\]
These are the three vertices of the original continuous angular
simplex. The stress weights in (19) are identical at all three
vertices. No transfer of endpoint-specific weights has been made.

## 4. Explicit continuous weight formulas

The following two polynomial formulas cover `0<=s<=27/100`:
\[
\begin{array}{c|l}
 0\le s\le4/25&\\ \hline
 a&.5882364+.4934062s+.1427643s^2-.5188337s^3\\
 \beta&1.0080571+.1130618s-.9739332s^2+2.6675520s^3\\
 \epsilon&1.1668343-.9213978s+.0709186s^2+1.1644648s^3
\end{array}
\tag{20}
\]
and
\[
\begin{array}{c|l}
 4/25\le s\le27/100&\\ \hline
 a&.6633158-.0399489s+.4780194s^2-.1700769s^3\\
 \beta&.9663412+.3388059s+.2953896s^2-4.0769811s^3\\
 \epsilon&1.1418718-.8017237s+.8506823s^2-2.3797095s^3.
\end{array}
\tag{21}
\]
Either formula is allowed at the common endpoint. Each whole
interval is treated by a single polynomial derivative estimate
below. In particular the formulas are not a list of angle states.

For clarity, the elementary coefficient estimate used to verify
(11) and the later bounds is as follows. If
`P(m+x)=sum_j p_j x^j`, define
\[
 \mathsf L(P;m,r)=p_0-
   \sum_{j\ {
m odd}}|p_j|r^j+
   \sum_{j\ge2\ {
m even}}\min\{p_j,0\}r^j.
\tag{22}
\]
Then `P(s)>=L(P;m,r)` on `|s-m|<=r`; also
`P(s)<=-L(-P;m,r)`. Coefficients in the translated polynomial are
given directly by
\[
 p_j=\sum_{i\ge j}\binom ij P_i m^{i-j},
 \quad\hbox{where }P(s)=\sum_i P_i s^i.
\tag{23}
\]
Use `(m,r)=(2/25,2/25)` for (20) and
`(m,r)=(43/200,11/200)` for (21). Applying (22) to the displayed
cubics proves the rational bounds (11).

## 5. Endpoint circle estimates are now allowed to use different masses

For each positive m, the elementary inequality
\[
 R\lVert F\rVert\le mQ+\frac{\lVert F\rVert^2}{4m}
\tag{24}
\]
follows by squaring `sqrt(m)*R-|F|/(2sqrt(m))`.
Define
\[
 T(F;m)=mQ+\frac{\lVert F\rVert^2}{4m}
                        -\frac{F_x+F_y}{2}.
\tag{25}
\]
Only after the exact-norm reduction (19), lower-bound its three
endpoint scalars by
\[
 N_j=\mathcal D_j-\sum_iT(F_{ij};m_{ij}),
 \quad j=0,1,2,
\tag{26}
\]
where j denotes the t-only, u-only, or e-only vertex, respectively.
Then the exact endpoint scalar in (19) is at least `N_j`.

All masses below are cubic polynomials in s; a tuple denotes the
coefficients of `1,s,s^2,s^3`. Use `A_rot` for A at j zero and
`A_fixed` for A at the other vertices. Use `B_rot` for B at j one
and `B_fixed` otherwise. Use `H_sec` for H at j two and
`H_fixed` otherwise. D has its common displayed mass. The E mass
is `s*M_E(s)`.

For `0<=s<=4/25` use
\[
\begin{array}{c|rrrr}
 A_{\rm rot}&.29347657&-.06503767&-.07091341&-.08897024\\
 A_{\rm fixed}&.29348151&.06325141&.04054196&-.07689433\\
 B_{\rm fixed}&.29492831&.08686475&-.16973016&.49966604\\
 B_{\rm rot}&.29493219&-.04166049&-.27993159&.48192325\\
 D&.38962916&-.09878934&-.24001063&.73320919\\
 H_{\rm fixed}&.38830893&-.17713048&.04857227&.19769415\\
 H_{\rm sec}&.38830222&-.17682548&.12596229&.26750787\\
 M_E&.30487404&-.22523113&.02419395&.28112053
\end{array}
\tag{27}
\]
For `4/25<=s<=27/100` use
\[
\begin{array}{c|rrrr}
 A_{\rm rot}&.30357263&-.14570632&.04070833&-.10732173\\
 A_{\rm fixed}&.30355109&-.00526874&.06446582&-.01674049\\
 B_{\rm fixed}&.29572699&.07226100&.09419652&-.82051441\\
 B_{\rm rot}&.29526357&-.05762896&-.00160373&-.75838043\\
 D&.37791971&-.03967690&.13681627&-1.11961265\\
 H_{\rm fixed}&.38317300&-.14574793&.14011328&-.36291958\\
 H_{\rm sec}&.38277232&-.13854359&.17734792&-.21542959\\
 M_E&.29868446&-.19396183&.20127830&-.55787176.
\end{array}
\tag{28}
\]

Estimate (22) on the respective whole intervals gives
\[
 m_A,m_B>.26,\qquad m_D>.34,\qquad m_H>.33,
 \qquad M_E>.23.
\tag{29}
\]
For positive s all masses are thus positive. At s zero, the E
force and its mass vanish; simply omit that zero contribution in
(26). The expression extends continuously because
\[
 \frac{\lVert F_E\rVert^2}{m_E}
 =s\frac{\epsilon^2+k^2}{M_E}.
\tag{30}
\]

## 6. Exact polynomial definitions for all endpoint estimates

Here are compact polynomial definitions so that the inequalities
below are reproducible from the rational coefficients in
(20)--(21) and (27)--(28), without any fitted or numerical input.
All operations in this section are in the ring
`Q[s,c]/(c^2+s^2-1)`.

For each endpoint let
\[
 D_j=4m_A m_B m_D m_H M_E>0,\qquad
 v_j=\begin{cases}1&j=0,1,\\c&j=2.\end{cases}
\tag{31}
\]
Evaluate the demand (8) and the forces (7) at the indicated
endpoint. Then, writing `J={A,B,D,H}` and
`\widehat F_i=v_j F_i`, define
\[
\begin{aligned}
 A_j(s)+B_j(s)c={}&
 D_jv_j^2\left[
   \mathcal D_j-Q\left(\sum_{i\in J}m_i+sM_E\right)
       +\frac12\sum_{i\in J}(F_{ix}+F_{iy})
       +\frac{s}{2}(\epsilon+k)\right]\\
 &-\sum_{i\in J}
        \frac{D_j}{4m_i}\lVert\widehat F_i\rVert^2
   -\frac{D_j}{4M_E}v_j^2s(\epsilon^2+k^2).
\end{aligned}
\tag{32}
\]
Although the e-only endpoint contains secant and tangent,
multiplication by `v_2^2=c^2` clears their denominators. All the
quotients `D_j/(4m_i)` and `D_j/(4M_E)` are products of the other
four displayed mass polynomials. Thus (32) defines ordinary
rational polynomials A and B by multiplication and the relation
`c^2=1-s^2`. In particular it is an explicit algebraic definition,
with no inversion of a polynomial needed.

By construction,
\[
                  D_jv_j^2N_j=A_j+B_jc.
\tag{33}
\]
The degree of `A_j+B_j C_6` below is at most 24 for j zero or one
and at most 26 for j two.

Set
\[
 C_6=1-\frac{s^2}{2}-\frac{s^4}{8}-\frac{s^6}{16}.
\tag{34}
\]
On the full interval `0<=s<=27/100`,
\[
                  C_6-\frac{s^8}{20}\le c\le C_6.
\tag{35}
\]
For the upper comparison, subtract `1-s^2` from `C_6^2`; the
result is `5s^8/64+s^10/64+s^12/256>=0`. For the lower comparison,
the same subtraction after replacing `C_6` by `C_6-s^8/20`, and
division by `s^8`, gives
\[
 \frac5{64}+\frac{s^2}{64}+\frac{s^4}{256}
       -\frac{C_6}{10}+\frac{s^8}{400}<0.
\]
Use `C_6>24/25`, `s<=27/100` for the strict inequality. Both
quantities being compared with c are positive; s zero follows
directly.

For a polynomial P on `[l,h]` define the one-sided coefficient
sum
\[
 \mathsf U(P;l,h)=\widetilde p_0+
       \sum_{i\ge1}\max\{\widetilde p_i,0\}(h-l)^i,
 \quad P(l+x)=\sum_i\widetilde p_i x^i.
\tag{36}
\]
It bounds P above on the entire interval. Direct expansion of
(32), using (23) for translation, gives
\[
 \mathsf U(B_j;0,4/25)<\frac3{50},\qquad
 \mathsf U(B_j;4/25,27/100)<\frac9{200}
 \quad(j=0,1,2).
\tag{37}
\]
For example the three lower-interval bounds are respectively
less than `.055320,.055209,.054999`; the three upper-interval
bounds are respectively less than `.037352,.037529,.042363`.
These comparisons follow from the finite rational sums (36),
with coefficients fixed by (32).

Let `M=3/50` in the first interval and `M=9/200` in the second,
and define the exact polynomial
\[
                     P_j=A_j+B_jC_6-M\frac{s^8}{20}.
\tag{38}
\]
Equations (35)--(37) give `A_j+B_jc>=P_j`. This remains true
when B is negative: then the upper bound `c<=C_6` already gives
`B_jc>=B_jC_6`, and the last term in (38) only weakens it.

## 7. Whole-interval positivity of the six explicit polynomials

The following are rational coefficient-sum inequalities, with
`L` as in (22) and the polynomial defined by (32) and (38).
On the first interval they are
\[
\begin{aligned}
 \mathsf L(P_0'';2/25,2/25)&>\frac1{250},\\
 \mathsf L(P_1'';2/25,2/25)&>\frac1{250},\\
 -\mathsf L(-P_2'';2/25,2/25)&<-\frac1{400}.
\end{aligned}
\tag{39}
\]
The first two left sides exceed `.004866` and `.004955`;
the last is below `-.002676`. On the second interval they are
\[
 \mathsf L(P_j';43/200,11/200)>\frac1{12500}
 \quad(j=0,1,2).
\tag{40}
\]
Their left sides exceed `.00008384,.00016689,.00018022`,
respectively. The displayed bounds have been rounded in the
indicated inequality directions. They can be verified simply by
substituting (20)--(21) and (27)--(28) in (32), reducing powers of
c, and applying the finite sums (22)--(23); thus (39)--(40) are
whole-polynomial arithmetic comparisons, not values on a mesh.

At `s_0=123/1000`, the first two lower-interval polynomials also
satisfy
\[
 P_j(s_0)>\frac1{2500000},\qquad
 |P_j'(s_0)|<\frac1{1000000},\quad j=0,1.
\tag{41}
\]
For example their values exceed `.0000004664` and `.0000004654`;
their derivative absolute values are less than `.000000193` and
`.000000626`. These are again direct rational substitutions.
By (39), for any s in that entire interval,
\[
\begin{aligned}
 P_j(s)&\ge P_j(s_0)+P_j'(s_0)(s-s_0)
                     +\frac1{500}(s-s_0)^2\\
 &>\frac1{2500000}
       -\frac{(1/1000000)^2}{2/250}
 =\frac{3199}{8000000000}>0.
\end{aligned}
\tag{42}
\]

The remaining lower-interval polynomial has
\[
 P_2(0)>\frac1{250000},\qquad
 P_2(4/25)>\frac1{250000}.
\tag{43}
\]
The second value exceeds `.0000042558`. Its strict concavity
from (39) therefore makes it positive throughout the interval.

Finally, each upper-interval polynomial satisfies
\[
                         P_j(4/25)>\frac1{250000}.
\tag{44}
\]
The three left sides exceed `.0000049856,.0000046613,.0000049916`.
Their positive derivative from (40) proves positivity over the
whole second interval. This proves, in all cases,
\[
              A_j+B_jc\ge P_j>0,
              \qquad N_j>0.
\tag{45}
\]

## 8. Contradiction and its precise use in the negative branch

Equation (24) makes each exact endpoint scalar in (19) at least
the corresponding positive number `N_j`. Equation (19) then
gives `N(t,u,e)>0` at every point of the angular simplex (3),
contradicting the necessary inequality (10). This proves the
conditional theorem (4), including all equality and zero-angle
boundaries.

In the remaining large-transverse negative branch, the same
shared-chain estimates also give `a_H<1`: since `b_A>=1/2`,
\[
 a_A\le\sqrt{Q-1}-\frac12,
 \quad b_H\ge2-a_A\ge\frac52-\sqrt{Q-1},
\]
and hence
\[
 a_H\le\sqrt{6\sqrt{Q-1}-8}-\frac12<1.
\tag{46}
\]
For the last strict comparison it is enough to use
`Q<2257/576`, equivalent to `sqrt(Q-1)<41/24`.
When `b_E>=0`, `epsilon=0` in the original E mixed-angle split
is therefore impossible: its EH1 inequality would give
`a_H>=1+b_E`. This last implication requires `b_E>=0`; it is
not asserted after a reflection that makes the variable b_E
negative.

For the original nonpositive-E sign and a large A tangent,
together with the E-boundary minimization already proved in
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`, the new
exclusion (4) leaves only the **E transverse-zero boundary** in
this large-transverse negative HG branch. The reflected theorem
also excludes the original `epsilon=0` boundary when B is the
large tangent and the negative error is on the D side, because
the stress theorem itself allows either E sign. It does not
exclude the other reflected boundary, which has `epsilon=0`
and `b_E<0` in the reflected variables. No assertion about that
remaining boundary, global owner selection, or the unrestricted
n=8 theorem is made here.
