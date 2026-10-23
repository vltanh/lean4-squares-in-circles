# Two complete scalar certificates for joint negatives and positive BT3

## 1. The exact endpoint functions

All terminating decimals in this note are exact rational numbers.
Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=.7,\quad K=13/12,
 \quad c_0=R/\sqrt2-1/2.
\tag{1}
\]
For positive coefficients k,c and a tilt η, define
\[
 f(z)=\cos z+\eta\sin z,\qquad m=c/f(z),\qquad
 \sigma=R\sqrt{1+\eta^2}-(1+\eta)/2,
\]
\[
 C_z=1+2\cos z+(.5+1.5\eta-\sigma)\sin z,
\qquad
 D(c)=\begin{cases}(1+c)/\sqrt2,&c\ge1,\\
                    \sqrt{1+c^2},&c\le1.
       \end{cases}
\tag{2}
\]
The zero-negative-angle positive-BT baseline is
\[
 B_0(z)=2k+6+mC_z
 -R\{2\sqrt{1+k^2}+\sqrt{1+m^2}+D(c)\}.
\tag{3}
\]
This is exactly the weighted demand minus support for the
original positive BT3 and arbitrary TD0 force identity,
with equal unit A/E scales and c=mf. The D term retains the
actual sorted support when c\(\ge1\). For c\(\le1\), the
full-circle optimizer lies on the sorted arc under the ranges below.

Let
\[
 F_k(t)=\sec t+K\tan t-R\sqrt{\sec^2t+k^2}
                         -1+R\sqrt{1+k^2},
\]
\[
 V_{k,1}(t)=\cos t-1
 -R\{\sqrt{1+k^2-2k\sin t}-\sqrt{1+k^2}\}.
\tag{4}
\]
We prove, on the entire interval \(0\le z\le h\),
\[
                \boxed{B_0(z)+V_{k,1}(z)>0,
                       \qquad B_0(z)+F_k(z)>0.}
\tag{5}
\]
These are the two scalar hypotheses of
[the joint-negative positive-BT theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_BT3_EXCLUSION.md).

## 2. Three continuous coefficient families

On \(0\le z\le .15\), choose
\[
 k=.65,\qquad \eta=.31865,\qquad c=1.38-2.6z+2.8z^2.
\tag{6}
\]
For the two remaining intervals use
\[
 \begin{split}
 k(z)={}&.65433234-.06770392z+.39062724z^2-.29937498z^3\\
       &+.35999242z^4-.29068717z^5+.14649232z^6,\\
 \eta(z)={}&.24865+.28z.
 \end{split}
\tag{7}
\]
For \(.15\le z\le .25\), put
\[
 c=1-1.22(z-.25)+1.72(z-.25)^2.
\tag{8}
\]
For \(.25\le z\le h\), put
\[
 c=1-.67(z-.25)+.48(z-.25)^2.
\tag{9}
\]
In every case m is the exact positive function c/f from (2).
The middle and high families agree at the actual D support
transition z=.25, where c=1. At z=.15 either stress is valid;
the two choices need not coincide.

The following ranges hold throughout the respective intervals:
\[
 .65\le k\le .751,\qquad k\le m\le c,\qquad .7<c<1.4;
\tag{10}
\]
\[
 c\ge1\Longrightarrow z\le.25<.3\text{ and }k<.6692,
 \qquad z\ge.15\Longrightarrow c\le1.1392<1.2.
\tag{11}
\]
Here is a direct range proof. The exact polynomial (7) is
increasing on [.15,h], as proved by the centered coefficient
bound (7) of
[the positive-TD scalar companion](HAND_G3_JOINT_NEGATIVE_A_CORE_E_SCALAR_CERTIFICATES.md).
Its endpoints lie strictly between .65 and .751, and
\(k(.25)<.659<.6692\).

The low c decreases from 1.38 to 1.053. The middle c decreases
from 1.1392 to 1. The high c decreases from 1 to .7957.
For low f, concavity and its endpoint values give f\(\ge1\),
while \(f\le\sqrt{1+.31865^2}<1.05\). Thus its m exceeds
\(1.053/1.05>1>k\).

On [.15,h], f has the exact second derivative
\[
                  f''=-.44\cos z-\eta(z)\sin z<0.
\tag{12}
\]
Alternating Taylor bounds at the endpoints give
\(f(.15)>1.03\) and \(f(h)>1.05\), so f\(>1\).
Also
\[
 f\le\sqrt{1+.44465^2}<1.095.
\tag{13}
\]
On the middle interval c\(\ge1\), whence
\(m>1/1.095>.751\ge k\).

On the high interval, (12) and the exact endpoint estimate
\[
 f'(h)=-.72\sin h+.44465\cos h>-.125
\tag{14}
\]
give f'\(>-.125\). Since c'\(\le-.238\), k'\(>0\), and
f\(>0\), the function c−kf has derivative less than
\[
                         -.238+.751(.125)<0.
\tag{15}
\]
At its right endpoint, upper Taylor bounds give
\[
 .7957-.751\{C_{12}(h)+.44465 S_9(h)\}>.0061.
\tag{16}
\]
Thus c−kf is positive throughout this interval, proving m\(>k\).
Finally f\(\ge1\) gives m\(\le c\). This proves (10)--(11)
without sampling a coefficient range.

## 3. Explicit rational endpoint polynomials

Use
\[
 R_+=1.978787508>R,\qquad d_+=.707106781187>1/\sqrt2.
\tag{17}
\]
Their directions follow by positive squaring. Write
\[
 S(z)=\sum_{j=0}^{7}\frac{(-1)^jz^{2j+1}}{(2j+1)!},\qquad
 C(z)=\sum_{j=0}^{8}\frac{(-1)^jz^{2j}}{(2j)!},
\]
\[
 f_*=C+\eta S,\qquad T_*=1+2C+(1+2\eta)S.
\tag{18}
\]
The exact sine and cosine errors on [0,h] are smaller than
\(7\cdot10^{-18}\) and \(3\cdot10^{-19}\), respectively.

Define squared-norm polynomials and positive mass polynomials:
\[
 \begin{array}{lll}
 v_0=1+k^2,&\alpha_0=(91+60k)/109,\\
 v_B=f_*^2+c^2,&\alpha_B=(20f_*+21c)/29,\\
 v_\eta=1+\eta^2,&\alpha_\eta=(40+13\eta)/42,\\
 v_V=1+k^2-2kS,&\alpha_V=\{36(k-S)+77C\}/85,\\
 v_F=1+k^2C^2,&\alpha_F=(91+60kC)/109,\\
 v_D=1+c^2,&\alpha_D=(21+20c)/29.
 \end{array}
\tag{19}
\]
Every mass exceeds 2/3 both for these Taylor polynomials and
for actual sine and cosine. For example k−S\(>.65-.645>0\),
C\(>.764\), and f\(_*\ge1\) up to an error below
\(10^{-16}\); hence the two potentially smallest masses,
\(\alpha_V\) and \(\alpha_B\), exceed respectively
\(77(.764)/85\) and \(20/29-10^{-15}\). All other cases
follow directly from their positive coefficients in (19).

For the first endpoint in (5), multiplied by f, put
\[
 A_1=f_*(2k+5+C)+cT_*.
\]
Use the four triples (squared norm, mass, weight)
\[
 (v_0,\alpha_0,f_*),\quad (v_B,\alpha_B,1),\quad
 (v_V,\alpha_V,f_*),\quad(v_\eta,\alpha_\eta,cS).
\tag{20}
\]
For the second endpoint, multiplied by f\(\cos z>0\), put
\[
 A_2=\{f_*(2k+5)+cT_*\}C+f_*(1+KS).
\]
Use
\[
 (v_0,\alpha_0,f_*C),\quad(v_B,\alpha_B,C),\quad
 (v_F,\alpha_F,f_*),\quad(v_\eta,\alpha_\eta,cSC).
\tag{21}
\]
On the first two coefficient intervals, D is diagonal.
Subtract \(R_+d_+(1+c)f_*\) from A\(_1\), or
\(R_+d_+(1+c)f_*C\) from A\(_2\).
On the high interval append the triple
\((v_D,\alpha_D,f_*)\) to (20), or
\((v_D,\alpha_D,f_*C)\) to (21).

For the resulting A\(_j\) and list of triples, define
\[
 P_j=2A_j\prod_i\alpha_i
 -R_+\sum_i w_i(v_i+\alpha_i^2)\prod_{\ell\ne i}\alpha_\ell.
\tag{22}
\]
These are completely specified polynomials over the rationals.
The masses have no approximation premise: the exact identity
\[
 \frac{v+\alpha^2}{2\alpha}-\sqrt v
                 =\frac{(\sqrt v-\alpha)^2}{2\alpha}\ge0
\tag{23}
\]
holds for every positive α and every v\(\ge0\).

To verify the force algebra, replace S,C in (18)--(22) by
sine and cosine. The identity
\[
 .5+1.5\eta-\sigma=1+2\eta-R\sqrt{1+\eta^2}
\]
accounts for the fourth triple in each list. Multiplying
(3) by f clears m=c/f. Adding the V term cancels one copy
of \(fR\sqrt{1+k^2}\), giving (20). Adding the F term and
multiplying by cosine instead produces the norm
\(\sqrt{1+k^2\cos^2z}\), giving (21).
Thus (23), with the upper constants (17), makes
\(P_j/(2\prod_i\alpha_i)\) a lower bound for the stated
endpoint, after its positive f or f\(\cos z\) multiplier.

The Taylor substitutions change (22) by less than \(10^{-8}\).
For an explicit uniform allowance, on the line segments from
the exact sine/cosine to (18) use
\[
 |S|<.646,\quad |C|<1.001,\quad |\alpha_i|<3,
 \quad |\partial_S\alpha_i|,|\partial_C\alpha_i|<4,
\]
\[
 |v_i|<4,\quad |\partial_Sv_i|,|\partial_Cv_i|<10,
 \quad |w_i|<2,\quad |\partial_Sw_i|,|\partial_Cw_i|<3,
\]
\[
 |A_j|<20,\qquad |\partial_S A_j|,|\partial_C A_j|<30.
\]
There are at most five mass factors. Product differentiation
in (22) bounds either partial derivative by \(10^7\); the
errors after (18) are much smaller than the stated allowance.
It suffices to prove both rational polynomials positive with
a reserve exceeding \(10^{-8}\).

## 4. Compact whole-interval positivity certificates

Here is the coefficient-norm convention used below. For a
rational polynomial p on [a,b], write
\[
 p((a+b)/2+(b-a)t/2)=\sum_n u_nt^n.
\]
Expand each power in Chebyshev polynomials:
\[
 t^n=2^{1-n}\sum_{0\le j<n/2}\binom nj T_{n-2j}(t)
       +\begin{cases}2^{-n}\binom n{n/2},&n\text{ even},\\0,&n\text{ odd}.
         \end{cases}
\tag{24}
\]
If the resulting coefficients are b\(_i\), define
\[
 \mathcal C_-(p;[a,b])=b_0-\sum_{i>0}|b_i|,\qquad
 \mathcal C_+(p;[a,b])=b_0+\sum_{i>0}|b_i|.
\tag{25}
\]
The identity (24) and \(|T_i|\le1\) prove these are lower
and upper bounds on the entire interval. No subdivision or
pointwise evaluation is part of this certificate.

### Low interval

The two polynomials (22), using (6) and diagonal D, have
degrees 64 and 66. Exact rational coefficient sums give
\[
 \begin{array}{lll}
 P_1(.15)>.00296,&
 \mathcal C_+(P'_1;[0,.15])<-.335,\\
 P_2(.15)>.00482,&
 \mathcal C_+(P'_2;[0,.15])<-.317.
 \end{array}
\tag{26}
\]
Both polynomials decrease on this whole interval and are
strictly positive at their right endpoint.

### Middle interval

Use (7)--(8) and diagonal D. The degrees are 71 and 83.
Write
\[
 P_j(.235+u)=\sum_i a_{j,i}u^i,
                  \qquad |u|\le .085.
\]
This centered domain contains the entire interval [.15,.25].
The exact coefficient bounds from (18)--(22) are
\[
 \begin{array}{lll}
 a_{1,0}>.0007316,&|a_{1,1}|<.010111,&
 a_{1,2}-\displaystyle\sum_{i\ge3}|a_{1,i}|(.085)^{i-2}>1.2768,\\
 a_{2,0}>.0007964,&|a_{2,1}|<.010731,&
 a_{2,2}-\displaystyle\sum_{i\ge3}|a_{2,i}|(.085)^{i-2}>1.4244.
 \end{array}
\tag{27}
\]
One completed square for each polynomial gives
\[
 P_1>.0007316-\frac{.010111^2}{4(1.2768)}>.000711,
\]
\[
 P_2>.0007964-\frac{.010731^2}{4(1.4244)}>.000776.
\tag{28}
\]

### High interval

Use (7),(9) and full D. The degrees are 73 and 85.
At the intrinsic support transition define the exact
polynomial quotient
\[
 q_j(u)=\frac{P_j(.25+u)-P_j(.25)}u,
                         \qquad0\le u\le .45.
\tag{29}
\]
The value at zero is its polynomial continuation. Exact
rational coefficient sums give
\[
 \begin{array}{lll}
 P_1(.25)>.0012418,&\mathcal C_-(q_1;[0,.45])>.0207,\\
 P_2(.25)>.0013591,&\mathcal C_-(q_2;[0,.45])>.0158.
 \end{array}
\tag{30}
\]
Thus both polynomials are strictly above their positive
left-endpoint values throughout this interval.

All coefficient aggregates in (26)--(30) are finite rational
sums of the explicitly defined polynomials (22), with the
exact convention (24)--(25) or the displayed power-tail norm.
Their smallest reserve exceeds .0007, whereas the total
Taylor allowance is less than \(10^{-8}\). Positive masses,
f and cosine therefore give both strict inequalities (5)
over all three whole intervals, including both joins.

These six certificates supply the scalar hypotheses of the
geometric assembly. They use three continuous coefficient
formulas, one intrinsic sorted-support transition, and global
polynomial identities. No angle mesh, optimizer minimum,
coefficient-row inventory, Lean compilation or CI is a premise.
