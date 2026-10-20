# Two scalar certificates for joint negative A and core E

## 1. The two endpoint inequalities

All decimals denote exact rational numbers. Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=.7,\quad
 K=\frac{13}{12},\quad \eta=.303,\quad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2}.
\tag{1}
\]
At \(0\le z\le h\), define \(m=c(\cos z+\eta\sin z)\),
\[
 C_z=1+2\cos z+(.5+1.5\eta-\sigma)\sin z,
\]
\[
 D(c)=
 \begin{cases}(1+c)/\sqrt2,&c\ge1,\\
               \sqrt{1+c^2},&c\le1,
 \end{cases}
\]
\[
 B_0(z)=2k+6+cC_z
       -R\{2\sqrt{1+k^2}+\sqrt{1+m^2}+D(c)\}.
\tag{2}
\]
Use \(F_k\) and \(V_{p,q}\) from
[the common-gain theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_COMMON_GAIN.md).
This note proves both strict inequalities
\[
             B_0(z)+V_{k,1}(z)>0,\qquad B_0(z)+F_k(z)>0
\tag{3}
\]
on the whole interval \([0,h]\), for the following weights.

On \(0\le z\le .15\), take
\[
                  k=.65,\qquad c=1.38-2.6z+2.8z^2.
\tag{4}
\]
On \(.15\le z\le h\), take
\[
 \begin{split}
 k={}&.65433234-.06770392z+.39062724z^2-.29937498z^3\\
     &+.35999242z^4-.29068717z^5+.14649232z^6,\\
 c={}&1.151145-.9z+.55z^2.
 \end{split}
\tag{5}
\]
The branch of D changes at \(z=.19\), because the c in
(5) satisfies \(c(.19)=1\) exactly and is strictly decreasing.
Thus the proof consists of three whole closed intervals:
\([0,.15]\), \([.15,.19]\), and \([.19,h]\).

## 2. Coefficient ranges needed by the geometric reduction

For (4), c decreases from 1.38 to 1.053. On this interval
\(f(z)=\cos z+.303\sin z\) increases, and
\[
 m'=c'f+cf'\le-1.76+1.38(.303)<0.
\]
The endpoint Taylor bounds give
\[
        1.088<m\le1.38,\qquad \sec(.38)<1.078<m.
\tag{6}
\]
For (5), k is strictly increasing. One short rational
certificate is to expand \(k'(.425+u)=\sum_{j=0}^{5}d_ju^j\):
\[
 d_0-\sum_{j=1}^{5}|d_j|(.275)^j>.023.
\tag{7}
\]
Substitution at the endpoints gives
\[
             .65<k(.15)\le k(z)\le k(h)<.751.
\tag{8}
\]
Also \(.790645\le c\le1.02852\). Concavity of f and
its endpoint Taylor bounds imply \(.96<f<1.045\); the
upper bound also follows from \(1+\eta^2<1.045^2\).
Consequently
\[
     m>.96(.790645)>.751\ge k,\qquad
     m<1.045(1.02852)<1.078,
     \qquad c\ge k.
\tag{9}
\]
Both families therefore satisfy
\[
 .65\le k\le .751,\qquad k\le c<1.4,\qquad k\le m.
\tag{10}
\]
Every coefficient of a rotating outer block is at most m
in (4), and at most 1.078 in (5), once the negative-primary
entry bounds \(r<.38\), \(s_{EH}<.25\) are used.

## 3. Exact rational support polynomials

Use the strict rational upper bounds
\[
 R<R_+=1.978787508,\qquad
 \sigma<\sigma_+=1.416128429,\qquad
 1/\sqrt2<d_+=.707106781187.
\tag{11}
\]
They follow, respectively, from
\[
 R_+^2>Q,\qquad
 \left(\sigma_++\frac{1+\eta}{2}\right)^2>Q(1+\eta^2),
 \qquad 2d_+^2>1.
\tag{12}
\]
For \(v\ge0,\alpha>0\), the elementary identity
\[
 \frac{v+\alpha^2}{2\alpha}-\sqrt v
                       =\frac{(\sqrt v-\alpha)^2}{2\alpha}\ge0
\tag{13}
\]
will bound every radical.

Let S and C be the exact Taylor polynomials
\[
 S(z)=\sum_{j=0}^{7}\frac{(-1)^jz^{2j+1}}{(2j+1)!},\qquad
 C(z)=\sum_{j=0}^{8}\frac{(-1)^jz^{2j}}{(2j)!},
\]
\[
 M=c(C+\eta S),\qquad J=1+2C+(.5+1.5\eta-\sigma_+)S.
\tag{14}
\]
The following quantities are rational polynomials in z:
\[
 \begin{array}{lll}
 v_0=1+k^2,&\alpha_0=(91+60k)/109,\\
 v_B=1+M^2,&\alpha_B=(20+21M)/29,\\
 v_D=1+c^2,&\alpha_D=(21+20c)/29,\\
 v_V=1+k^2-2kS,&\alpha_V=\{36(k-S)+77C\}/85,\\
 v_F=1+k^2C^2,&\alpha_F=(91+60kC)/109.
 \end{array}
\tag{15}
\]
All \(\alpha\)'s exceed \(1/2\) on their intervals, both
with the Taylor polynomials and with actual sine and cosine.
For \(\alpha_V\), it is enough that \(k\ge.65>\sin h\)
and \(\cos h>.764\); the others are immediate.

For the first endpoint in (3), start with
\[
 H_1=2k+5+C+cJ,
\]
and use the three triples
\[
              (v_i,\alpha_i,w_i)=(v_0,\alpha_0,1),
                (v_B,\alpha_B,1),(v_V,\alpha_V,1).
\tag{16}
\]
For the second endpoint multiplied by \(\cos z>0\), start
with
\[
 H_2=(2k+5+cJ)C+1+KS,
\]
and use
\[
              (v_i,\alpha_i,w_i)=(v_0,\alpha_0,C),
                (v_B,\alpha_B,C),(v_F,\alpha_F,1).
\tag{17}
\]
On the diagonal D branch, replace \(H_1\) by
\(H_1-R_+d_+(1+c)\), and \(H_2\) by
\(H_2-R_+Cd_+(1+c)\). On the other branch append the
fourth triple \((v_D,\alpha_D,1)\) in (16), or
\((v_D,\alpha_D,C)\) in (17).

For either resulting list, define the exact polynomial
\[
 P_j=2H_j\prod_i\alpha_i
        -R_+\sum_iw_i(v_i+\alpha_i^2)\prod_{\ell\ne i}\alpha_\ell.
\tag{18}
\]
Thus (13) makes \(P_1/(2\prod\alpha_i)\) a lower bound
for the first endpoint in (3), and makes
\(P_2/(2\prod\alpha_i)\) a lower bound for the second endpoint
times cosine, when S,C are replaced by sine and cosine.
The constants in (11) only lower these bounds.

The Taylor substitutions in (18) change its value by less
than \(10^{-8}\). To check this directly, the errors in S,C
on \([0,h]\) are less than \(7\cdot10^{-18}\) and
\(3\cdot10^{-19}\). In (15)--(18), there are at most four
factors \(\alpha_i\); their magnitudes are less than 2 and
their partial derivatives in S,C are less than 3. One may use
\(|H_j|,|\partial_SH_j|,|\partial_CH_j|<20\),
\(|v_i|<4\), and \(|\partial_Sv_i|,|\partial_Cv_i|<10\).
Product differentiation bounds both partial derivatives of
(18) by \(10^6\), more than sufficient for the stated error.

It remains to prove the two polynomials (18) positive with
reserve exceeding \(10^{-8}\). The following coefficient
norm certificates cover each full interval.

## 4. The low interval

Use (4), the diagonal D branch, and write
\(P_j(.15+u)=\sum_i a_{j,i}u^i\), where \(-.15\le u\le0\).
Expansion of (14)--(18) gives
\[
 \begin{array}{lll}
 a_{1,0}>.001645,&a_{1,1}<-.126,&
 a_{1,2}-\displaystyle\sum_{i\ge3}|a_{1,i}|(.15)^{i-2}>.584,\\
 a_{2,0}>.003289,&a_{2,1}<-.100,&
 a_{2,2}-\displaystyle\sum_{i\ge3}|a_{2,i}|(.15)^{i-2}>1.234.
 \end{array}
\tag{19}
\]
The sums terminate at degrees 52 and 68 respectively.
It follows on the whole interval that
\[
 \begin{split}
 P_1(.15+u)&>.001645-.126u+.584u^2\ge .001645,\\
 P_2(.15+u)&>.003289-.100u+1.234u^2\ge .003289.
 \end{split}
\tag{20}
\]

## 5. The interval ending at the sorted-D transition

Use (5), the diagonal D branch, and write
\(P_j(.185+u)=\sum_i a_{j,i}u^i\). The actual interval
\(.15\le z\le .19\) has \(|u|\le .035\). Rational expansion
gives
\[
 \begin{array}{lll}
 a_{1,0}>.00004709,&|a_{1,1}|<.000799,&
 a_{1,2}-\displaystyle\sum_{i\ge3}|a_{1,i}|(.035)^{i-2}>.6002,\\
 a_{2,0}>.00005068,&|a_{2,1}|<.000842,&
 a_{2,2}-\displaystyle\sum_{i\ge3}|a_{2,i}|(.035)^{i-2}>.65.
 \end{array}
\tag{21}
\]
The degrees are 58 and 80. Completing the two squares gives
\[
 P_1>.00004709-\frac{.000799^2}{4(.6002)}>.0000468,
 \qquad
 P_2>.00005068-\frac{.000842^2}{4(.65)}>.0000504.
\tag{22}
\]

## 6. The full-D interval

Use (5), the full-circle D branch, and expand at the intrinsic
transition: \(P_j(.19+u)=\sum_i a_{j,i}u^i\), with
\(0\le u\le .51\). For the first polynomial, of degree 60,
the exact coefficient bounds are
\[
 \begin{gathered}
 a_{1,0}>.000082,\quad a_{1,1}>.007554,\quad
 a_{1,2}>-.02507,\quad a_{1,3}>1.17946,\quad
 a_{1,4}>-2.4597,\\
 a_{1,5}+\sum_{\substack{i>5\\a_{1,i}<0}}
                               a_{1,i}(.51)^{i-5}>.91789.
 \end{gathered}
\tag{23}
\]
The quadratic \(1.17946-2.4597u+.91789u^2\) decreases
on this interval and is greater than .1637 at \(u=.51\).
It follows that
\[
 P_1>.000082+u\{.007554-.02507u+.1637u^2\}>.000082,
\tag{24}
\]
where the final quadratic is positive because
\(.02507^2<4(.007554)(.1637)\).

For the second polynomial, of degree 82, the bounds are
\[
 \begin{gathered}
 a_{2,0}>.0000883,\quad a_{2,1}>.008137,\quad
 a_{2,2}>-.02479,\\
 a_{2,3}+\sum_{\substack{i>3\\a_{2,i}<0}}
                               a_{2,i}(.51)^{i-3}>.0367.
 \end{gathered}
\tag{25}
\]
Therefore
\[
 P_2>.0000883+u\{.008137-.02479u+.0367u^2\}>.0000883,
\tag{26}
\]
using \(.02479^2<4(.008137)(.0367)\).

Every bound in (19), (21), (23), and (25) is a rational
coefficient or coefficient-norm inequality of the explicitly
defined polynomial (18). Equations (20), (22), (24), and (26)
prove positivity on the entire respective intervals. Their
reserves exceed the Taylor error from Section 3. The positive
denominators and cosine now establish both scalar inequalities
(3), including all interval endpoints.
