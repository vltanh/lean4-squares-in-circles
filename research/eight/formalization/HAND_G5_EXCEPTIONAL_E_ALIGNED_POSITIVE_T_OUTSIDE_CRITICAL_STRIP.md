# Exceptional E-aligned contact with positive T outside the critical strip

## 1. Exact domain and strict conclusion

All terminating decimals denote exact rational numbers. Put
\[
 Q_1=1957767069/500000000,\qquad R=\sqrt{Q_1},\qquad h=.7.
\tag{1}
\]
Every square is sorted and contained at a common ceiling at most
Q1. H,A have positive tangent and B,D have negative tangent;
G,T may have either tangent sign. E has signed tangent
\(y_E\ge0\). Retain HG2, GA1 with error \(x\ge0\), either
AB0 or AB2, DE3 with error \(e\ge0\), and aligned EH0 with
its exact actual contact
\[
                              a_H+y_E=1.
\tag{2}
\]
Retain either of the following actual T regimes:
\[
\begin{array}{c|cc|c}
 &BT&TD&\text{nonnegative primary error}\\ \hline
 \mathrm{TD}&2&2&z=d_{TD}\ge0\\
 \mathrm{BT}&3&0&z=d_{BT}\ge0.
\end{array}
\tag{3}
\]
Every remaining actual error may have either sign. The seven
errors sum to zero and both their positive and negative variations
are at most h. Thus
\[
 t=x+e+z\le h.
\]
Assume
\[
                         t\in[0,.1]\ \cup\ [.16,h].
\tag{4}
\]

**Theorem.** No such necessary system exists. The exclusion is
strict at Q1 and includes all zero-error witness ties. It does
not require any square to have a particular radial kind.

Together with
[the positive-T critical-strip theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_CRITICAL_STRIP.md),
this treats the exceptional E-positive contact for both positive
T owners on the whole interval \(0\le t\le h\), at
\(q\le q_*\). The critical theorem retains the sharp hard-chain
zero and proves \(x=z=0\); the present theorem is strict outside
that strip. No reflection changing E's sign is used here.

## 2. Continuous weights and exact forces

Select one of these base coefficient families using t:
\[
\begin{array}{c|c|c|c|c|c}
 &t\text{ interval}&K&L&C&\eta\\ \hline
 \mathrm{L}_0&[0,.1]&.86265+.67t+.27t^2&.50521+.84t+.5t^2&.86265+.72t+.30t^2&.262+.19t+.08t^2\\
 \mathrm{L}_1&[.16,.18]&.86265+.67t+.27t^2&.50521+.84t+.5t^2&.86265+.72t+.30t^2&.262+.19t+.08t^2\\
 \mathrm{M}&[.18,.35]&1&.551+.67t+.21t^2&.891+.64t+.02t^2&.305-.02t+.035t^2\\
 \mathrm{H}&[.35,.7]&1&.70+.32t&1.13&.27+.08t.
\end{array}
\tag{5}
\]
At a shared endpoint either adjacent family is valid. Set
\[
 k=K+.06z,\qquad l=L-.23z,\qquad c=C-.53z,
\]
\[
 n=k(\cos x+\eta\sin x),\quad
 p=\cos e+\eta\sin e,\quad
 m=c(\cos z+\eta\sin z).
\tag{6}
\]
Give HG,GA,AB the weights n,k,l and DE,EH the weights 1,p.
Give BT,TD the weights m,c in the TD regime and c,m in the
BT regime. Every weight is positive.

The G force is exactly
\(k\sin x(a_G+\eta(-y_G))\). The T force is, respectively,
\[
 c\sin z(a_T-\eta y_T),\qquad
 c\sin z(a_T+\eta y_T).
\tag{7}
\]
For
\[
 \sigma_\eta=R\sqrt{1+\eta^2}-(1+\eta)/2,
\]
the containing shifted circles bound these forces by
\(k\sigma_\eta\sin x\) and \(c\sigma_\eta\sin z\),
for either sign of G and T. The actual DE3 and aligned EH0
projections give E force
\[
                         \sin e(a_E+\eta y_E).
\tag{8}
\]
Indeed the signed E coefficient is
\(p-\cos e=\eta\sin e\). The four outer zero-ordinary-error
pairs are
\[
\begin{array}{c|cccc}
 &H&A&B&D\\ \hline
 \mathrm{TD}&(p,n)&(k,l)&(l,m)&(1,c)\\
 \mathrm{BT}&(p,n)&(k,l)&(l,c)&(1,m).
\end{array}
\tag{9}
\]
These force identities are valid before any optimization of a
coordinate or angular argument.

## 3. The primary split at fixed z

Fix t,z and all ordinary errors and actual anchor coordinates.
The coefficients k,l,c,eta are fixed. Split x+e=t−z before
maximizing the four outer supports, and retain E's actual
coordinates during this split. The varying coefficient p
multiplies the zero EH residual in (2).

The sorted H residual is greater than −.065, as in Section 3
of [the sharp E-aligned proof](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_SHARP_CRITICAL_STRIP.md).
Also \(a_E-.5<.915\), \(\sigma_\eta-.5<.935\), and
\(y_E\ge0\). Throughout (5)--(6),
\[
                         .862<k\le1.042,
                         \qquad .262\le\eta<.327.
\tag{10}
\]
The split second derivative is consequently at most
\[
 k\{-.435\cos x+.957\sin x\}-.5\cos e+.915\sin e.
\tag{11}
\]
On x+e<=h, its upper bounds at x=0 and e=0 are respectively
less than −.16 and −.20. Explicitly,
\[
\begin{split}
 -.435(.862)-.5(.7648)+.915(.6443)&<-.16,\\
 1.042\{-.435(.7648)+.957(.6443)\}-.5&<-.20.
\end{split}
\tag{12}
\]
For fixed x+e the expression in (11) is a linear combination
of cos x and sin x. Dividing by positive cos x makes its sign
affine in tan x, so its negative endpoint signs prove negativity
on the entire split. The complete relaxed stress is strictly
concave. It suffices to consider the two full triangular faces
\[
 \mathrm{GT}:\quad (x,e)=(t-z,0),\qquad
 \mathrm{ET}:\quad (x,e)=(0,t-z),\qquad0\le z\le t.
\tag{13}
\]
No physical transport is asserted in this concavity argument.
All dependence on z in (6) remains; there is no concavity claim
in z.

## 4. Actual ordinary blocks and their concentration

For a positive pair a,b, let q=max(a,b), r=min(a,b)/q and define
\[
\begin{split}
 U_{a,b}(s)&=\min(a,b)(\cos s+\sin s-1)
 -R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\},\\
 V_{a,b}^{\nu}(s)&=\nu(\cos s-1)
 -R\{\sqrt{a^2+b^2-2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{split}
\tag{14}
\]
The actual valid negative coefficients and possible mixed blocks
are
\[
\begin{array}{c|cccc|c}
 &\nu_H&\nu_A&\nu_B&\nu_D&\text{possible mixed block}\\ \hline
 \mathrm{TD}&n&l&\max(l,m)&c&B\\
 \mathrm{BT}&n&l&l&m&\text{none}.
\end{array}
\tag{15}
\]
An actual AB0 angle belongs to B and an actual AB2 angle belongs
to A. H,A each have at most one ordinary angle. In the TD row,
B is enlarged to permit both AB and BT ordinary arguments even
when AB2 is selected. D has no ordinary angle in that row;
allowing an extra single-angle D block is a harmless enlargement.
In the BT row B has only its possible AB angle and D only its
TD0 angle. No absent geometric witness is used.

Every ratio is above one half. H,A,D and the BT-row B block
have actual negative coefficient between the smaller and larger
pair coefficient. Their one-angle functions are concave because
\(-RN''(-s)<.762\min(a,b)<\min(a,b)\cos h\).
Only TD-row B uses the separately concave two-angle function,
with its larger negative coefficient as in (15). The
[continuous angular concentration](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
therefore applies to the full signed ordinary domain.

After removing the three nonnegative primary errors, the remaining
ordinary totals satisfy N−P=t, P<=h−t and N<=h. Concentration
leaves pure charges \(V_i(t)\), a same-block TD B alternative,
or separated alternatives
\[
                         U_i(P)+V_j(h),\qquad P=h-t.
\tag{16}
\]
We prove below that each same-block or separated alternative
is at least its own pure charge. Thus the whole envelope is at
least
\[
                         \min_{i\in\{H,A,B,D\}}V_i(t).
\tag{17}
\]
The universal positive-side bound is
\[
                         U_i(P)\ge-.545q_{\max}P,
\tag{18}
\]
where qmax bounds every actual pair coefficient. We do not
replace (15)'s mixed coefficient during this concentration.

## 5. Uniform angular comparisons on the three families

The following bounds hold on both faces (13) and for both T
owners. In the low row the larger interval [0,.18] is permitted.
\[
\begin{array}{c|c|c|l}
 &q_{\max}&\text{ratios}&\text{additional bounds}\\ \hline
 \mathrm{L}&1.05&\text{all}>.585; B>.585+.2t&\text{each larger coefficient}>.862;\ B\text{ has }l<\min(c,m)\\
 \mathrm{M}&1.118&H,D>.71; A\in(.62,.812);\ B>2/3&\min(H,D)>.911;\ l>.636;\ \min(c,m)>.911>l\\
 \mathrm{H}&1.131&\text{all}>.71&\text{each coefficient}>.731;\ m+.03>l.
\end{array}
\tag{19}
\]
Here min(H,D) means each coefficient of the H and D pairs.
For the middle row, the final comparison \(.911>l\) can be
weakened to l<min(c,m); in fact l<.812. Section 8 gives a
single whole-square rational certificate for all the bounds
actually needed in (19).

### 5.1 Same-block alternatives

For a mixed pair with ratio r and larger coefficient q, the
same-block term at (P,h) minus its pure term at t is at least
\[
               q\{r(\cos P+\sin P-1)+\cos h-\cos t\}.
\tag{20}
\]
On the low family use r=.585+.2t. The bracket is positive
on [0,.2]: its value at 0 exceeds .004, its first derivative
at 0 and .2 exceeds .011 and .021, and its third derivative
is below −.5. Its first derivative is therefore concave and
positive everywhere on this interval.

On the middle and high families r>=2/3. The bracket for r=2/3
is convex, decreasing, and zero at t=h. For example, its second
derivative equals
\[
 (\cos h-2/3)\cos(h-t)+(\sin h-2/3)\sin(h-t)>0,
\]
and its derivative at h is \(\sin h-2/3<0\). This proves
(20) nonnegative on the full domain.

### 5.2 Every low separated term pays its positive cost

Put \(V_r=V_{r,1}^{1}\). Its derivative increases with r,
and its derivative is positive on [0,h] at r=.585. Since
\(\nu_j\le\max(a_j,b_j)\), (19) gives
\[
 V_j(h)-V_j(t)
 \ge .862\{V_{.585}(h)-V_{.585}(t)\}
 >.862(.7)(h-t).
\tag{21}
\]
The final fixed-ratio chord holds on the whole interval
0<=t<=.18. Subtracting .7(h−t) from that chord gives a decreasing
function, whose value at .18 exceeds .005. Positive squaring
establishes both assertions, as in Section 5 of
[the TD0 outside-strip proof](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_OUTSIDE_CRITICAL_STRIP.md).
The exact reserve is
\[
                       .862(.7)-.545(1.05)>.031.
\tag{22}
\]
Thus every low separated alternative dominates its own V_j(t).
No comparison between different negative indices is needed.

### 5.3 Middle and high separated terms

For ratios at least 2/3, the balanced derivative estimate is
\[
                         (V_{a,b}^{\max(a,b)})'>.674\max(a,b).
\tag{23}
\]
It follows by positive squaring from the decreasing cubic
\[
 Q_1r^2(1-v^2)-(v+.674)^2(1+r^2-2rv),
          \quad r=2/3,\quad 0\le v\le.6443,
\]
whose value at .6443 is greater than .00048. It handles middle B:
\[
                  .674(.911)-.545(1.118)>.0047.
\tag{24}
\]
For middle A, its actual coefficient is the smaller coefficient l.
With r=l/k in [.62,.812], convexity in r gives
\(1+r^2-2r\sin h<.786^2\). Concavity in angle then yields
\[
 V_A'(s)\ge V_A'(h)
 >.636\{-.6443+1.9787(.7648)/.786\}>.8.
\tag{25}
\]

For every ratio .71<=r<=1, one has
\[
                         (V_{a,b}^{\max(a,b)})'>\min(a,b).
\tag{26}
\]
Concavity reduces this to s=h. Positive squaring reduces it to
\[
 Q_1r^2(.7648)^2-(r+.6443)^2(1+r^2-2r(.6442))>.052
                       \quad(.71\le r\le1).
\tag{27}
\]
The whole-interval coefficient-norm lower bound of this quartic
is greater than .0683, as verified explicitly in Section 8.
Equation (26) handles middle H,D and every high index. The high
reserve is
\[
                         .731-.545(1.131)>.114.
\tag{28}
\]
Equations (23)--(28) pay the positive cost in every separated
term. Along with Sections 5.1--5.2 they prove (17), including
all ordinary error signs and both AB owners.

## 6. The endpoint scalars

Define
\[
 C_\eta(s)=1+2\cos s+
                 (1+2\eta-R\sqrt{1+\eta^2})\sin s.
\tag{29}
\]
At either face in (13), with pairs (9), the zero-ordinary-error
baseline is
\[
 B=kC_\eta(x)+cC_\eta(z)+2l+C_\eta(e)
                            -R\sum_j\sqrt{a_j^2+b_j^2}.
\tag{30}
\]
All four remaining circle supports have been maximized only
now, after the actual-coordinate split.

For the scalar alone, use the coefficients
\[
\begin{array}{c|cccc}
 &\widehat\nu_H&\widehat\nu_A&\widehat\nu_B&\widehat\nu_D\\ \hline
 \mathrm{TD,L/M}&n&l&m&c\\
 \mathrm{TD,H}&n&l&m+.03&c\\
 \mathrm{BT}&n&l&l&m.
\end{array}
\tag{31}
\]
These are at least the respective coefficients in (15). In
particular, l can exceed m in the high TD family; the certified
inequality m+.03>l is needed here. This replacement is performed
only after concentration, where \(\cos t-1\le0\) makes it a
valid scalar lower bound.

For each index i let
\[
\begin{split}
 F_i={}&kC_\eta(x)+cC_\eta(z)+2l+C_\eta(e)
                   +\widehat\nu_i(\cos t-1)\\
 &-R\sum_{j\ne i}\sqrt{a_j^2+b_j^2}
       -R\sqrt{a_i^2+b_i^2-2a_ib_i\sin t}.
\end{split}
\tag{32}
\]
The explicit certificate in the next section proves, uniformly
on every whole face,
\[
                             F_i>77/1000000.
\tag{33}
\]
Equations (17), (30)--(33) contradict the weak necessary
inequalities on both faces. The strict split in Section 3 then
proves the theorem for every x+e+z=t in (4).

## 7. Explicit whole-square polynomial certificate

Use the exact enclosure arithmetic (4)--(10) and tensor identity
(20)--(21) of
[the sole-E positive-T polynomial companion](HAND_G5_SOLE_E_POSITIVE_T_POLYNOMIAL_CERTIFICATES.md).
For clarity, the construction required here is specified fully
below. It uses total-degree-14 truncation, with every discarded
coefficient charged by its absolute value, and uses sine through
degree 13 and cosine through degree 14 with remainders
\(h^{15}/15!\) and \(h^{16}/16!\). Products use the stated
left-to-right order and integer powers use binary exponentiation.

For each full interval [a,b] in (5), put
\[
 t=(a+b)/2+(b-a)X/2,\qquad z=t(1+Y)/2,
                           \qquad -1\le X,Y\le1.
\tag{34}
\]
Choose either face (13). Form k,l,c,eta by (5)--(6), and form
\[
 n=k(C(x)+\eta S(x)),\quad p=C(e)+\eta S(e),\quad
 m=c(C(z)+\eta S(z))
\]
as rational enclosure pairs. Use the pairs (9) and coefficients
(31). Here C,S mean the just specified trigonometric enclosures.

For a positive squared-norm enclosure v=[p_v,e_v], define
\[
 \rho_v=10^{-8}\left\lfloor10^8\sqrt{(p_v)_{00}}+\frac12\right\rfloor,
\qquad
 \mathcal S(v)=\rho_v\sum_{j=0}^7
   \binom{1/2}{j}\left(\frac{v-\rho_v^2}{\rho_v^2}\right)^j.
\tag{35}
\]
Evaluate the sum by Horner's rule in the enclosure arithmetic.
Every constant coefficient used in (35) is positive. The integer
rounding is specified by two rational square comparisons. The
eighth derivative of the square root is negative, hence
\(\mathcal S(v)\ge\sqrt v\) for every actual v>=0.

Put \(R_+=1.978770866>R\). Start with
\[
\begin{split}
 B_0={}&k\{1+2C(x)+(1+2\eta)S(x)\}
      +c\{1+2C(z)+(1+2\eta)S(z)\}\\
 &+2l+1+2C(e)+(1+2\eta)S(e)\\
 &-R_+\{kS(x)+cS(z)+S(e)\}\mathcal S(1+\eta^2).
\end{split}
\tag{36}
\]
For index i, add \(\widehat\nu_i(C(t)-1)\). In order H,A,B,D,
subtract \(R_+\mathcal S(a_j^2+b_j^2)\) for j different from i,
and subtract
\(R_+\mathcal S(a_i^2+b_i^2-2a_ib_iS(t))\) for j=i.
Call the resulting enclosure \([P_i,E_i]\). All primary sine
weights are nonnegative, so
\[
                              F_i\ge P_i-E_i.
\tag{37}
\]

For \(P=\sum p_{ij}X^iY^j\), define
\[
 d_{kl}=2^{k+l}\sum_{i\ge k,j\ge l}
 (-1)^{i+j-k-l}\binom{i}{k}\binom{j}{l}p_{ij},
\]
\[
 \beta_{AB}(P)=\sum_{k\le A,l\le B}d_{kl}
 \frac{\binom{A}{k}}{\binom{16}{k}}
 \frac{\binom{B}{l}}{\binom{16}{l}},\qquad0\le A,B\le16.
\tag{38}
\]
The tensor identity in the cited companion expresses P as a
convex combination of these coefficients on the whole square.
Substitution of (5), (9), (31), (34)--(36) into (38) gives the
following compact uniform rational bounds:
\[
       E_i<53/1000000,\qquad
       \beta_{AB}(P_i)>13/100000
                         \quad(0\le A,B\le16).
\tag{39}
\]
The quantifiers include all four full intervals, both faces,
both T owners, and all four negative indices. Formula (38),
together with the uniquely specified rational arithmetic, is
the algebraic certificate; its indices are not sampled angles.
There is no subdivision inside an interval and no coefficient-row
inventory. A common denominator makes every comparison in (39)
an exact signed-integer comparison, by (23) of the companion.
Equations (37)--(39) give (33) directly.

## 8. Exact range and one-variable verification

Here is a compact reproduction rule for the coefficient claims
in (19), using the same full-square enclosure arithmetic and
coefficient map (38). For every pair (a,b), certify
\(q_{\max}-a\) and \(q_{\max}-b\). Add the following expressions:

* Low: a−.585b and b−.585a for each pair; the chosen larger
  coefficients n,k,b_B,1 minus .862; and
  \(l-(.585+.2t)b_B\), \(b_B-l-.2\).
* Middle: a−.71b, b−.71a, a−.911 and b−.911 for H,D;
  \(l-.62k\), \(.812k-l\), \(l-.636\);
  \(3l-2b_B\), \(b_B-l-.2\), \(b_B-.911\).
* High: a−.71b, b−.71a, a−.731 and b−.731 for every pair;
  and \(m+.03-l\).

Here \(b_B=m\) in the TD row and \(b_B=c\) in the BT row.
For every polynomial/error pair [P,E] in this finite recipe,
\[
             E<10^{-9},\qquad \beta_{AB}(P)-E>10^{-4}.
\tag{40}
\]
The two stronger comparisons also hold uniformly:
\[
  \beta_{AB}(3l-2b_B)-E>.0097\quad\text{in the middle family},
\]
\[
  \beta_{AB}(m+.03-l)-E>.0068\quad\text{in the high family}.
\tag{41}
\]
This proves the required ranges on both complete triangular faces.
The low inequalities also hold directly on [0,.18]:
\(m\le C\), because m decreases with z at fixed t, and
\[
 L-.23t-(.585+.2t)C
       =.00055975+.01627t+.1805t^2-.06t^3>0.
\tag{42}
\]
Also \(L-.23t-.585(K+.06t)>0\); all other low ranges
follow from (5), \(\eta<.299\), and
\(K+.06t\le1.002798\).

The one-variable checks use rational Taylor bounds
\(S_{15}\le\sin\le S_{13}\) and
\(C_{14}\le\cos\le C_{16}\) on [0,h]. Fixed positive square
roots are enclosed by rationals differing by \(2\cdot10^{-12}\),
with the two square inequalities checked exactly. These give the
same-block endpoint reserves stated after (20), the fixed-ratio
chord reserve .005 in (21), and the cubic reserve .00048 in
(23). For the chord's monotonicity it is enough to check
\[
 q_L(.585)^2\cos^2(.18)
 >(.7+\sin(.18))^2(1+.585^2),\qquad q_L=19577/5000.
\tag{43}
\]

For completeness, the coefficient-norm operator used for (27)
is explicit. If \(A(u)=\sum_j a_j u^j\) on [0,D], define
\[
 b_0=\sum_j a_jD^j4^{-j}\binom{2j}{j},\qquad
 b_i=2\sum_{j\ge i}a_jD^j4^{-j}\binom{2j}{j-i}\quad(i>0).
\]
Then \(A\ge b_0-\sum_{i>0}|b_i|\), by the shifted Chebyshev
identity. For the quartic in (27), put r=.71+u and D=.29.
This exact rational lower bound is greater than .0683, proving
its stated .052 reserve. All remaining inequalities
(12), (22), (24), (25), (28) are the displayed rational
comparisons. These checks complete the whole-domain angular
and scalar proof, with no sampled value or optimizer premise.
