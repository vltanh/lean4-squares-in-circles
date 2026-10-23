# Exceptional E-aligned contact with negative T outside the critical strip

## 1. Complete actual scope

All terminating decimals are exact rationals. Put
\[
 Q_1=1957767069/500000000,\qquad R=\sqrt{Q_1},\qquad
 h=.7,\qquad K=13/12.
\tag{1}
\]
The sorted squares are contained at a common ceiling q<=Q1.
H,A have positive tangent and B,D negative tangent; G and T
may initially have either sign. T lies on one of its two
canonical radial boundaries: its true core or its actual
outer-q circle. E may have either radial kind, has signed
tangent \(y_E\ge0\), and satisfies the actual aligned contact
\[
                              a_H+y_E=1.
\tag{2}
\]
Retain HG2, GA1, either AB0 or AB2, DE3 and aligned EH0. Write
\[
                 x=d_{GA}\ge0,\qquad e=d_{DE}\ge0,
                 \qquad t=x+e\in[0,.1]\ \cup\ [.16,h].
\tag{3}
\]
The remaining actual T regime is either
\[
\begin{array}{c|cc|c}
 &BT&TD&\text{negative primary}\\ \hline
 \mathrm{TD}&2&2&d_{TD}=-s<0\\
 \mathrm{BT}&3&0\text{ aligned}&d_{BT}=-s<0.
\end{array}
\tag{4}
\]
Every other actual error may have either sign. The seven errors
sum to zero and both variations are at most h.

**Theorem.** No necessary system satisfying (1)--(4) exists.
The exclusion is strict at Q1, includes weak owner ties, and
requires no E-sign reflection.

Together with
[the sharp negative-T critical-strip theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_NEGATIVE_T_CRITICAL_STRIP.md),
this covers both negative-T regimes at the exceptional contact
on the whole total-angle interval. The critical theorem retains
the sharp hard-chain possibility by same-state secondary
reselection; the present theorem is strict outside that strip.

## 2. Entry, fixed weights, and the primary split

The local B,T,D comparisons in Sections 4--5 of
[the complete core-E positive-GA theorem](HAND_G5_POSITIVE_GA_HG2_CORE_E_COMPLETE_EXCLUSION.md)
are independent of E's kind, sign and owners. A negative TD2
can either be reselected as actual TD0 at the same state, or
T is flat with
\[
                         a_T=7/12,\qquad0<s<.3.
\tag{5}
\]
An aligned negative BT3 can either be reselected as actual BT2,
or T is flat with
\[
                    a_T=7/12,\qquad0<y_T<.156,
                         \qquad0<s<.09.
\tag{6}
\]
These entry arguments use the canonical T alternative stated
in Section 1 and the common actual q. All numerical upper cuts
remain valid with q<=Q1. If a secondary is available,
[the TD0 outside-strip theorem](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_OUTSIDE_CRITICAL_STRIP.md)
already excludes the same actual state and errors. We may
therefore assume (5) or (6).

Use exactly the unadapted coefficient families of that outside
proof:
\[
\begin{array}{c|c|c|c|c|c}
 &t\text{ interval}&k&l&c&\eta\\ \hline
 \mathrm{L}&[0,.1]\cup[.16,.18]&.86265+.67t+.27t^2&.50521+.84t+.5t^2&.86265+.72t+.30t^2&.262+.19t+.08t^2\\
 \mathrm{M}&[.18,.35]&1&.551+.67t+.21t^2&.891+.64t+.02t^2&.305-.02t+.035t^2\\
 \mathrm{H}&[.35,.7]&1&.70+.32t&1.13&.27+.08t.
\end{array}
\tag{7}
\]
Set
\[
 f(u)=\cos u+\eta\sin u,\qquad n=kf(x),\qquad p=f(e).
\tag{8}
\]
Give HG,GA,AB,DE,EH the weights n,k,l,1,p. In the TD case,
give BT2,TD2 weights c,c sec s. In the BT case, give BT3,TD0
weights c sec s,c. The signed T coordinate cancels exactly.

For fixed t,s the secant coefficient does not change during
\(x+e=t\). The changing EH weight multiplies the zero residual
(2). Thus the original strict G/E split applies before maximizing
any anchor support. Only the two faces
\[
 \mathrm{ET}: (x,e)=(0,t),\qquad
 \mathrm{GT}: (x,e)=(t,0)
\tag{9}
\]
remain. The second-derivative bound is the same as (8) of the
TD0 outside proof, with negative endpoint bounds −.16 and −.21.
This is scalar concavity at fixed actual coordinates, not a
physical motion or a claim of feasibility at a relaxed face.

## 3. The sorted D gain retains the useful secant curvature

Write \(\mathcal S(a,b)\) for the support of the sorted contained
D domain in direction \((a,b)\), in its unshifted nonnegative
coordinates. Every such D has
\[
                      0\le b_D\le\sqrt{Q_1/2}-1/2<.9.
\tag{10}
\]
Consequently, for \(b_2\ge b_1\),
\[
 \mathcal S(a,b_2)-\mathcal S(a,b_1)\le.9(b_2-b_1).
\tag{11}
\]
This follows by applying the bound on b_D to each support point
and then taking the supremum.

In the TD case D has no ordinary angle: both DE and TD are
primary. Relative to its sorted baseline at coefficient c, the
exact secant gain is
\[
 G_D(s)=c\{K\tan s+\tfrac12(\sec s-1)\}
       -\{\mathcal S(1,c\sec s)-\mathcal S(1,c)\}.
\tag{12}
\]
Hence
\[
 G_D(s)\ge cJ(s),\qquad
 J(s)=K\tan s-.4(\sec s-1).
\tag{13}
\]
Define the decreasing quadratic
\[
                 g(s)=K-.2s+.32s^2,
                    \qquad0\le s\le.3.
\tag{14}
\]
The following strict gain is useful near the edge of the critical
strip:
\[
                            J(s)>s g(s)\quad(0<s\le.3).
\tag{15}
\]
Here is a short exact certificate. Multiply the difference by
cos s and use the lower Taylor bounds S7,C6 and upper bound C4.
The resulting lower polynomial is exactly
\[
 s^3\left\{\frac{37}{900}-\frac{s}{12}
       +\frac{223s^2}{1800}+\frac{7s^3}{900}
       -\frac{4097s^4}{302400}\right\}>.016s^3.
\tag{16}
\]
For the last inequality discard the two positive middle terms
and substitute s=.3 in the two negative terms. Also
\(g'(s)=-.2+.64s\le-.008\), and \(g(.3)>1.0521\).
Thus, if \(a=\min(t,.3)\),
\[
                         G_D(s)\ge c g(a)s\quad(0\le s\le a).
\tag{17}
\]
For the later positive-net case, note also
\[
 cJ'(s)=c\sec^2s\{K-.4\sin s\}
     >.86265(K-.4(.3))>.83.
\tag{18}
\]

The sorted baseline improves the full-circle baseline as well.
If c>1 its exact support is attained on the diagonal, and its
improvement is
\[
 R\left\{\sqrt{1+c^2}-\frac{1+c}{\sqrt2}\right\}
 =\frac{R(c-1)^2}
       {2\{\sqrt{1+c^2}+(1+c)/\sqrt2\}}>.32(c-1)^2.
\tag{19}
\]
Here c<=1.13, \(\sqrt{1+1.13^2}<1.509\), and
\((4(.32)(1.509))^2<Q_1\) prove the displayed coefficient.
We retain the nonnegative correction
\[
 \delta_D(t)=
 \begin{cases}
 0,&\mathrm L,\\
 .32(c-1)^2,&\mathrm M,\mathrm H,
 \end{cases}
\tag{20}
\]
since the middle and high families have c>1. Ignoring the tiny
possible low-family improvement only weakens the bound.

## 4. The short B secant gain

In the BT case D again has no ordinary angle, because both DE
and aligned TD0 contribute no D rotation. B has only its possible
AB angle. Its changed pair is \((l,c\sec s)\), and its exact
full-circle baseline gain is
\[
 G_B(s)=cF_{l/c}(s),\qquad
 F_r(s)=\sec s+K\tan s-R\sqrt{\sec^2s+r^2}
                             -1+R\sqrt{1+r^2}.
\tag{21}
\]
For every family in (7), l/c>.585. On [0,.09],
\[
 \frac{R}{\sqrt{1+r^2\cos^2s}}<1.712,
\]
by positive squaring at r=.585 and
\(\cos s\ge1-.09^2/2\). Therefore
\[
 F_r'(s)=\sec^2s\left\{K+\sin s
       -\frac{R\sin s}{\sqrt{1+r^2\cos^2s}}\right\}
       \ge K-.712s.
\]
Integration gives
\[
                 G_B(s)>1.05cs\quad(0<s\le.09),
 \qquad K-.356(.09)>1.05.
\tag{22}
\]
No sorted B correction is needed. Put \(\delta_B=0\).

## 5. The complete signed ordinary envelope

Use the functions U and V from (14) of
[the positive-T outside-strip proof](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_OUTSIDE_CRITICAL_STRIP.md).
The original zero-T pairs are
\[
                    H:(p,n),\quad A:(k,l),\quad
                    B:(l,c),\quad D:(1,c).
\tag{23}
\]
Only H,A,B have ordinary arguments. Set
\[
 V_H(u)=V_{p,n}^{n}(u),\qquad
 V_A(u)=V_{k,l}^{l}(u),\qquad
 V_B(u)=V_{l,c}^{c}(u).
\tag{24}
\]
In the TD case, B may be mixed; its larger negative coefficient
is c. In the BT case B has one angle, with actual negative
coefficient l and modified pair \((l,c\sec s)\). Its negative
charge is at least the canonical V_B in (24). Indeed the norm
gain increases in the larger coefficient for all ratios at least
one half and angles in [0,h], and l<c. The modified ratio is
\[
                    l/(c\sec s)>.585\cos(.09)>1/2.
\tag{25}
\]
The larger-coordinate monotonicity follows by squaring its
positive derivative comparison: it is enough that
\(\sin u\le2r/(1+r^2)\), which follows from
\(\sin h<.8\) and \(1/2\le r\le1\).

Every actual one-angle function is concave and the TD mixed B
function is separately concave. The unchanged H,A ratios and
the ratios just stated are above one half; each actual negative
coefficient is at least the smaller pair coefficient. Concentration
therefore respects the actual one-angle blocks and never puts
both signs into H or A. D is not introduced as an ordinary block.

Use the uniform positive cost
\[
 U_i(P)\ge-\gamma P,\qquad
 \gamma=\begin{cases}.573,&\mathrm L,\\.619,&\mathrm M,\mathrm H.
 \end{cases}
\tag{26}
\]
In the low family all actual ordinary coefficients, including
c sec(.09), are below 1.05. In the other families they are below
1.135. Thus (26) follows from the universal .545 bound. The
actual ordinary totals satisfy
\[
                         N-P=t-s,\qquad P\le h-t,\quad N\le h-s.
\tag{27}
\]

### 5.1 Nonnegative net negative magnitude

Suppose s<=t, and write d=t−s. Enlarge the positive and negative
budgets to h−d and h. The scalar concentration leaves pure
charges, a possible same-block B term, or separated charges.
Its lower envelope is
\[
                         \min(V_H(d),V_A(d),V_B(d)).
\tag{28}
\]
Here are the complete saturation checks.

On the low family d<=t<=.18, all pair ratios exceed .585 and
each larger coefficient exceeds .862. The actual B ratio is
at least .585+.2d. For TD this follows directly from
l/c>.585+.2t and d<=t. For BT the ratio is (l/c) cos s:
its loss from the lower bound .585+.2t is at most
.621s^2/2<.2s for 0<s<=.09, and s=0 is immediate.
Thus it also exceeds .585+.2(t-s). The low same-block proof
in Section 5.1 of the positive-T outside note therefore applies. For every own
negative index, the whole fixed-ratio chord gives
\[
 V_j(h)-V_j(d)\ge.862\{V_{.585,1}^{1}(h)-V_{.585,1}^{1}(d)\}
                    >.862(.7)(h-d)>.573(h-d).
\tag{29}
\]
This pays its separated positive cost. In the BT case its actual
B charge dominates the canonical B charge at both endpoints.

On the middle and high families all unchanged ratios are at
least 2/3, with every larger coefficient at least 1. Consequently
\[
                            V_j'(u)>.674>.619
\tag{30}
\]
for H,A and canonical B, by the balanced derivative estimate.
The ratio-2/3 same-block comparison applies to TD B. For BT B
use its canonical lower charge and the positive cost (26).
Thus all same-block and separated endpoints dominate one of
the pure charges in (28).

### 5.2 Positive net magnitude

Suppose s>=t and write d=s−t. The complete envelope is at least
\[
                                 -\gamma d.
\tag{31}
\]
For a separated pair, (29) at d=0 gives \(V_j(h)>.573h\)
in the low family; (30) gives \(V_j(h)>.619h\) in the other
families. Concavity and V_j(0)=0 therefore give
\(V_j(N)\ge\gamma N\). Together with (26), this pays the
negative part of P−N=d.

For the possible mixed TD B block, subtract its pure positive
charge at d=P−N. The exact difference is
\[
 c\{r(\phi(P)-\phi(P-N))+\cos N-1\},\qquad
 r=l/c>.585,\quad\phi(u)=\cos u+\sin u.
\tag{32}
\]
Put b=N/2. Its sign, when N>0, is that of
\(r\{\cos(P-b)-\sin(P-b)\}-\sin b\). Since P<=h, this
is at least
\[
                 .585\{\cos(h-b)-\sin(h-b)\}-\sin b.
\]
After division by cos b it is affine and decreasing in tan b.
Its value at b=h/2, before division, is
\[
                    .585\{\cos(.35)-\sin(.35)\}-\sin(.35)>.006.
\tag{33}
\]
Thus (32) is nonnegative. At N=0 it is exactly zero. There is
no mixed block in the BT case. This proves (31) over the full
signed ordinary domain, including every cancellation pattern.

## 6. Only the intrinsic secant endpoint remains

At either face (9), write B for the full-circle zero-T baseline
from (30) of the positive-T outside note, with z=0. Thus
\[
 C_\eta(u)=1+2\cos u+
       (1+2\eta-R\sqrt{1+\eta^2})\sin u,
\]
\[
 B=kC_\eta(x)+2l+3c+C_\eta(e)
             -R\{\sqrt{p^2+n^2}+\sqrt{k^2+l^2}
                      +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\tag{34}
\]
The first pair has p,n as in (8). Define
\[
 (a,L,\delta)=
 \begin{cases}
 (\min(t,.3),\ g(\min(t,.3)),\ \delta_D(t)),&\mathrm{TD},\\
 (\min(t,.09),\ 1.05,\ 0),&\mathrm{BT}.
 \end{cases}
\tag{35}
\]
For 0<=s<=a, (17), (22) and (28) bound the stress below by
\[
                B+\delta+cLs+\min_{j=H,A,B}V_j(t-s).
\tag{36}
\]
For fixed t and face, every function
\(cLs+V_j(t-s)\) is concave. Hence its minimum is attained
at s=0 or s=a. At s=0 the strict pure scalar inequalities of
Sections 3--5 of the original TD0 outside-strip proof apply.
The extra correction delta is nonnegative. Only s=a remains.

If s>=t, necessarily t is at most the relevant secant cap.
In the TD case (18) and (31) give
\[
 B+\delta+G_D(s)-\gamma(s-t)
 \ge B+\delta+cJ(s)-\gamma(s-t)
 \ge B+\delta+cJ(t)\ge B+\delta+cg(t)t.
\tag{37}
\]
In the BT case \(1.05c>.619\), so the same conclusion is
\(B+1.05ct\). These are exactly the s=a=t endpoints of
(36). This handles all 0<s<.3 and 0<s<.09; no concavity of
the exact secant gain is assumed.

For the endpoint scalar alone replace the H negative coefficient
by 1.06, which is at least both possible actual n values. Keep
l at A and c at canonical B. Put
\[
 \widehat\nu=(1.06,l,c),\qquad d=t-a,
\]
\[
 F_j=B+\delta+cLa+\widehat\nu_j(\cos d-1)
       -R\{\sqrt{a_j^2+b_j^2-2a_jb_j\sin d}
                                -\sqrt{a_j^2+b_j^2}\}.
\tag{38}
\]
Here the pairs are (23). The replacement is only after angular
concentration, and weakens the scalar because cos d−1<=0.
For d=0 all three charges vanish and only one scalar is needed.
The next section proves uniformly
\[
                                  F_j>.00014.
\tag{39}
\]
Equations (36)--(39) exclude each face. Strict G/E concavity
then excludes every actual primary split, proving the theorem.

## 7. Whole-interval rational endpoint certificates

Only the family changes and intrinsic caps .3,.09 split a
scalar interval. The complete construction domains are
\[
\begin{array}{c|c|c|c}
 \text{T regime}&\text{family}&t\text{ interval}&a\\ \hline
 \mathrm{TD}&\mathrm L&[0,.1]&t\\
 \mathrm{TD}&\mathrm L&[.16,.18]&t\\
 \mathrm{TD}&\mathrm M&[.18,.3]&t\\
 \mathrm{TD}&\mathrm M&[.3,.35]&.3\\
 \mathrm{TD}&\mathrm H&[.35,.7]&.3\\
 \mathrm{BT}&\mathrm L&[0,.09]&t\\
 \mathrm{BT}&\mathrm L&[.09,.1]&.09\\
 \mathrm{BT}&\mathrm L&[.16,.18]&.09\\
 \mathrm{BT}&\mathrm M&[.18,.35]&.09\\
 \mathrm{BT}&\mathrm H&[.35,.7]&.09.
\end{array}
\tag{40}
\]
For a full interval [b,b+D], use the local variable u=t−b.
Use the sine polynomial S15 and cosine polynomial C16. Form
(7), p=C16(t)+eta S15(t), and the four pairs in (23) on
both faces (9). Before radical terms, the polynomial expression
is respectively
\[
\begin{split}
 A_{ET}&=3k+2l+3c+1+2C_{16}(t)+(1+2\eta)S_{15}(t),\\
 A_{GT}&=3+2l+3c+k\{1+2C_{16}(t)+(1+2\eta)S_{15}(t)\}.
\end{split}
\tag{41}
\]
Add delta+cLa. If a is a cap, add
\(\widehat\nu_j(C_{16}(t-a)-1)\) and subtract
\(2a_jb_jS_{15}(t-a)\) from that squared norm. If a=t,
all charges are zero and no index is selected.

Use the four resulting squared norms with weight 1. Append
the fifth weighted norm
\[
 (1+\eta^2,S_{15}(t))\quad\text{on ET},\qquad
 (1+\eta^2,kS_{15}(t))\quad\text{on GT}.
\tag{42}
\]
These weights are nonnegative. For each squared norm v, construct
its positive cubic mass by the same exact rule as (30) of the
TD0 outside-strip proof:
\[
\begin{gathered}
 \rho_0=1,\quad \rho_{i+1}=(\rho_i+v(0)/\rho_i)/2\quad(i=0,1,2),\\
 w=([v]_{\le3}-v(0))/v(0),\qquad
 m_v=[\rho_3(1+w/2-w^2/8+w^3/16)]_{\le3}.
\end{gathered}
\tag{43}
\]
For the five weighted norms \((v_i,w_i)\), set
\[
 P=2A\prod_i m_{v_i}
 -R_+\sum_i w_i(v_i+m_{v_i}^2)\prod_{r\ne i}m_{v_r},
                         \qquad R_+=1.978770866.
\tag{44}
\]
The exact identity
\((v+m^2)/(2m)-\sqrt v=(\sqrt v-m)^2/(2m)\ge0\)
shows that \(P/(2\prod m)\) is a lower bound for the scalar
with those polynomial trigonometric inputs.

Let \(\mathcal L_D\) be the whole-interval shifted-Chebyshev
coefficient-norm lower bound specified at the end of the
positive-T outside-strip proof. Direct rational substitution
into (41)--(44) gives the following compact uniform certificates:

* For every row of (40), face, and allowed index except the
  TD middle diagonal row, \(\mathcal L_D(P)>.004\).
* For the TD middle diagonal row, the two faces are identical;
  \(P(0)>.00238\) and
  \(\mathcal L_{.12}((P-P(0))/u)>.0072\).
* Every mass lies in (.89,1.51), every squared norm is above .79,
  and every resulting numerator has degree at most 50.

There are 44 such whole-interval scalar constructions. The
second bullet proves positivity on its entire interval by a
positive first quotient; it is not a pointwise test. All
numerators are therefore above .00238, and
\[
                              2\prod_i m_{v_i}<2(1.51)^5<16.
\tag{45}
\]

The sine and cosine substitution errors are respectively at
most \(h^{17}/17!\) and \(h^{18}/18!\), each below
\(10^{-15}\). The scalar's total absolute partial-derivative
bound in its four possible trigonometric inputs is below 20:
all coefficients are at most 1.13, eta<.327, and the squared
norms remain above .78 throughout their Taylor enclosures.
For a norm differentiated in a coefficient its derivative has
absolute value at most 1; a derivative in the sine argument
has magnitude \(a_jb_j/N_j\). These bounds give the stated
constant directly. The total substitution loss is thus less
than \(10^{-10}\). Combining (44)--(45),
\[
                    F_j>.00238/16-10^{-10}>.00014,
\]
which proves (39). Every coefficient-norm assertion above is
one exact rational calculation on a full interval. There is no
angle mesh, optimizer premise, or coefficient-row inventory.
