# A negative A primary and a longer nonnegative E total

## 1. Original scope

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad L=\frac16,\quad d=\frac8{15},\quad
 M=\frac{19}{50},\quad D=d-M=\frac{23}{150},\quad K=\frac{13}{12}.
\tag{1}
\]
Retain the original sorted outer states H,G,B,D with signed
tangents respectively positive, negative, negative and negative,
either HG0 or HG2, BT2, and TD2 with error z≥0. E is nonpositive
and may have either canonical radial kind. Its selected DE3/EH1
primaries have nonnegative total e, including a signed sum when
both are retained, as in
[the signed E comparison](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md).
Every unselected secondary argument remains arbitrary.

A has one genuine negative primary of magnitude s, with its
other edge secondary. The alternatives are GA3/AB0 or GA2/AB2.
The local entry theorem gives a positive flat-core A with
\(a_A=7/12\), and the respective bounds
\[
 \begin{array}{c|cc}
  \text{negative primary}&b_A& s\\ \hline
  GA3&b_A<39/250&s<1/4,\\
  AB2&b_A<1/2&s<19/50.
 \end{array}
\tag{2}
\]
Retain the neighboring inequalities and the variation bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+\le h,\qquad\sum_i(-d_i)_+\le h.
\tag{3}
\]
In particular z+e≤h, because the positive parts of a selected
E-primary pair sum to at least e.

**Theorem.** There is no such necessary system when e≥s.
Together with
[the shorter-E transfer](HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md),
this excludes every nonnegative E total for either genuine
negative A primary and every nonnegative TD2 error. It retains
BT2. No frame order is assumed.

The proof applies after an A-only transport when the displayed
local, radial, and variation data have been preserved. Its
scalar calculations use no new original-marker assertion.

## 2. One concave gain handles both negative A primaries

For a fixed actual flat-core A, subtract the zero-angle A-primary
projection and include the width difference. The gains are
\[
 g_G(s)=K\sin s-(b_A+\tfrac12)(1-\cos s),
 \qquad
 g_B(s)=K\sin s-(\tfrac12-b_A)(1-\cos s).
\tag{4}
\]
For a genuine negative GA3 witness the sharper contact cut is
\[
                  b_A<.156-.63s,\qquad s<.244.
\tag{5}
\]
This is exactly the local contact-vector proof in
[the sharp negative EH1 entry cut](HAND_G3_CORE_E_NEGATIVE_EH1_SHARP_ENTRY_CUT.md).
To check its use here, the actual projections at error −s are
\[
 P_{GA3}=a_G-\tfrac7{12}\sin s-b_A\cos s,
 \qquad P_{GA2}=a_G\cos s-b_G\sin s-b_A.
\]
They are the same two formulas as EH1/EH0 in that local proof,
under \((a_H,b_H,a_E,b_E)=(a_G,b_G,7/12,b_A)\).
The feasible first projection and infeasible second projection
give the identical strict corner comparison
\[
             Q>(b_A+\tfrac12+\cos s)^2+(K+\sin s)^2.
\tag{6}
\]
The cited whole-interval derivative and endpoint bounds therefore
prove (5) without any additional incident-edge hypothesis.

For negative AB2, its actual inequality instead gives
\[
 b_A\ge\tfrac12+(\tfrac12-b_B)\sec s+K\tan s
                           \ge1-b_B>\tfrac1{10}.
\tag{7}
\]
The derivative of the middle expression is positive, because
\(K+(1/2-b_B)\sin s>K-.4>0\).

Define on the whole analytic interval 0≤r≤M
\[
             g_*(r)=K\sin r-(.656-.63r)(1-\cos r).
\tag{8}
\]
At every actual input in (2), either gain in (4) is at least
g_*(s). For GA3 this follows from (5). For AB2, (7) gives
\(1/2-b_A<.4\), while
\(.656-.63r\ge.4166>.4\) throughout [0,M].

The comparison function is strictly concave:
\[
 g_*''(r)=\frac{53}{300}\sin r+(.63r-.656)\cos r
 \le\frac{53}{300}M+(.63M-.656)(1-M^2/2)<-.31.
\tag{9}
\]
This concavity holds even beyond the smaller actual GA3 cut.
An analytic endpoint at r=M will not assert a GA3 witness there.

## 3. The small total is absorbed directly

Write \(\delta_0=z+e\). Suppose first \(\delta_0\le L\), and
put \(e'=e-s\ge0\). The support charge
\[
 j(u)=W(u)-1-S(\sin u,1-\cos u),\qquad
 W(u)=\frac{1+\cos u+|\sin u|}{2},
\tag{10}
\]
is on its axis branch for 0≤u≤L. With
\(a_0=\sqrt{Q-1/4}-1/2\), it satisfies
\[
 j'(u)=-\tfrac12\sin u-(a_0-\tfrac12)\cos u
                         >-\frac{599}{600},
\tag{11}
\]
using \(a_0-1/2<.915\) and \(.915+L/2=599/600\).
Also
\[
 \frac{g_*(r)}r\ge K(1-L^2/6)-.328L>1
                         \qquad(0<r\le L).
\tag{12}
\]
Here the positive .63r(1−cos r) term was discarded before
using the elementary sine and cosine bounds.

Use the already proved small-total weights at z+e' from
[the nonnegative-A/E theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).
Their two A multipliers are equal to l>1, and their two E
multipliers equal one. Equations (11)--(12) give
\[
                   l g_*(s)+j(e)\ge j(e')+s/600.
\tag{13}
\]
The weak form also holds at s=0.

Delete the negative A-primary argument, the designated E
arguments, and the fixed TD argument inside the force sum.
Its remaining signed sum is \(-z-e'\), its positive variation
is at most h−z−e≤h−z−e', and its negative variation is at most h.
The reference circle forces are exactly the positive-TD2,
nonnegative-E expression at virtual E total e', with A's
deleted argument inserted as zero. Thus the small-total
scalar proof applies. Its strict positivity, strengthened by
(13), is a contradiction. No reference owner is declared to
be an actual witness.

## 4. Balanced concentration at a larger total

Now assume L≤δ_0≤h. Use the explicit families of Section 4
of the same nonnegative-A/E theorem, with its parameter
\(\theta=z\) and its E total equal to the actual e.
For z≥L put t=z−L and use
\[
 \begin{split}
 k&=.6692+.5218t-.5956t^2+.4216t^3+.28e,\\
 l&=1+.0175t-1.0932t^2+1.278t^3+.25e,\\
 c&=1.0163-.0209t-1.1486t^2+1.4069t^3+.25e.
 \end{split}
\tag{14}
\]
For z≤L≤z+e put x=L−z and use
\[
             k=.6692-.10x+.28e,
       \qquad l=1+.25e,\qquad c=1.0163+.25e.
\tag{15}
\]
All decimals in this note denote exact rationals.

Put
\[
 \eta=.293,\quad m=c(\cos z+\eta\sin z),\quad
 \sigma=R\sqrt{1+\eta^2}-(1+\eta)/2.
\tag{16}
\]
The actual seven multipliers are \((k,l,l,m,c,1,1)\).
The referenced range proof gives all three ordinary pairs
\[
 H=(k,1),\quad G=(k,l),\quad
 B=(\min(l,m),\max(l,m))
\tag{17}
\]
smaller-to-larger ratio at least 2/3 and
\(q_{\max}/q_{\min}\le6/5\). It also gives every hypothesis
of the sorted D minorant. These weights are now held fixed
while s is varied in the scalar argument.

Use the full-circle upper support
\(\overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2\), and weaken the
sorted D zero support to this full support as well. The baseline is
\[
 \begin{split}
 B(z)={}&k+2l+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(k,l)
       -\overline S(l,m)-\overline S(1,c).
 \end{split}
\tag{18}
\]
Define the ordinary negative increments
\[
 V_{p,q}(u)=q(\cos u-1)
       -R\{\sqrt{p^2+q^2-2pq\sin u}-\sqrt{p^2+q^2}\}.
\tag{19}
\]

The negative A comparison contributes at least l g_*(s), and
the E comparison contributes at least j(e). The remaining
ordinary arguments have
\[
 P\le h-z-e,\quad N\le h-s,
              \qquad N-P=z+e-s=\delta_0-s\ge0.
\tag{20}
\]
Enlarge their domain to \(P\le h-(\delta_0-s)\), \(N\le h\).
The established balanced concentration, including its D
minorant, therefore leaves only the three functions
\[
 F_i(s)=B(z)+l g_*(s)+j(e)+V_i(\delta_0-s),
                                  \qquad i=H,G,B.
\tag{21}
\]
Every F_i is concave in s on \([0,\min(e,M)]\): (9) proves
the gain concavity, and the whole-interval norm lemma proves
V_i concave. Thus it suffices to prove the endpoint values at
\[
                         s=0,\qquad s=\min(e,M).
\tag{22}
\]
The first is exactly a T endpoint already certified by the
nonnegative-A/E theorem. Sections 5--7 below prove the second.

## 5. Four intrinsic domains and twelve explicit numerators

For convenience use native variables (x,y) separately on the
following four whole domains:

| Domain | z | e | s | Native domain |
| --- | --- | --- | --- | --- |
| TE | L+x | y | e | x,y≥0, x+y≤d |
| TC | L+x | M+y | M | x,y≥0, x+y≤D |
| RE | L−x | x+y | e | 0≤x≤L, 0≤y≤M−x |
| RC | L−x | M+y | M | 0≤x≤L, 0≤y≤D+x |

TE certifies a larger domain than required: its endpoint is
used only when e≤M. This algebraic extension is harmless.
The other three domains are precisely their indicated weight
and endpoint alternatives. Together they cover the second
endpoint in (22).

In each row substitute z,e into (14) or (15), and put
\(\delta=z+e-s\). Use the rational bounds
\[
 \overline R=1.978787508,\qquad
 \overline a=1.414575672,\qquad
 \overline\sigma=1.415477291,
\tag{23}
\]
whose positive-square comparisons are already proved in the
nonnegative-A/E theorem. Let
\[
 J(u)=\frac{C_{10}(u)-1}{2}+(\tfrac12-\overline a)S_9(u),
\]
\[
 G(u)=K S_{11}(u)+(.656-.63u)(C_{10}(u)-1).
\tag{24}
\]
Every coefficient \(.656-.63s\) is positive on these domains,
so G(s)≤g_*(s). The E lower charges are
\[
 j_e^-=
 \begin{cases}
 J(e)-.002e^4,&\mathrm{TE},\mathrm{TC},\\
 J(e),&\mathrm{RE},\\
 J(e)-.029e^4,&\mathrm{RC}.
 \end{cases}
\tag{25}
\]
The two quartic support envelopes are proved in Section 5 of
the nonnegative-A/E theorem. In RE, e≤M<1/2, so the exact
support remains on the axis branch and needs no quartic loss.

Put
\[
 \mathcal M=c\{C_{12}(z)+\eta S_9(z)\},
\qquad
 q_B^+=
 \begin{cases}
 l+.15(d-x),&\mathrm{TE},\mathrm{TC},\\
 \mathcal M,&\mathrm{RE},\mathrm{RC}.
 \end{cases}
\tag{26}
\]
The already proved coefficient ranges give
\(q_B^+\ge\max(l,m)\) and \(\mathcal M\ge m\).
Start with the nonradical polynomial
\[
 A=2k+3l+3+c\{1+2C_{10}(z)
           +(\tfrac32\eta+\tfrac12-\overline\sigma)S_9(z)\}
                         +j_e^-+lG(s),
\tag{27}
\]
and the four squared norms
\[
 P_H=1+k^2,\quad P_G=k^2+l^2,
                \quad P_B=l^2+\mathcal M^2,\quad P_D=1+c^2.
\tag{28}
\]
For index H, G, or B respectively, add to A
\[
 C_{10}(\delta)-1,\qquad
 l(C_{10}(\delta)-1),\qquad q_B^+(C_{10}(\delta)-1),
\tag{29}
\]
and replace the corresponding squared norm by
\[
 P_H-2kS_{11}(\delta),\qquad
 P_G-2klS_{11}(\delta),\qquad
 P_B-2l\mathcal M S_{11}(\delta).
\tag{30}
\]
These replacements have the required bound directions.
In particular the B norm increases in its second coefficient
when m/l>2/3>sin δ, so replacing m by \(\mathcal M\) is valid
before replacing sin δ by its lower polynomial.

For every resulting P let P_0=P(0,0) and define
\[
 w=\frac{[P]_{\le3}-P_0}{P_0},\qquad
 r=\rho\left[1+\frac w2-\frac{w^2}{8}+\frac{w^3}{16}\right]_{\le3}.
\tag{31}
\]
Truncation is by total degree in the native variables. The
default rational constants ρ, in H,G,B,D order, are
\[
 \begin{array}{c|cccc}
  \text{domains}&H&G&B&D\\ \hline
  TE,RE&1.203257512&1.203257512&1.451171531&1.425785990\\
  TC,RC&1.265525725&1.341857056&1.587872067&1.494987522
 \end{array}
\tag{32}
\]
At the single replaced norm in (30), replace its ρ by
\[
 \begin{array}{c|ccc}
  \text{domains}&H&G&B\\ \hline
  TE,RE&1.107155480&1.107155480&1.325511353\\
  TC,RC&1.159403846&1.232394077&1.450364739.
 \end{array}
\tag{33}
\]
No root-approximation property is used. The whole-domain
coefficient bounds below give respectively
\[
           r>.71,\quad r>1.07,\quad r>1.10,\quad r>1.03
             \qquad\text{on TE, TC, RE, RC}.
\tag{34}
\]
Thus each is a positive auxiliary in
\(\sqrt P\le(P+r^2)/(2r)\).

Finally define each of the twelve numerators by
\[
 \mathcal N
 =2A\prod_{j=H,G,B,D}r_j
       -\overline R\sum_{j=H,G,B,D}(P_j+r_j^2)
                                      \prod_{q\ne j}r_q.
\tag{35}
\]
The corresponding scalar endpoint in (21) is at least
\(\mathcal N/(2\prod r_j)\). The numerator degrees are 39
in TE and TC, and 35 in RE and RC.

## 6. Explicit coefficient conventions

The following finite formulas specify every coefficient bound
used in Section 7. Put
\[
 a_{n0}=4^{-n}\binom{2n}{n},\qquad
 a_{nj}=2\,4^{-n}\binom{2n}{n-j}\quad(1\le j\le n),
\tag{36}
\]
with zero values outside that range. Then
\(u^n=\sum_j a_{nj}T_j(2u-1)\), and |T_j|≤1 on [−1,1].
For a one-variable polynomial \(P(t)=\sum p_nt^n\) on [0,A],
let \(b_j=\sum_n p_nA^na_{nj}\). Its coefficient bounds are
\[
              b_0-\sum_{j\ge1}|b_j|\le P
                        \le b_0+\sum_{j\ge1}|b_j|.
\tag{37}
\]

For \(P(x,y)=\sum p_{ij}x^iy^j\), a triangle of side A is
covered by \(x=Au(1-v),y=Auv\), and its tensor coefficients are
\[
 b_{kl}=\sum_{ij}p_{ij}A^{i+j}a_{i+j,k}
                 \sum_{r=0}^i(-1)^r\binom ir a_{j+r,l}.
\tag{38}
\]
Use A=d for TE and A=D for TC.
For a trapezoid \(0\le x\le L,0\le y\le A+Bx\), substitute
\(x=Lu,y=(A+BLu)v\). Its tensor coefficients are
\[
 b_{kl}=\sum_{ij}p_{ij}\sum_{r=0}^j\binom jr
                      A^{j-r}B^rL^{i+r}a_{i+r,k}a_{jl}.
\tag{39}
\]
Use (A,B)=(M,−1) for RE and (D,1) for RC. In either case
the whole-domain lower and upper bounds are
\[
                  b_{00}\mp\sum_{(k,l)\ne(0,0)}|b_{kl}|.
\tag{40}
\]
These substitutions cover entire intrinsic domains; they
introduce no subdivisions.

For the one completed square below, write
\(P(d/2+u)=\sum a_ju^j\) and put
\[
        q=a_2-\sum_{j\ge3}|a_j|(d/2)^{j-2}.
\tag{41}
\]
When q>0, the whole interval |u|≤d/2 gives
\(P\ge a_0+a_1u+qu^2\ge a_0-a_1^2/(4q)\).
All quoted decimals in the following bounds are rational
outward comparisons for these explicit finite sums.

## 7. Positivity of all twelve numerators

### 7.1 The equal endpoint on the full triangle TE

Write exactly
\[
                 \mathcal N(x,y)=\mathcal N(x,0)+yH(x,y).
\tag{42}
\]
The quotient is a polynomial. The whole-triangle upper
coefficient bounds for H_y, in index order H,G,B, are
\[
                         H_y<-.67,\qquad-.51,\qquad-.44.
\tag{43}
\]
Thus \(H(x,y)\ge H(x,d-x)\). On that far edge the G and B
lower coefficient bounds are respectively .065 and .022.
For the H index, the completed square (41) gives
\[
                         q>1.33,\qquad
                         a_0-a_1^2/(4q)>.047.
\tag{44}
\]
All three far-edge quotients are therefore positive.

The base polynomial \(\mathcal N(x,0)\) is identically the
corresponding pure-T base polynomial in Section 6.1 of
the nonnegative-A/E theorem: restricting every formula
(24)--(35) to y=0 gives the same polynomial and the same
positive masses. For completeness its certificates are:

* H: the constant exceeds .001786 and the quotient after
  subtracting that constant and dividing by x exceeds .057;
* G: both chord endpoints exceed .001786 and the quotient
  above its endpoint chord, divided by x(d−x), exceeds −.00657;
* B: both chord endpoints exceed .0266 and that same chord
  quotient exceeds 1.25.

The G bound still gives
\(.001786-.00657d^2/4>.001\); all three bases exceed .001.
Together with (42)--(44), this proves TE positivity.

### 7.2 The cut endpoint on the small triangle TC

The direct whole-triangle lower coefficient bounds for
\(\mathcal N_H,\mathcal N_G,\mathcal N_B\) are respectively
\[
                             .024,\qquad .043,\qquad .306.
\tag{45}
\]
No boundary reduction is required for this domain.

### 7.3 The equal endpoint on the trapezoid RE

The whole-domain upper coefficient bounds give
\[
             (\mathcal N_H)_{xx}<-7,\qquad
             (\mathcal N_G)_{xx}<-7,\qquad
             (\mathcal N_B)_{xx}<-11.
\tag{46}
\]
At fixed y, the permitted x interval is
\([0,\min(L,M-y)]\). Concavity therefore reduces positivity
to its three intrinsic boundary curves. Their one-variable
coefficient lower bounds are:

| Index | x=0, 0≤y≤M | x=L, 0≤y≤M−L | y=M−x, 0≤x≤L |
| --- | ---: | ---: | ---: |
| H | .0013 | .0148 | .0268 |
| G | .0013 | .0148 | .0268 |
| B | .3174 | .0148 | .0260 |

Every boundary is positive, hence so is the entire trapezoid.

### 7.4 The cut endpoint on the trapezoid RC

Write \(\mathcal N(x,y)=\mathcal N(x,0)+yH(x,y)\).
The whole-trapezoid lower coefficient bounds for H are
\[
                             .90,\qquad1.23,\qquad3.64
\tag{47}
\]
in index order H,G,B. The corresponding one-variable lower
bounds for \(\mathcal N(x,0)\) on [0,L] are
\[
                             .022,\qquad.022,\qquad.021.
\tag{48}
\]
Equations (47)--(48) prove positivity on all of RC.

## 8. Conclusion

The positive masses (34) and twelve numerator certificates
prove the second endpoint in (22) strictly positive. Its first
endpoint was already proved. Concavity of each F_i then makes
every function (21) positive at the actual s, contradicting
the necessary weighted inequalities. Section 3 covered the
remaining small-total range.

The argument keeps the four actual outer circles, uses the
actual A gain and a single E support charge, and treats only
the three circle indices left by continuous concentration.
Every new scalar bound is an explicit whole-domain coefficient
sum, concavity reduction, or completed square. No state mesh,
sampled minimum, Bernstein inventory, Lean compilation, or CI
is used.
