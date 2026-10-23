# The exceptional aligned-E contact with a positive T primary: the sharp strip

## 1. Full signed domain and conclusion

Set
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,\qquad h=.7.
\tag{1}
\]
Every decimal in this note is an exact rational. Let
\(q_*\in(q_L,Q_1)\) be the sharp hard-chain radius parameter from
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md),
and put \(R=\sqrt{q_*}\).

Consider sorted squares contained at a common ceiling \(q\le q_*\).
The anchor signs are H,A positive and B,D negative; G,T have arbitrary
signs and radial kinds. E has signed tangent \(y_E\ge0\), either radial
kind, and the actual owners include
\[
 HG2,\quad GA1,\quad AB0\text{ or }AB2,\quad DE3,\quad EH0.
\tag{2}
\]
Write the GA1 and DE3 errors as \(x,e\ge0\). EH0 is aligned and has
the exact actual contact
\[
                         a_H+y_E=1.
\tag{3}
\]
Retain either of the following actual T regimes:
\[
 \begin{array}{c|c|c}
 &\text{owners}&\text{nonnegative primary error}\\ \hline
 \mathrm{TD}&BT2,TD2&z=d_{TD}\ge0\\
 \mathrm{BT}&BT3,TD0&z=d_{BT}\ge0.
 \end{array}
\tag{4}
\]
All remaining errors are arbitrary. Their sum is \(-t\), where
\[
                 t=x+e+z\in[.1,.16],
\tag{5}
\]
and the positive and negative variations of the complete cyclic
error list are at most h.

**Theorem.** Under (1)--(5), \(x=z=0\). Thus neither a positive GA1
nor a positive T primary survives this exceptional contact in the
critical strip. All ordinary error signs, both AB owners, arbitrary
G/T signs, and weak owner ties are included. The theorem preserves
the genuine hard-chain zero at \(x=z=0\).

The proof uses a stress on the actual witnesses. Its relaxed scalar
endpoints are not asserted to be feasible packings, and no change of
the original radius or of an actual owner is used.

## 2. The exact supporting dual and a small adaptation

For the given t, use the exact supporting chain and dual
\((k_0,l_0,c_0,\eta)\) from Sections 2 and 7 of
[the exceptional-E critical theorem](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_SHARP_CRITICAL_STRIP.md).
For clarity, their complete definitions are
\[
\begin{aligned}
 r&=\sqrt{q_*-u_0^2},&U&=\sqrt{q_*-(2-u_0)^2},\\
 V&=3-U,&Y&=\sqrt{q_*-V^2},\\
 v&=2-Y,&w&=\sqrt{q_*-v^2},\\
 k_1&=2-\cos t(r-1)+\sin t\,u_0,&
 k_2&=1+\cos t\,v-\sin t(w-1),\\
 \eta&=v/w,&\lambda&=\cos t+\eta\sin t,\\
 k_0&=\lambda V/Y,&l_0&=k_0(2-u_0)/U,&c_0&=k_1/k_2.
\end{aligned}
\tag{6}
\]
Here \(u_0\) is the unique position minimizer of
\(k_1^2+k_2^2-q_*\) at t. The cited whole-strip proof gives
\[
\begin{gathered}
 .998-.635t<u_0<1.002-.64t,\qquad .27<\eta<.31,\\
 1<\lambda<1.04,\qquad .925<k_0<.985,\qquad .925<c_0<1,\\
 l_0<.67,\quad l_0/k_0<.675,\quad .63<l_0/c_0<.68,\\
 c_0-k_0<.02,\qquad c_0-l_0>.296.
\end{gathered}
\tag{7}
\]
Adapt the weights to the actual positive T angle by
\[
 k=k_0+.06z,\qquad l=l_0-.23z,\qquad c=c_0-.53z.
\tag{8}
\]
For fixed t,z these weights and \(\eta\) remain fixed. Define
\[
 f(s)=\cos s+\eta\sin s,\qquad
 n=kf(x),\quad p=f(e),\quad m=cf(z).
\tag{9}
\]
Since \(0\le s\le t\le.16\), \(f'(s)>.106\), and consequently
\(1\le f(s)\le\lambda<1.04\). The following useful ranges follow
directly from (7)--(9):
\[
\begin{gathered}
 .925<k<.995<1,\quad .8402<c\le m\le c_0<1,\quad l<.67,\\
 l/k<.675,\qquad .61<l/m<1,\qquad l/c<.71,\\
 m-k<.02,\qquad m-l>.248.
\end{gathered}
\tag{10}
\]
Indeed \(m'(z)=-.53f(z)+cf'(z)<-.22\), with t and the original
dual fixed. Thus \(m\le c_0-.22z\), and
\[
\begin{aligned}
 l-.61m&>.02(.925)-(.23-.61(.22))(.16)>.003,\\
 .71c-l&>.03(.925)-(.71(.53)-.23)(.16)>.004,\\
 m-l&\ge c-l>.296-.30(.16)=.248.
\end{aligned}
\tag{11}
\]

## 3. Actual stress and reduction of the G/E split

Weight HG,GA,AB,DE,EH by \((n,k,l,1,p)\). In the TD regime use
\((BT,TD)=(m,c)\); in the BT regime use \((BT,TD)=(c,m)\).
The G and T forces are, respectively,
\[
 k\sin x\{a_G+\eta(-y_G)\},\qquad
 c\sin z\{a_T\mp\eta y_T\},
\tag{12}
\]
where the minus sign applies to TD and the plus sign to BT.
For either sign of each intermediate square, their circle supports
are bounded by \(k\sigma_\eta\sin x\) and
\(c\sigma_\eta\sin z\), where
\[
             \sigma_\eta=R\sqrt{1+\eta^2}-(1+\eta)/2.
\tag{13}
\]
The E force is \(\sin e(a_E+\eta y_E)\). The zero-error pairs are
\[
\begin{array}{c|cccc|c}
 &H&A&B&D&\text{actual negative coefficients}\\ \hline
 \mathrm{TD}&(p,n)&(k,l)&(l,m)&(1,c)&(n,l,m,c)\\
 \mathrm{BT}&(p,n)&(k,l)&(l,c)&(1,m)&(n,l,l,m).
\end{array}
\tag{14}
\]
Only B in the TD row can have two ordinary angular arguments.
Every other block has at most one. D has no ordinary argument in
the TD row; retaining its zero block as an additional possible
single-angle block only enlarges the scalar relaxation. Likewise
the unused A or B block for a particular AB choice can be retained
at zero. No extra actual separation witness is asserted.

Fix t,z and split \(x+e=t-z\) before maximizing anchor supports.
The changing EH coefficient multiplies exactly zero by (3). The
ordinary H residual is greater than \(-.065\), as in the cited
critical theorem. Keeping E's actual coordinates, with
\(y_E\ge0\) and \(a_E-.5<.915\), gives the split second derivative
upper bound
\[
 k\{-.435\cos x+.956\sin x\}-.5\cos e+.915\sin e<-.60.
\tag{15}
\]
For the final inequality it suffices to replace both cosines by
\(\cos(.16)\), both sines by \(\sin(.16)\), and k by .925 in
the resulting negative G term. The T force and all its weights are
constant during this split. Hence only the two full faces
\[
 \mathrm{ET}:x=0, e=t-z,\qquad
 \mathrm{GT}:x=t-z, e=0
\tag{16}
\]
need to be checked; every interior G/E split is strictly stronger
than the chord of these endpoint stresses.

## 4. A common ordinary-angle envelope

Use
\[
\begin{aligned}
 H_{a,b}(s)&=R\{\sqrt{a^2+b^2}-\sqrt{a^2+b^2-2ab\sin s}\},\\
 V_{a,b}^{\nu}(s)&=H_{a,b}(s)+\nu(\cos s-1),\\
 U_{a,b}(s)&=\min(a,b)(\cos s+\sin s-1)\\
 &\hspace{12mm}-R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{aligned}
\tag{17}
\]
The complete ordinary-angle contribution in either row of (14),
on either face (16), is at least the same charge
\[
                         V_B(t):=V_{l,m}^{m}(t).
\tag{18}
\]
Here and below the parameters k,l,c,m are held fixed when an
ordinary angle is varied.

To prove (18), apply the separately concave concentration from
[the scalar-envelope theorem](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
All ratios in (14) exceed one half. Single-angle blocks have
negative coefficient at least their smaller coefficient, and
the only mixed block is B in the TD regime, with its larger
negative coefficient m. Thus the possible minima are pure
negative charges at t, the same-block B saturation, and separated
terms \(U_i(h-t)+V_j(h)\).

### 4.1 Pure and far charges in the TD row

H and D have both coefficients at least .8402, one at least 1,
and negative coefficient below 1.04. Coordinate monotonicity of
the norm gain on these balanced rectangles gives
\[
 V_H(t),V_D(t)>1.184t,
 \qquad V_H(h),V_D(h)>.777.
\tag{19}
\]
By concavity and its initial slope,
\[
                         V_B(t)<1.102t,
 \qquad V_B(h)<.671.
\tag{20}
\]
For the far upper bound first increase l to .67, then m to 1
in the norm gain, and use \(m>.8402\) in its negative cosine
term. The second coordinate increase is legitimate because
the intermediate ratio is then at least .67, exceeding \(\sin h\).

If \(m\le k\), the A charge dominates B by monotonicity of H
and its smaller negative coefficient. All ratios on the intervening
coefficient segment exceed one half; the required monotonicity
follows by squaring the derivative comparison and using
\(\sin h<.8\le2r/(1+r^2)\) for \(1/2\le r\le1\).
Otherwise, for
\(k\le b\le m\) the ratio \(l/b<.675\), and
\[
                  \partial_b H_{l,b}(t)<.5t,
 \qquad \partial_b H_{l,b}(h)<1.
\tag{21}
\]
These follow by integrating
\[
 \partial_b H_{l,b}(s)
 =\int_0^s
 \frac{R(l/b)^2(l/b-\sin a)\cos a}
      {\{1+(l/b)^2-2(l/b)\sin a\}^{3/2}}\,da.
\tag{22}
\]
For the first bound one may replace the numerator ratio by
\(.675^3\), the sine in the denominator by .16, and use positive
squaring. The far bound also follows from the elementary global
estimate \(\partial_bH_{l,b}(h)\le R(l/b)\sin h<1\).
Consequently
\[
\begin{aligned}
 V_A(t)-V_B(t)&>.248(1-\cos t)-.5(.02)t>0,\\
 V_A(h)-V_B(h)&>.248(1-\cos h)-.02>.038.
\end{aligned}
\tag{23}
\]
The near inequality uses
\((1-\cos t)/t\ge .1/2-.1^3/24\) on the strip.

### 4.2 The BT row also dominates the canonical B charge

The H,A,D estimates just established apply unchanged. For B,
write \(\Delta=m-c\ge0\). On \(c\le b\le m\), (10) gives
\(l/b<.71\). The integrand in (22) is uniformly below .4.
One convenient exact proof maximizes its factor without the
cosine over the sine argument: for \(0<r<1\),
\[
 \frac{r^2(r-s)}{(1+r^2-2rs)^{3/2}}
 \le\frac{r}{3\sqrt3\sqrt{1-r^2}}
 \quad(s<r),
\tag{24}
\]
and it is nonpositive when \(s\ge r\). Positive squaring at
\(r=.71\) gives \(Rr/(3\sqrt3\sqrt{1-r^2})<.4\).
Therefore
\[
 V_{l,c}^{l}(a)-V_{l,m}^{m}(a)
 \ge(m-l)(1-\cos a)-.4a\Delta.
\tag{25}
\]
Here \(\Delta\le.31z\), with strictness when z>0, and
\(m-l>.296-.30z+\Delta\). For \(a=t\), the coefficient
\(1-\cos t-.4t\) is negative, so (25) is at least
\[
 (.296+.01z)(1-\cos t)-.124tz
 >t^2\{.296(1/2-.16^2/24)-.124\}>.023t^2.
\tag{26}
\]
For \(a=h\), (25) is greater than
\(.248(1-\cos h)-.4h(.31)(.16)>.044\).
Thus the BT B charge dominates the same canonical charge both
at t and at h.

### 4.3 Same-block and separated endpoints

The TD same-block B charge exceeds its pure charge because
\[
 .61\{\cos(h-t)+\sin(h-t)-1\}-\cos t+\cos h>.004.
\tag{27}
\]
This function has positive second derivative on [.1,.16],
negative first derivative at .16, and the displayed positive
value at .16. There is no mixed block in the BT row.

Every positive charge satisfies \(U_i(P)\ge-.545(1.04)P\).
All far negative charges dominate \(V_B(h)\) by (19)--(26).
Monotonicity of the fixed-ratio derivative and the scale bounds
\(l/m>.61\), \(m>.8402\) give
\[
 V_B(h)-V_B(t)
 >.8402\{V_{.61,1}^{1}(h)-V_{.61,1}^{1}(t)\}
 >.8402(.75)(h-t).
\tag{28}
\]
The last brace is evaluated with radius \(\sqrt{q_L}\).
After subtracting \(.75(h-t)\), its derivative is negative
throughout [.1,.16] and its value at .16 is greater than .005;
positive radical squaring verifies both bounds. Since
\(.8402(.75)-.545(1.04)>.063\), every separated endpoint
also exceeds the pure charge. This proves (18) for both regimes,
including all ordinary sign patterns and ties.

## 5. The GT face and the BT regime are stronger

Put
\[
 C_\eta(s)=1+2\cos s+
                 \{1+2\eta-R\sqrt{1+\eta^2}\}\sin s.
\tag{29}
\]
At fixed t,z let \(a=t-z\). The GT baseline minus the ET
baseline, in either T regime, is exactly
\[
 (1-k)(3-C_\eta(a))
 +R\{\sqrt{f(a)^2+k^2}-\sqrt{1+k^2f(a)^2}\}\ge0.
\tag{30}
\]
It is strictly positive when \(a>0\), because k<1,
\(f(a)>1\), and \(C_\eta(a)<3\). The last claim follows
from \(1+2\eta-R\sqrt{1+\eta^2}<0\), checked by squaring
at the endpoint \(\eta=.31\) and radius \(\sqrt{q_L}\).

On either face, the BT baseline minus the TD baseline is
\[
 R\{\sqrt{l^2+m^2}-\sqrt{1+m^2}
               -\sqrt{l^2+c^2}+\sqrt{1+c^2}\}\ge0,
\tag{31}
\]
since \(m\ge c\) and
\(b\mapsto\sqrt{l^2+b^2}-\sqrt{1+b^2}\) increases for l<1.
Their common ordinary lower bound (18) is identical.
It therefore remains only to prove the ET/TD scalar is
nonnegative, strictly so when z>0.

## 6. The adapted ET scalar increases from the exact hard zero

Write \(a=t-z\), \(p=f(a)\), \(m=cf(z)\). After cancelling
the unshifted B norm against (18), the ET/TD scalar is
\[
\begin{aligned}
 S(t,z)={}&3k+2l+cC_\eta(z)+C_\eta(t-z)+m(\cos t-1)\\
 &-R\{\sqrt{p^2+k^2}+\sqrt{k^2+l^2}
       +\sqrt{l^2+m^2-2lm\sin t}+\sqrt{1+c^2}\}.
\end{aligned}
\tag{32}
\]
Section 7 proves the uniform whole-triangle inequality
\[
                \partial_zS(t,z)>.0018
       \qquad(.1\le t\le.16,\ 0\le z\le t).
\tag{33}
\]
At z=0 the adaptation disappears. The exact supporting-chain
identity from Section 5 of the original critical theorem gives
\[
 S(t,0)=N(N-R)/k_2\ge0,
 \qquad N=\sqrt{k_1^2+k_2^2}.
\tag{34}
\]
Hence \(S(t,z)>.0018z\) for z>0. Equations (18), (30),
and (31) exclude z>0 on both faces and in both T regimes.
If z=0 and x>0, (30) is strict at the GT face, while the
strict split concavity (15) excludes every interior G/E split.
The only remaining possibility is x=z=0, as claimed.

## 7. One exact whole-domain derivative certificate

This section specifies a single rational polynomial calculation
for (33). It uses no angle subdivision, sampled premise, or
stored inventory of coefficient rows.

### 7.1 The differentiated expression

Set \(A=1+2\eta-R\sqrt{1+\eta^2}\),
\(C'(s)=-2\sin s+A\cos s\), and use the constants
\[
 a_k=.06,\qquad a_l=-.23,\qquad a_c=-.53.
\]
With t fixed, define
\[
\begin{aligned}
 p'&=\sin(t-z)-\eta\cos(t-z),\\
 m'&=a_cf(z)+c\{-\sin z+\eta\cos z\},\\
 N_H^2&=p^2+k^2,&N_A^2&=k^2+l^2,\\
 N_B^2&=l^2+m^2-2lm\sin t,&N_D^2&=1+c^2.
\end{aligned}
\tag{35}
\]
The exact derivative to be enclosed is
\[
\begin{aligned}
 D={}&3a_k+2a_l+a_cC_\eta(z)+cC'(z)-C'(t-z)
                         +m'(\cos t-1)\\
 &-R\left\{
 \frac{pp'+ka_k}{N_H}+\frac{ka_k+la_l}{N_A}
 +\frac{la_l+mm'-(a_lm+lm')\sin t}{N_B}
 +\frac{ca_c}{N_D}\right\}.
\end{aligned}
\tag{36}
\]

### 7.2 Rational polynomial arithmetic with a uniform remainder

On \((X,Y)\in[-1,1]^2\) put
\[
 t=.13+.03X,\qquad z=t(1+Y)/2.
\tag{37}
\]
A model \([P,E]\), with P a rational polynomial of total degree
at most 10 and \(E\ge0\), encloses its quantity within E
uniformly on this entire square. Write
\(\|P\|_1=\sum_{i,j}|P_{ij}|\).
Addition adds the polynomials and errors. Multiplication forms
PQ, discards all terms of total degree above 10, and adds their
coefficient norm to
\[
                  E\|Q\|_1+F\|P\|_1+EF.
\tag{38}
\]
Whenever a model is constructed, including constant models and
the results of primitive addition, negation, or multiplication,
round every retained coefficient to the nearest multiple of
\(10^{-24}\), charging the sum of all absolute rounding losses
to the error. Round the error upward to a multiple of
\(10^{-20}\). Ties can be rounded toward positive infinity.
Division by a fixed rational is scalar multiplication under
the same rule. These rounding steps only enlarge enclosures.

Use the Taylor polynomials
\[
 \sin b=\sum_{j=0}^6\frac{(-1)^jb^{2j+1}}{(2j+1)!}
          +[-\epsilon_s,\epsilon_s],\quad
 \cos b=\sum_{j=0}^7\frac{(-1)^jb^{2j}}{(2j)!}
          +[-\epsilon_c,\epsilon_c],
\tag{39}
\]
where \(\epsilon_s=.7^{15}/15!\),
\(\epsilon_c=.7^{16}/16!\). The operations in (38) include
the discarded polynomial terms. This conservative remainder
works for every argument in (36), all of which lie in [0,.16].

For \(v^\alpha\), where \(\alpha\in\{1/2,-1/2,-1\}\),
take the constant coefficient of the input model. If
\(\alpha=\pm1/2\), let \(\rho\) be its square root rounded
to the nearest multiple of \(10^{-10}\), using rational
squares to decide the rounding, and put \(b=\rho^2\).
If \(\alpha=-1\), let b be that constant coefficient itself.
Form the model \(W=v/b-1\), and set \(s=\|W_P\|_1+W_E\).
In every occurrence below,
\[
                               s<.095.
\tag{40}
\]
Evaluate, by Horner's rule and (38),
\[
 b^\alpha\sum_{j=0}^{12}\binom\alpha j W^j.
\tag{41}
\]
Here \(b^{1/2}=\rho\), \(b^{-1/2}=1/\rho\), and
\(b^{-1}=1/b\) are rational. Before multiplication by that
factor, add the uniform error
\[
              \left|\binom\alpha{13}\right|
                            \frac{s^{13}}{1-s}.
\tag{42}
\]
The binomial coefficients after index 13 have nonincreasing
absolute values for all three exponents, so (42) bounds the
entire convergent tail. This also proves positivity of every
radicand or reciprocal denominator to which the rule is applied.

### 7.3 The complete polynomial builder and its rational bound

Start the chain (6) from the following two models:
\[
 q_*\ \longmapsto\left[\frac{q_L+Q_1}{2},\frac{Q_1-q_L}{2}\right],
 \qquad
 u_0\ \longmapsto[1-.6375t,.00175].
\tag{43}
\]
The second model follows from (7), since the half-width
\(.002-.0025t\) is at most .00175. The models allow every
q,u in these enclosures independently, which is stronger
than only enclosing the stationary chain.

Construct r,U,V,Y,v,w in exactly the displayed order in (6),
using (41) for each square root. Construct \(\sin t,\cos t\)
by (39), then \(k_1,k_2,\eta,\lambda,k_0,l_0,c_0\) from (6),
using (41) with exponent -1 for reciprocals. Apply (8), form
the sine and cosine models at z and t-z, and substitute them
in (35)--(36). Use exponent -1/2 for the four displayed
reciprocal norms, and exponent 1/2 for R and
\(\sqrt{1+\eta^2}\). All products and sums use (38).
The resulting model \([P,E]\) has total degree 10 and 66
potential monomials. Exact rational coefficient addition gives
\[
\begin{gathered}
 P_{00}>.04183,\qquad
 \sum_{(i,j)\ne(0,0)}|P_{ij}|<.01946,\qquad E<.02053,\\
 P_{00}-\sum_{(i,j)\ne(0,0)}|P_{ij}|-E>.0018.
\end{gathered}
\tag{44}
\]
These are full-square coefficient inequalities for the explicitly
specified polynomial, not values at angle samples. For orientation,
the respective exact rational quantities begin
\(.04184009676032266\), \(.01945325611302902\),
\(.02052047636025025\), and \(.00186636428704339\).
The rational bounds in (44), rather than these decimal displays,
are the certificate. Since \(|X|,|Y|\le1\), (44) proves
\(D>.0018\) on the whole triangle (37), completing (33).

All auxiliary constants used in Sections 2--5 follow from the
same rational sine/cosine polynomials and positive radical
squares. In particular the angular chord has reserve greater
than .005, the same-block endpoint greater than .004, and the
primary split is below -.60. The only new derivative calculation
is the one explicit whole-domain model (35)--(44).
