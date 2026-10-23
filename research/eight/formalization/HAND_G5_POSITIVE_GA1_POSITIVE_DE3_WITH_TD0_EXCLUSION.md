# Positive GA1 and positive DE3 cannot coexist with HG2, BT2 and TD0

## 1. Scope and the actual inequalities

All terminating decimals below are exact rational numbers. Put
\[
 Q_1=\frac{1957767069}{500000000},\qquad R=\sqrt{Q_1},
 \qquad h=.7,\qquad a_0=\sqrt{Q_1-1/4}-1/2.
\tag{1}
\]
Use the normal signs H,A positive, B,D negative, G negative and
E nonpositive. For the unsigned sorted coordinates,
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le Q_1.
\tag{2}
\]
T may have either signed transverse coordinate \(y_T\). These
bounds hold for actual squares contained at any common ceiling
\(q\le Q_1\). No outer/core assumption is used below.

Retain the actual owners
\[
 HG2,\quad GA1,\quad AB0\text{ or }AB2,\quad
 BT2,\quad TD0,\quad DE3,\quad EH0.
\tag{3}
\]
Write their errors as
\[
 u,x,\alpha,\beta,\gamma,e,\delta,
 \qquad x,e\ge0,
\]
\[
 u+x+\alpha+\beta+\gamma+e+\delta=0,
 \qquad \sum d_i^+=\sum(-d_i)^+\le h.
\tag{4}
\]
The five ordinary errors in (4) may have arbitrary signs. Both
zero primary angles are allowed. G1 supplies the required
variation bound for an original or eligible boundary-neighbor
cycle; the proof includes the closed bounds in (4).

With \(W(v)=(1+\cos v+|\sin v|)/2\), the actual inequalities are
\[
\begin{aligned}
 a_H\sin u+b_H\cos u+b_G&\ge W(u),\\
 a_A+a_G\sin x-b_G\cos x&\ge W(x),\\
 a_B\cos\beta+b_B\sin\beta-y_T&\ge W(\beta),\\
 a_D\sin\gamma+b_D\cos\gamma+y_T&\ge W(\gamma),\\
 a_D+a_E\sin e+b_E\cos e&\ge W(e),\\
 a_H\cos\delta+b_H\sin\delta-b_E&\ge W(\delta).
\end{aligned}
\tag{5}
\]
The AB0 inequality is
\(b_A+a_B\sin\alpha+b_B\cos\alpha\ge W(\alpha)\);
AB2 is
\(a_A\sin\alpha+b_A\cos\alpha+b_B\ge W(\alpha)\).

**Theorem.** There is no system (2)--(5). In particular, a normal
positive GA1 with HG2, BT2 and arbitrary TD0 cannot retain a
nonnegative DE3 primary together with EH0. The theorem includes
both AB owners, all signs of the ordinary errors, all weak
zero-angle ties, and both radial kinds of G,T,E.

The proof changes no actual square. Its ceiling is Q1, which is
sufficient in the sharp reduction: \(q>Q_1\) already implies
\(q>q_*\).

## 2. Two positive coefficient families

Put \(t=x+e\in[0,h]\), and fix
\[
                         \lambda=1.25.
\tag{6}
\]
For \(0\le t\le.35\), use
\[
 k=1.06-.1t,\qquad l=.565+.75t,\qquad
 c=.903+.65t,\qquad g=.32.
\tag{7}
\]
For \(.35\le t\le h\), use
\[
 k=1.07-.12t,\qquad l=.77+.20t,\qquad
 c=1.13,\qquad g=.30+.05t.
\tag{8}
\]
Either family is valid at the shared endpoint. Hold these
coefficients fixed while splitting the fixed total t between x
and e. Set
\[
                         n(x)=k(\cos x+g\sin x).
\tag{9}
\]
Weight the seven actual inequalities in (3) by
\[
                         (n,k,l,c,c,1,\lambda).
\tag{10}
\]
T cancels. The G force is \(k\sin x(1,g)\), so its support is at
most \(k\sigma_g\sin x\), where
\[
                    \sigma_g=R\sqrt{1+g^2}-(1+g)/2.
\tag{11}
\]
The E force is
\[
                       (\sin e,\cos e-\lambda).
\tag{12}
\]
Its second component is nonpositive. Hence (2) gives the exact
axis upper support
\[
             a_E\sin e+b_E(\cos e-\lambda)\le a_0\sin e.
\tag{13}
\]
This is valid for either radial kind of E, including e=0.

The remaining force vectors are
\[
\begin{aligned}
 H&=(\lambda\cos\delta+n\sin u,
                       \lambda\sin\delta+n\cos u),\\
 D&=(1+c\sin\gamma,c\cos\gamma).
\end{aligned}
\tag{14}
\]
For AB0 they are
\[
 A=(k,l),\qquad
 B=(c\cos\beta+l\sin\alpha,c\sin\beta+l\cos\alpha);
\tag{15}
\]
for AB2 they are
\[
 A=(k+l\sin\alpha,l\cos\alpha),\qquad
 B=(c\cos\beta,c\sin\beta+l).
\tag{16}
\]
The four pairs at zero ordinary errors are
\[
                       (\lambda,n),(k,l),(l,c),(1,c).
\tag{17}
\]
Their complete shifted-circle supports are valid even when a
force component is negative.

## 3. Strict concavity of the complete primary split

Perform this split before maximizing the H,A,B,D supports. Keep
all ordinary errors and all actual anchor coordinates fixed.
The tangent residual
\[
                   M_H=W(u)-a_H\sin u-b_H\cos u>-.065
\tag{18}
\]
holds on the entire signed interval \(|u|\le h\). For u nonpositive
it is at least \(1-c_0>.1\), where \(c_0=\sqrt{Q_1/2}-1/2<.9\).
For u nonnegative, the sorted support in the direction
\((\sin u,\cos u)\) is its diagonal support, so
\[
 M_H\ge.5-(c_0-.5)(\sin u+\cos u)>.5-.4(1.410)>-.065.
\]
The tilt range \(.3175\le g\le.335\) in (7)--(8) gives
\[
                    \sigma_g-.5<.935,
 \qquad a_0-.5<.915.
\tag{19}
\]
For example, the first bound follows by squaring at the two
endpoints: \((1.935+g/2)^2-Q_1(1+g^2)>0\) is a concave quadratic.

After (11) and (13), the second derivative of the relaxed
weighted expression along \(e=t-x\) is at most
\[
 k\{-.5\cos x+.935\sin x\}+.065n(x)
                       -.5\cos e+.915\sin e,
\]
and thus is at most
\[
                k\{-.435\cos x+.957\sin x\}
                       -.5\cos e+.915\sin e.
\tag{20}
\]
All coefficient families satisfy \(.986\le k\le1.06\). The
value of (20) at x=0 is less than
\[
                  -.435(.986)-.5(.7648)+.915(.6443)<-.22;
\]
its value at e=0 is less than
\[
                  1.06\{-.435(.7648)+.957(.6443)\}-.5<-.199.
\]
Here \(\cos h>.7648\) and \(\sin h<.6443\). The first endpoint
expression increases with t. For the second, its bracket also
increases with t; when it is negative the assertion is immediate,
and otherwise its upper bound uses k at most 1.06.

For fixed t, (20) is a linear combination of \(\cos x,\sin x\).
After division by the positive cosine it is affine in \(\tan x\),
so its two negative endpoint values imply negativity throughout.
Its second derivative is its negative; it is therefore convex,
and its maximum is at an endpoint. Thus the full split is
strictly concave, with second derivative less than −.19.
It suffices to prove positivity at
\[
                         (x,e)=(0,t),\qquad(t,0).
\tag{21}
\]
This is a scalar endpoint reduction over the full relaxed domain,
not a motion of actual squares.

## 4. Every ordinary-angle allocation is covered

For a sorted positive pair \(a\le b\), define
\[
\begin{aligned}
 U_{a,b}(s)&=a(\cos s+\sin s-1)
 -R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\},\\
 V_{a,b}^{\nu}(s)&=\nu(\cos s-1)
 -R\{\sqrt{a^2+b^2-2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{aligned}
\tag{22}
\]
The available negative ordinary coefficients are precisely
\[
                 \nu_H=\lambda,\qquad \nu_A=l,
                 \qquad \nu_B=c,\qquad \nu_D=c.
\tag{23}
\]
In particular, k is not an available negative coefficient at A:
its GA1 angle is already the fixed nonnegative primary. Similarly,
the DE3 coefficient 1 is not available for an ordinary error at D.
H and B alone can contain a mixed positive/negative ordinary pair.
Enlarging B to a two-angle block even for AB2 is harmless.

Every ratio in (17) is at least 1/2. The one-angle A,D functions
are concave: the negative norm curvature is at most
\(C_0<.762\min(a,b)\), whereas \(\nu\ge\min(a,b)\) and
\(\cos h>.7648\). H,B use the separately concave two-angle
function with negative coefficient equal to the larger coefficient.
Consequently the continuous simplex reduction in
[the scalar-envelope note](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
applies with the actual indices (23). With
\[
                              P=h-t,\qquad N=h,
\tag{24}
\]
its alternatives are the four pure charges \(V_i(t)\), same-block
terms at H or B, and separated terms \(U_i(P)+V_j(h)\).
The positive charge uses the smaller coefficient as a valid
lower bound. This accounts for every sign allocation in (4).

### 4.1 The high family

Every ratio in (17) is at least .74. To see the only less immediate
H bound, use
\[
 n\ge.986\{.7648+.3175(.6442)\}>.74\lambda,
 \qquad n<\lambda.
\]
A,B have ratio at least \(.84/1.13>.74\), and D has ratio
\(1/1.13>.74\). The larger coefficients are all between .986
and \(\lambda=1.25\).

A same-block term minus its pure negative term is
\[
       a(\cos P+\sin P-1)-b(\cos t-\cos h)\ge0,
\tag{25}
\]
because
\(\cos(h-P)-\cos h\le\sin h(\cos P+\sin P-1)\)
and \(.74>\sin h\).
The universal positive estimate at the larger ceiling Q gives
\[
                               U_{a,b}(P)\ge-.545bP.
\tag{26}
\]
For the negative estimate, on \(0\le w\le h\),
\[
                         (V_{a,b}^{\nu})'(w)>.80b
                  \qquad(a/b\ge.74,\ \nu\le b).
\tag{27}
\]
Indeed its lower derivative increases with \(r=a/b\), so use
r=.74. Squaring the positive sides of
\[
 Rr\sqrt{1-s^2}>(s+.80)\sqrt{1+r^2-2rs}
\]
gives the cubic
\[
 \frac{1442103117461}{1250000000000}
 -\frac{4778}{3125}s
 -\frac{1654683117461}{1250000000000}s^2+\frac{37}{25}s^3.
\tag{28}
\]
Its derivative is less than −1.39 on \([0,.6443]\), and its
right endpoint exceeds .0149. Thus (27) holds throughout.
Integrating it from t to h, and using
\[
                     .80(.986)-.545(1.25)>.1075,
\tag{29}
\]
makes every separated term at least its own pure negative term
at t. Hence the four pure cases suffice on the high family.

### 4.2 The low family

Write \(V_B=V_{l,c}^{c}\). Direct bounds from (7) are
\[
\begin{gathered}
 1.025\le k\le n<\lambda,\qquad .903\le c\le1.1305,\\
 .625<l/c<.733,\qquad l/k<.81,\qquad
 c-l\ge.303,\qquad c-k\le.1055.
\end{gathered}
\tag{30}
\]
The H ratio exceeds .82, so its same-block term dominates its
pure term by (25). For B the same assertion follows from
\[
 f(t)=.625\{\cos(h-t)+\sin(h-t)-1\}-\cos t+\cos h>0
                  \qquad(0\le t\le.35).
\tag{31}
\]
For a direct check, \(f''>.058\), \(f'(.35)<-.0298\), and
\(f(.35)>.00188\). Therefore f' is negative throughout,
f decreases, and its minimum is positive.

For the separated alternatives, every negative charge at h
is at least \(V_B(h)\). Define the positive norm gain
\[
 H(a,b;s)=R\{\sqrt{a^2+b^2}-\sqrt{a^2+b^2-2ab\sin s}\}.
\tag{32}
\]
At h it increases in either coefficient whenever their ratio is
greater than \(\tan(h/2)\). This follows directly by differentiating;
for example the sign after squaring is that of
\(2r-\sin h(1+r^2)\). All coefficient paths used here have
ratio at least 1/2, greater than \(\tan(.35)\).
The following fixed radical bounds then give
\[
\begin{aligned}
 V_H(h)&\ge H(1.025,1.25;h)-1.25(1-\cos h)>.9636,\\
 V_D(h)&\ge H(1,.903;h)-1.1305(1-\cos h)>.8025,\\
 V_B(h)&\le1.131\{\cos h-1+H(.733,1;h)\}<.7857.
\end{aligned}
\tag{33}
\]
These bounds use only positive squaring and the enclosures
\(\sin h\in(.6442,.6443)\), \(\cos h\in(.7648,.7649)\).
Homogeneity and the same coefficient monotonicity justify the
last line.

For A, if \(k\ge c\), coefficient monotonicity and \(l<c\)
immediately give \(V_A(h)\ge V_B(h)\). If \(k<c\), let
\(k\le q\le c\) and r=l/q. Its negative-angle norm is at most q,
so
\[
 \partial_qH(q,l;h)
 \le R\{(1+r^2)^{-1/2}-1+r\sin h\}<.6.
\tag{34}
\]
The expression in braces increases for \(0\le r\le.81\);
its derivative is positive since
\(\sin h>.6442>r/(1+r^2)^{3/2}\).
At r=.81, use \((1+.81^2)^{-1/2}<.778\) and \(\sin h<.645\).
Consequently
\[
\begin{aligned}
 V_A(h)-V_B(h)
 &\ge(c-l)(1-\cos h)-.6(c-k)\\
 &\ge.303(.235)-.6(.1055)>.0079.
\end{aligned}
\tag{35}
\]
This proves the claimed comparison for every actual negative index.

Finally, throughout the complete low interval,
\[
                         V_B(h)-V_B(t)>.7(h-t).
\tag{36}
\]
Section 6 gives an exact degree-68 polynomial certificate.
Combining (26), (30), (33)--(36) makes each separated alternative
at least
\[
             V_B(t)+\{.7-.545(1.25)\}(h-t)
                 =V_B(t)+.01875(h-t)>V_B(t).
\tag{37}
\]
Thus the full low envelope is bounded below by the minimum of
its four actual pure charges. No comparison between the pure
A and B functions at t is needed.

## 5. The two endpoint scalar families

Put
\[
 C_g(t)=1+2\cos t+(1+2g-R\sqrt{1+g^2})\sin t.
\tag{38}
\]
The baseline at the E endpoint \((x,e)=(0,t)\) is
\[
\begin{aligned}
 B_E(t)={}&1+\tfrac12\cos t+(\tfrac12-a_0)\sin t
                  +\tfrac32\lambda+3k+2l+3c\\
 &-R\{\sqrt{\lambda^2+k^2}+\sqrt{k^2+l^2}
                        +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{aligned}
\tag{39}
\]
At the G endpoint \((x,e)=(t,0)\), it is
\[
\begin{aligned}
 B_G(t)={}&\tfrac32(1+\lambda)+2l+3c+kC_g(t)\\
 &-R\{\sqrt{\lambda^2+n(t)^2}+\sqrt{k^2+l^2}
                        +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{aligned}
\tag{40}
\]
The negative coefficients remain \((\lambda,l,c,c)\). Their
pair products are \((\lambda k,kl,lc,c)\) at E and
\((\lambda n(t),kl,lc,c)\) at G.
We prove, for each family and each \(i\in\{H,A,B,D\}\),
\[
                         B_E(t)+V_i(t)>0,
 \qquad                    B_G(t)+V_i(t)>0.
\tag{41}
\]
Section 4 makes these sixteen scalar inequalities sufficient.

## 6. Compact whole-interval polynomial certificates

Take the rational upper radii
\[
 R_+=1.978770866>R,
 \qquad A_+=1.914558470771>\sqrt{Q_1-1/4},
\tag{42}
\]
and the Taylor polynomials
\[
 S(t)=\sum_{j=0}^7\frac{(-1)^jt^{2j+1}}{(2j+1)!},
 \qquad C(t)=\sum_{j=0}^8\frac{(-1)^jt^{2j}}{(2j)!}.
\tag{43}
\]
Positive squaring proves both upper-radius assertions. On [0,h],
the errors in S,C are less than \(7\cdot10^{-18}\) and
\(3\cdot10^{-19}\), respectively.

The following are explicit rational instructions for every scalar
polynomial. Use the local variable z=t−a, with \((a,D)=(0,.35)\)
for (7) or \((a,D)=(.35,.35)\) for (8). Substitute (43) in the
coefficient families and set \(n=k(C+gS)\).
At the E endpoint use the outside part and squared norms
\[
\begin{aligned}
 A&=1+C/2+(1-A_+)S+3\lambda/2+3k+2l+3c,\\
 (v_H,v_A,v_B,v_D)&=(\lambda^2+k^2,k^2+l^2,l^2+c^2,1+c^2).
\end{aligned}
\tag{44}
\]
At G use
\[
\begin{aligned}
 A&=3(1+\lambda)/2+2l+3c+k\{1+2C+(1+2g)S\},\\
 (v_H,v_A,v_B,v_D)&=(\lambda^2+n^2,k^2+l^2,l^2+c^2,1+c^2),
\end{aligned}
\tag{45}
\]
and include the extra squared norm \(1+g^2\) with weight kS.
The four anchor norms have weight 1.
For the negative index i, add \(\nu_i(C-1)\) to A and replace
\[
                         v_i\longmapsto v_i-2b_iS,
\tag{46}
\]
where \(\nu_i\) is (23) and \(b_i\) is its pair product after
(40). The unperturbed norm cancels exactly, so every remaining
radical has a nonpositive coefficient.

For each resulting polynomial v, let \(v_0=v(0)>0\), and define
\[
 \rho_0=1,\qquad \rho_{j+1}=(\rho_j+v_0/\rho_j)/2
                  \quad(j=0,1,2),
\]
\[
 w=([v]_{\le3}-v_0)/v_0,\qquad
 m_v=[\rho_3(1+w/2-w^2/8+w^3/16)]_{\le3}.
\tag{47}
\]
Truncation is in z. These are explicit rational polynomials;
no fitted root value occurs. For the resulting squared norms and
nonnegative weights \((v_j,w_j)\), form
\[
 P=2A\prod_jm_{v_j}
       -R_+\sum_jw_j(v_j+m_{v_j}^2)\prod_{r\ne j}m_{v_r}.
\tag{48}
\]
Every mass is positive. The identity
\[
       \frac{v+m^2}{2m}-\sqrt v
                    =\frac{(\sqrt v-m)^2}{2m}\ge0
\tag{49}
\]
makes \(P/(2\prod m_{v_j})\) a lower scalar bound, before the
Taylor error. It is valid for every positive mass.

For any rational polynomial \(p(z)=\sum a_nz^n\) on [0,D], put
\[
 B_0=\sum_na_n\frac{D^n}{4^n}\binom{2n}{n},\qquad
 B_j=2\sum_{n\ge j}a_n\frac{D^n}{4^n}\binom{2n}{n-j}\quad(j\ge1),
\]
\[
                         \mathcal L_D(p)=B_0-\sum_{j\ge1}|B_j|.
\tag{50}
\]
The identity \(p(z)=\sum B_jT_j(2z/D-1)\), with \(|T_j|\le1\),
gives \(p\ge\mathcal L_D(p)\) on the entire interval.

For the low family, use the exact identity
\[
                         P(z)=P(0)+z\,\frac{P(z)-P(0)}z.
\tag{51}
\]
The rational constants satisfy \(P_E(0)>.0009336\) and
\(P_G(0)>.0009802\), for each negative index. Formula (50)
gives the following whole-interval lower bounds on the first
quotient in (51), or on P itself for the high family:

| Family and certified expression | Endpoint | H | A | B | D |
|---|---|---:|---:|---:|---:|
| [0,.35], first quotient | E | 2.1983 | .4051 | .2381 | 1.6817 |
| [0,.35], first quotient | G | 2.7808 | .4731 | .3421 | 1.8390 |
| [.35,.7], numerator P | E | .5926 | .1425 | .1345 | .5620 |
| [.35,.7], numerator P | G | .5368 | .1569 | .1484 | .5974 |

These are coefficient-norm bounds on complete intervals. The
maximum degree is 46. The same rule proves that every mass is
greater than 1.049 on the low family and greater than .802 on the
high family, and every mass is less than 3. Keeping these masses
fixed, all partial derivatives of (48) in its sine/cosine inputs
are less than \(10^7\): there are at most five masses, \(|A|<30\),
\(|v_j|<5\), \(|w_j|<2\), and input partials at most 30.
The substitution error is therefore less than \(10^{-8}\), below
every displayed positive reserve. This proves (41).

Here is the additional certificate for the low chord (36). Set
\[
 s_L=S(h),\qquad
 c_L=\sum_{j=0}^7\frac{(-1)^jh^{2j}}{(2j)!},\qquad
 S_+(t)=\sum_{j=0}^6\frac{(-1)^jt^{2j+1}}{(2j+1)!},
\]
\[
\begin{aligned}
 v_h&=l^2+c^2-2lc s_L,\\
 d&=2lc\{s_L-S_+(t)\},\\
 A_0&=.7(h-t)+c\{C(t)-c_L\},\\
 B_0&=Q_1d-A_0^2,\\
 P_0&=B_0^2-4Q_1A_0^2v_h.
\end{aligned}
\tag{52}
\]
The alternating Taylor directions make d a lower bound for the
actual norm-square difference; \(v_h,A_0\) are upper bounds for
their respective positive quantities. Formula (50), applied once
on the complete interval [0,.35], gives
\[
                   A_0>.4422,\qquad B_0>2.0115,
                   \qquad P_0>.6127.
\tag{53}
\]
The degree of P0 is 68. Two positive-sided squarings now give
(36): first \(B_0>2R A_0\sqrt{v_h}\), then
\(R(\sqrt{v_h+d}-\sqrt{v_h})>A_0\). The stated Taylor directions
preserve both strict inequalities for the actual quantities.

## 7. The exact endpoint interface

Sections 4--6 make both endpoint weighted expressions in (21)
strictly positive for every allowed allocation of ordinary errors
and every sorted contained anchor. Section 3 then makes the
expression strictly positive at the original split (x,e).
The actual inequalities (5) and the positive weights (10) require
it to be nonpositive. This contradiction proves the theorem.

The result covers the complete sole nonnegative-DE3/EH0 endpoint
with positive GA1, including outer E and arbitrarily small primary
angles. Together with
[the EH1/DE2 companion](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md),
it closes both sole-primary E endpoints for the stated BT2/TD0
regime. A DE3/EH1 pair, or a primary TD2/BT3 witness, still requires
its separate finite join. No equality claim is inferred from a
modified intermediate square; this proof changes none.

All numerical assertions above are rational polynomial identities,
positive-sided radical comparisons, or coefficient bounds on whole
continuous intervals. Sampled states, optimizer output, state meshes,
Lean compilation and CI are not proof premises.
