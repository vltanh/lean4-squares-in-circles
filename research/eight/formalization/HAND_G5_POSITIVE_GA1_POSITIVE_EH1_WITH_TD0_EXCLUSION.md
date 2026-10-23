# Positive GA1 and positive EH1 cannot coexist with HG2, BT2 and TD0

## 1. Exact scope and actual projections

All terminating decimals below are exact rational numbers. Put
\[
 Q_1=\frac{1957767069}{500000000},\qquad R=\sqrt{Q_1},
 \qquad h=.7,\qquad
 a_0=\sqrt{Q_1-1/4}-1/2,\quad c_0=\sqrt{Q_1/2}-1/2.
\tag{1}
\]
Work with the normal signs H,A positive, B,D negative, G negative,
and E nonpositive. Write their sorted unsigned coordinates as
\(a_i\ge b_i\ge0\). Every actual square is contained at a common
ceiling \(q\le Q_1\); in particular
\[
 (a_i+1/2)^2+(b_i+1/2)^2\le Q_1.
\tag{2}
\]
T can have either sign, with signed transverse coordinate \(y_T\).
No outer/core assumption is needed in the proof, so in particular
it applies when E is outer and H,A,B,D are the original outer anchors.

Retain actual witnesses
\[
 HG2,\quad GA1,\quad AB0\text{ or }AB2,\quad
 BT2,\quad TD0,\quad DE2,\quad EH1.
\tag{3}
\]
Let their errors in cyclic order be
\[
 u,x,\alpha,\beta,\gamma,\delta,e,
 \qquad x,e\ge0,
\]
\[
 u+x+\alpha+\beta+\gamma+\delta+e=0,
 \qquad \sum d_i^+=\sum(-d_i)^+\le h.
\tag{4}
\]
The G1 consequence for an original or eligible boundary-neighbor
cycle supplies (4), with strict variation bounds. We prove the
contradiction even with the closed bounds displayed here.

With \(W(t)=(1+\cos t+|\sin t|)/2\), the projections used are
\[
\begin{aligned}
 a_H\sin u+b_H\cos u+b_G&\ge W(u),\\
 a_A+a_G\sin x-b_G\cos x&\ge W(x),\\
 a_B\cos\beta+b_B\sin\beta-y_T&\ge W(\beta),\\
 a_D\sin\gamma+b_D\cos\gamma+y_T&\ge W(\gamma),\\
 a_D\cos\delta+b_D\sin\delta+b_E&\ge W(\delta),\\
 a_H+a_E\sin e-b_E\cos e&\ge W(e).
\end{aligned}
\tag{5}
\]
AB0 is \(b_A+a_B\sin\alpha+b_B\cos\alpha\ge W(\alpha)\);
AB2 is \(a_A\sin\alpha+b_A\cos\alpha+b_B\ge W(\alpha)\).
These are actual witnesses; no owner conversion is made.

**Theorem.** There is no system (2)--(5). Consequently a normal
positive GA1 with HG2, BT2 and arbitrary TD0 cannot have a retained
nonnegative EH1 primary and DE2. This includes all weak zero-angle
ties, all individual signs of the five ordinary errors, both AB
owners and either radial kind of G,T,E.

The proof is a positive weighted sum of (5), followed by exact
support and continuous angle inequalities. Its ceiling is Q1,
which suffices for the final sharp reduction because \(q>Q_1\)
already gives \(q>q_*\).

## 2. Three coefficient families

Set \(t=x+e\in[0,h]\). On \(0\le t\le.2\), use
\[
\begin{aligned}
 k&=.86265+.55t+.3t^2,& c&=k+.3t,\\
 l&=.50521+.823t+.7t^2,&g&=.32,\\
 \eta&=.262+.267t+.1t^2.
\end{aligned}
\tag{6}
\]
On \(.2\le t\le.35\), put \(z=t-.2\) and use
\[
\begin{aligned}
 k&=.983+.10z-.3z^2,& c&=1.045+.65z-1.5z^2,\\
 l&=.698+.9z-z^2,&g&=.31,&\eta&=.319+.2z.
\end{aligned}
\tag{7}
\]
On \(.35\le t\le h\), use
\[
 k=1.017-.02t,\qquad c=1.13,\qquad
 l=.70+.36t,\qquad g=.27+.08t.
\tag{8}
\]
The choices on a shared endpoint need not agree: either positive
stress is valid there. All coefficients are held fixed while
splitting the fixed total t between x and e.

In every family put
\[
 n(x)=k(\cos x+g\sin x).
\tag{9}
\]
For (6)--(7), put
\[
 p(e)=\cos e+\eta\sin e,
\tag{10}
\]
and weight the seven actual inequalities by
\[
                    (n,k,l,c,c,p,1).
\tag{11}
\]
The G and E force vectors are respectively
\[
 k\sin x\,(1,g),\qquad \sin e\,(1,\eta),
\tag{12}
\]
and T cancels. Thus the shifted-circle bound gives their supports
\(k\sigma_g\sin x\) and \(\sigma_\eta\sin e\), where
\[
 \sigma_v=R\sqrt{1+v^2}-(1+v)/2.
\tag{13}
\]
For (8), use p=1 in (11). The E force is then
\((\sin e,1-\cos e)\); its complete-circle support is
\[
 2R\sin(e/2)-\tfrac12(\sin e+1-\cos e).
\tag{14}
\]
The support bound is valid at e=0 as well.

The four remaining force vectors are
\[
\begin{aligned}
 H&=(1+n\sin u,n\cos u),\\
 D&=(p\cos\delta+c\sin\gamma,
                         p\sin\delta+c\cos\gamma).
\end{aligned}
\tag{15}
\]
For AB0,
\[
 A=(k,l),\qquad
 B=(c\cos\beta+l\sin\alpha,
                         c\sin\beta+l\cos\alpha);
\tag{16}
\]
for AB2,
\[
 A=(k+l\sin\alpha,l\cos\alpha),\qquad
 B=(c\cos\beta,c\sin\beta+l).
\tag{17}
\]
The four pairs at zero ordinary errors are therefore
\[
                    (1,n),(k,l),(l,c),(p,c).
\tag{18}
\]

## 3. The fixed-total split is strictly concave

We first perform this split before maximizing the H,A,B,D supports.
This avoids assuming that a substituted contact state is an actual
packing. The ordinary errors and the sorted anchor coordinates
are fixed in this calculation; their total remains \(-t\).

For every sorted contained H and every \(|u|\le h\),
\[
 M_H=W(u)-a_H\sin u-b_H\cos u>-.065.
\tag{19}
\]
For u nonpositive, it is at least \(1-c_0>.1\). For u nonnegative,
the sorted support in the direction \((\sin u,\cos u)\) is the
diagonal support, and
\[
 M_H\ge\tfrac12-(c_0-\tfrac12)(\sin u+\cos u)
       >.5-.4(1.410)>-.065.
\]
Similarly, the radial residual at D satisfies
\[
 M_D=W(\delta)-a_D\cos\delta-b_D\sin\delta>-.415.
\tag{20}
\]
For a nonpositive error this follows from \(a_D\le a_0<1.415\).
For \(0\le\delta\le1/4\), the circle optimizer is on the axis:
\(\sin\delta<1/(2R)\). The axis expression increases from
\(1-a_0\). For \(1/4\le\delta\le h\), the complete-circle bound
instead gives \(M_D\ge.5+\sin\delta+\cos\delta-R>-.264\).
This proves (20) on the entire signed interval.

Throughout the tilt ranges in (6)--(8),
\[
                         \sigma_g-\tfrac12<.935,
 \qquad \sigma_\eta-\tfrac12<.935.
\tag{21}
\]
For (6)--(7), the second derivative of the relaxed weighted
expression along \(e=t-x\), using (12), is at most
\[
 k\{-\tfrac12\cos x+.935\sin x\}
 +\{-\tfrac12\cos e+.935\sin e\}
 +.065n(x)+.415p(e).
\tag{22}
\]
Here \(.862<k<1\), \(g\le.32\), \(\eta\le.35\), and \(t\le.35\).
Hence (22) is bounded above by
\[
 k\{-.435\cos x+.956\sin x\}
                 -.085\cos e+1.081\sin e.
\tag{23}
\]
At x=0, using \(\cos .35>.9393\), \(\sin .35<.343\),
this is less than
\[
              -.435(.862)-.085(.9393)+1.081(.343)<-.084.
\]
At x=t it is less than \(-.154\). For fixed t, (23) is a
linear combination of \(\sin x,\cos x\). Dividing by the
positive cosine makes it affine in \(\tan x\), so its negative
endpoint values imply negativity everywhere. Its second derivative
is its negative; it is therefore convex and its maximum is at an
endpoint. Thus the split second derivative is less than \(-.08\).

For (8), keep the actual E coordinates until after the split.
Its second derivative contribution is
\[
       -(.5+b_E)\cos e+(a_E-.5)\sin e
                    \le-.5\cos e+.915\sin e.
\tag{24}
\]
There is no varying D coefficient. Consequently the total is at most
\[
 k\{-.435\cos x+.961\sin x\}
                         -.5\cos e+.915\sin e.
\tag{25}
\]
Its two endpoint values, using \(1.003\le k\le1.01\),
\(\cos h>.7648\), \(\sin h<.6443\), are less than \(-.22\)
and \(-.20\). The same affine-tangent argument proves that (25)
is less than \(-.20\) on the whole split interval.

Thus in every family it is sufficient to prove the weighted
expression positive at the two intrinsic endpoints
\[
                         (x,e)=(0,t),\quad(t,0).
\tag{26}
\]
This is a scalar concavity argument on the full relaxed domain;
no motion of an actual square is asserted or required.

## 4. The complete ordinary-angle envelope

For a positive pair \(a\le b\), define
\[
\begin{aligned}
 U_{a,b}(s)&=a(\cos s+\sin s-1)
 -R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\},\\
 V_{a,b}^{\nu}(s)&=\nu(\cos s-1)
 -R\{\sqrt{a^2+b^2-2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{aligned}
\tag{27}
\]
The actual coefficient \(\nu\) of a negative ordinary angle is
\[
 \nu_H=n,\qquad \nu_A=l,\qquad
 \nu_B=c,\qquad \nu_D=\max(p,c).
\tag{28}
\]
The A coefficient is l because GA1 is already a fixed positive
primary. H similarly has only its HG2 ordinary argument.
Only B and D may contain both a positive and a negative ordinary
argument. Allowing two arguments at B even for AB2 enlarges the
domain and is harmless.

The separately concave two-error circle theorem applies to (18):
all sorted coefficient ratios are at least 1/2. H and A have one
ordinary angle; their actual \(V^\nu\) is concave because
\(-RN^{\prime\prime}(-s)\le C_0<.762\min(a,b)\),
\(\nu\ge\min(a,b)\), and \(\cos h>.7648\). Only B and D use
the mixed-sign two-angle function, whose negative coefficient is
the larger coefficient of its sorted pair. With remaining
positive cap \(P=h-t\), negative cap \(N=h\), it suffices to
consider pure negative charges \(V_i(t)\), same-block terms at B,D,
and separated terms \(U_i(P)+V_j(N)\). This is exactly the continuous
simplex endpoint reduction of
[the scalar-envelope note](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md),
with the actual available negative indices (28) retained.

### 4.1 The middle and high families

In (7)--(8), every ratio is at least 2/3. A same-block term minus
its pure negative term is
\[
 a(\cos P+\sin P-1)-b\{\cos t-\cos h\}\ge0,
\tag{29}
\]
since
\[
 \cos(h-P)-\cos h\le\sin h(\cos P+\sin P-1),
 \qquad 2/3>\sin h.
\]
For a separated term use the universal
\(U_{a,b}(P)\ge-.545bP\), proved in the scalar-envelope note at
the larger ceiling Q and therefore valid at Q1.
Also, on the whole interval \(0\le w\le h\),
\[
                        (V_{a,b}^{\nu})'(w)>.674b
          \qquad(\nu\le b,\ a/b\ge2/3).
\tag{30}
\]
Indeed the derivative increases with the ratio a/b, so put r=2/3
and square the positive sides of
\[
 Rr\sqrt{1-s^2}>(s+.674)\sqrt{1+r^2-2rs}.
\]
For \(0\le s\le.6443\), the resulting cubic is
\[
 \frac{1219568569}{1125000000}
 -\frac{754543}{562500}s
 -\frac{1560767069}{1125000000}s^2+\frac43s^3.
\tag{31}
\]
Its derivative is negative on this whole interval and its right
endpoint exceeds .00048. This proves (30).

In the middle family, the larger coefficients lie in [.983,1.11].
In the high family they lie in [1,1.13]. Thus respectively
\[
 .674(.983)-.545(1.11)>0,
 \qquad .674-.545(1.13)>0.
\tag{32}
\]
Integrating (30) from t to h shows that every separated term
is at least its own pure negative term at t. Hence it suffices
to check the four actual pure terms in (28). In the middle family
\(c>p\), so \(\nu_D=c\); this follows directly from (7),(10),
whose difference c−p is positive and increasing there.

### 4.2 The low family has one canonical pure charge

Write
\[
                         V_B(s)=V_{l,c}^{c}(s).
\tag{33}
\]
Direct rational bounds from (6), valid also for every split
\(x+e=t\le.2\), give
\[
\begin{gathered}
 .86265\le k\le n<1.05,\qquad 1\le p<1.05,
 \qquad c<1.045,\quad l<.698,\\
 .585+.35t\le l/c<.669,\quad l/k<.72,
 \quad c-k=.3t,
 \quad c-l>.346.
\end{gathered}
\tag{34}
\]
H and D have both product coordinates at least those of the pair
\((.86265,1)\), and negative coefficient at most 1.05. Positive
squaring gives
\[
 \frac{R(.86265)}{\sqrt{1+.86265^2}}>1.292.
\]
Consequently their pure charges are at least
\[
 1.292\sin t-1.05(1-\cos t)>1.17t.
\tag{35}
\]
On the other hand V_B is concave on \([0,t]\). In fact its norm
there is at least c, and its second derivative is less than
\(c\{-\cos .2+R(.669)^2\}<0\). Therefore
\[
 V_B(t)\le\frac{Rlc}{\sqrt{l^2+c^2}}t<1.15t.
\tag{36}
\]
This removes the H,D pure alternatives.

For A, put
\[
 H(a,b;s)=R\{\sqrt{a^2+b^2}-\sqrt{a^2+b^2-2ab\sin s}\}.
\]
For \(k\le q\le c\) and \(0\le s\le t\le.2\),
\[
                0\le\partial_q H(q,l;s)<.55s.
\tag{37}
\]
One explicit verification differentiates the integral formula for H.
With r=l/q and v=sin w, its integrand is
\[
 R\frac{r^2(r-v)\cos w}{(1+r^2-2rv)^{3/2}}.
\]
It increases with r on \(.585\le r\le.72\), \(0\le v\le.2\):
the derivative numerator is
\(r\{3r-2v-2r^2v+rv^2\}>0\).
Its upper bound
\(R(.72)^3/(1+.72^2-2(.72)(.2))^{3/2}\) is less than .55
by positive squaring. Thus
\[
\begin{aligned}
 V_A(t)-V_B(t)
 &\ge(c-l)(1-\cos t)-.55(c-k)t\\
 &>\{.346(1/2-.04/24)-.165\}t^2\ge0.
\end{aligned}
\tag{38}
\]
All pure alternatives therefore dominate V_B(t).

For the same B block, (29) follows from the lower ratio in (34).
Here the function
\[
 f(t)=(.585+.35t)\{\cos(h-t)+\sin(h-t)-1\}
                                      -\cos t+\cos h
\tag{39}
\]
is positive on [0,.2]. Its value at zero exceeds .004;
its derivative at 0 and .2 exceeds .07 and .06 respectively;
and \(f'''< -1\) on the whole interval. Thus f' is concave,
positive at both endpoints, and f is increasing. D's ratio
exceeds .82, so its same-block term dominates its pure term
by (29).

For separated terms, each positive charge satisfies the uniform
bound
\[
                              U_i(P)>-.408.
\tag{40}
\]
For completeness, U decreases with its angle on [0,h]. At h it
is convex in the ratio r=a/b. Its tangent at r=1 has positive slope and bounds it below
on \([1/2,1]\) by
\[
 \tfrac12(\cos h+\sin h-1)
       -\tfrac34R\{\sqrt{2+2\sin h}-\sqrt2\}>-.388.
\]
Multiplying by \(b<1.05\) proves (40).

Every actual negative charge at h is at least V_B(h). For A,
\(\partial_qH(q,l;h)<1\): its negative-angle norm is at most q,
so the derivative is at most \(R(.72)\sin h<1\). Hence
\[
 V_A(h)-V_B(h)\ge(c-l)(1-\cos h)-(c-k)
                >.346(.235)-.06>0.
\]
For H,D the same norm comparison as in (35), now at h, gives a
lower bound greater than .79; the B charge is less than .72.
Here the gain \(H(p,q;h)\) increases in each coefficient whenever
\(\min(p,q)/\max(p,q)>\sin h\); the rectangle paths from
\((.86265,1)\) to these pairs have ratio greater than .82.
These fixed radical bounds follow by positive squaring using
(34), \(\sin h\in(.6442,.6443)\), \(\cos h\in(.7648,.7649)\).

Finally, the whole low coefficient interval satisfies
\[
                         V_B(h)-V_B(t)>.43.
\tag{41}
\]
A short polynomial certificate is supplied in Section 6. Together
(40)--(41) make every separated term exceed \(V_B(t)+.022\).
Thus in the low family the complete ordinary-angle envelope
is bounded below by V_B(t), including every actual sign allocation.

## 5. The endpoint scalars

Put
\[
 C_v(s)=1+2\cos s+(1+2v-R\sqrt{1+v^2})\sin s.
\tag{42}
\]
For the first two families, the endpoint baselines at (26) are
\[
\begin{aligned}
 B_E(t)&=3k+2l+3c+C_\eta(t)
 -R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
              +\sqrt{l^2+c^2}+\sqrt{p(t)^2+c^2}\},\\
 B_G(t)&=3+2l+3c+kC_g(t)
 -R\{\sqrt{1+n(t)^2}+\sqrt{k^2+l^2}
              +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{aligned}
\tag{43}
\]
For the high family B_G is unchanged and
\[
 B_E(t)=3+\sin t-2R\sin(t/2)+3k+2l+3c
 -R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
              +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\tag{44}
\]
At an E endpoint the actual negative coefficients are
\((k,l,c,c)\) on the middle/high families; at a G endpoint they
are \((n(t),l,c,c)\). The corresponding pair products are
\((k,kl,lc,pc)\) or \((n,kl,lc,c)\), with p=1 in (44).

We prove
\[
 B_E+V_B>0,\quad B_G+V_B>0\qquad(0\le t\le.2),
\tag{45}
\]
and
\[
 B_E+V_i>0,\quad B_G+V_i>0
 \quad(i=H,A,B,D; .2\le t\le h).
\tag{46}
\]
Equations (45)--(46), Section 4 and the strict split concavity
prove the theorem. The next section gives exact whole-interval
certificates for every scalar in (45)--(46).

## 6. Rational polynomial certificates

Take
\[
 R_+=1.978770866>R,
\quad S(t)=\sum_{j=0}^{7}\frac{(-1)^jt^{2j+1}}{(2j+1)!},
\quad C(t)=\sum_{j=0}^{8}\frac{(-1)^jt^{2j}}{(2j)!}.
\tag{47}
\]
Their errors on [0,h] are less than \(7\cdot10^{-18}\) and
\(3\cdot10^{-19}\). The upper radius follows by positive squaring.

Here are explicit rational instructions for all the polynomials.
Use a local variable z=t−a, where \((a,D)\) is respectively
\((0,.2),(.2,.15),(.35,.35)\). Substitute the relevant exact
coefficient family and the Taylor polynomials (47).
For either endpoint let \(v_H,v_A,v_B,v_D\) be its four squared
norms in (43) or (44). Start with the part of its baseline outside
these four norms, replacing the tilt term
\(-R\sqrt{1+v^2}\sin t\) by an additional triple
\[
            (1+\eta^2,S)\quad\hbox{or}\quad(1+g^2,kS),
\tag{48}
\]
where a triple here records (squared norm, nonnegative weight).
All four anchor norms have weight 1. At the high E endpoint there
is no extra triple: put \(-2R_+S(t/2)\) directly in the outside part.

For the negative index i, add \(\nu_i(C-1)\) to the outside part
A and replace
\[
                         v_i\longmapsto v_i-2b_iS,
\tag{49}
\]
where \(b_i\) is its pair product specified after (44).
Thus adding a V term cancels the corresponding unperturbed norm
exactly; no radical with a positive coefficient remains.

For each resulting squared-norm polynomial v, put \(v_0=v(0)>0\).
Define three rational Newton steps
\[
 \rho_0=1,\qquad \rho_{j+1}=\tfrac12(\rho_j+v_0/\rho_j)
                      \quad(j=0,1,2),
\]
\[
 w=\frac{[v]_{\le3}-v_0}{v_0},\qquad
 a_v=\left[\rho_3\{1+w/2-w^2/8+w^3/16\}\right]_{\le3}.
\tag{50}
\]
The brackets mean truncation in the local variable z. These are
explicit polynomials over the rationals. Their definition involves
no fitted or sampled value. Every mass \(a_v\) is positive; the
whole-interval bounds below in fact give \(a_v>.82\).
For the resulting triples \((v_j,w_j)\), define
\[
 P=2A\prod_j a_{v_j}
       -R_+\sum_jw_j(v_j+a_{v_j}^2)
                              \prod_{r\ne j}a_{v_r}.
\tag{51}
\]
The identity
\[
 \frac{v+a^2}{2a}-\sqrt v=\frac{(\sqrt v-a)^2}{2a}\ge0
\tag{52}
\]
shows that \(P/(2\prod a_{v_j})\) is a lower bound for the
corresponding scalar, before the harmless Taylor error.
The masses in (50) stay fixed in this comparison: (52) is valid
for every positive mass, not only a Taylor approximation to a norm.

The following single coefficient-norm rule verifies all bounds.
If \(P(z)=\sum_{n=0}^Na_nz^n\) on \([0,D]\), define
\[
 b_0=\sum_na_n\frac{D^n}{4^n}\binom{2n}{n},\qquad
 b_j=2\sum_{n\ge j}a_n\frac{D^n}{4^n}\binom{2n}{n-j}
                                  \quad(j\ge1).
\tag{53}
\]
The identity
\(P(z)=\sum_jb_jT_j(2z/D-1)\) and \(|T_j|\le1\) give
\[
                     P(z)\ge b_0-\sum_{j\ge1}|b_j|.
\tag{54}
\]
Applying this whole-interval rational bound to (51) gives the
following strict lower bounds. Each entry is a coefficient-norm
bound on its complete interval, not a value at a sampled state.

| Family | Endpoint | H | A | B | D |
|---|---|---:|---:|---:|---:|
| [0,.2] | E | — | — | .000097 | — |
| [0,.2] | G | — | — | .00917 | — |
| [.2,.35] | E | .32410 | .03010 | .01205 | .40674 |
| [.2,.35] | G | .36756 | .04300 | .02449 | .38228 |
| [.35,.7] | E | .18718 | .02403 | .02961 | .35712 |
| [.35,.7] | G | .13913 | .03957 | .04347 | .36173 |

The maximum degree is 46. The same bound (54) gives masses
larger than .992 on the low family, 1.043 on the middle family,
and .825 on the high family. Keeping the masses fixed, all
partials of the unspecialized numerator in its sine/cosine inputs
are less than \(10^7\): there are at most five masses, each less
than 3, with \(|A|<30\), \(|v_j|<5\), \(|w_j|<2\), and input
partials bounded by 30. Thus the total substitution error is less
than \(10^{-8}\), far below every reserve in the table.
This proves (45)--(46).

Here is the additional low-family certificate for (41). Put
\[
 s_L=S(h),\qquad c_L=\sum_{j=0}^{7}\frac{(-1)^jh^{2j}}{(2j)!},
 \quad S_+(t)=\sum_{j=0}^{6}\frac{(-1)^jt^{2j+1}}{(2j+1)!},
\]
\[
\begin{aligned}
 v_h&=l^2+c^2-2lc s_L,\\
 d&=2lc\{s_L-S_+(t)\},\\
 A_0&=.43+c\{C(t)-c_L\},\\
 B_0&=Q_1d-A_0^2,\\
 P_0&=B_0^2-4Q_1A_0^2v_h.
\end{aligned}
\tag{55}
\]
The alternating Taylor directions make d a lower bound for the
norm-square difference, and \(v_h,A_0\) upper bounds for their
respective positive quantities. On the entire interval [0,.2],
(54) gives
\[
 A_0>.6326,\qquad B_0>1.7944,\qquad P_0>.1800.
\tag{56}
\]
Two positive-sided squarings give (41). Formula (55), of degree 72,
is a whole-interval polynomial identity and is not an angular mesh.

## 7. Conclusion and exact interface

For every fixed total t, Sections 4--6 make both endpoints of
(26) strictly positive for every allowed allocation of the five
ordinary errors and every sorted contained anchor. Section 3
makes the full weighted expression concave along the complete
split interval. It is therefore strictly positive at the original
allocation \((x,e)\). But (5) and the positive weights (11) require
it to be nonpositive. This contradiction proves the theorem.

The result removes the entire stated EH1/DE2 endpoint, including
outer E and arbitrarily small positive GA1. It does not on its own
convert a DE3/EH1 pair to this endpoint, or replace TD0 by a primary
TD2 or BT3. Those are separate finite-join obligations. No equality
inference is drawn from a changed intermediate square, since this
proof changes no actual square at all.

All certificates use rational polynomial identities and coefficient
norms on complete intervals. No sampled minimum, optimizer output,
state mesh, Lean compilation or CI result is a proof premise.
