# The aligned-HG negative-primary endpoint also has a short span with TD2

## 1. Original-data statement and the common middle stress

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,\quad
 c=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2,
 \quad K=13/12.
\tag{1}
\]
Retain a sorted true-core necessary cycle at an actual ceiling
\(q\le Q\), with real frame spread at most h. H,A are
nonnegative, B,D,G are nonpositive, and T has either signed
tangent. Assume actual witnesses
\[
 HG\in\{0,2\},\quad GA1,\quad AB\in\{0,2\},
 \quad BT2,\quad TD2,
 \qquad \theta_H=\theta_G>\theta_A,
\tag{2}
\]
and suppose actual GA0 is unavailable. Then
\[
                         \theta_H-\theta_D<11/50.
\tag{3}
\]
No E state, E witness, T sign, AB alignment, TD alignment,
or further original frame order is an input. Every state,
frame and actual witness is unchanged by this proof. Together
with the [TD0 span theorem](HAND_G5_NEGATIVE_GA_ALIGNED_HG_TD0_SPAN_BOUND.md),
this proves (3) for either actual transverse TD owner.

Write
\[
 t=\theta_H-\theta_A,
 \qquad f(t)=\tfrac12+(\tfrac32-c)\cos t+K\sin t.
\]
The actual negative-primary comparison and aligned HG give
\[
                    0<t<.09,\qquad a_A\ge f(t).
\tag{4}
\]
The derivation is Section 1 of the TD0 span theorem; it uses
neither E nor the other TD owner. All decimals below denote
exact rational numbers.

For \(.65\le\lambda\le.92\) define
\[
 \begin{split}
 N_\lambda(z)&=\sqrt{1+\lambda^2+2\lambda\sin z},
 \qquad n_\lambda=N_\lambda(0),\\
 U_\lambda(z)&=\lambda(\cos z+\sin z-1)
                       -R\{N_\lambda(z)-n_\lambda\},\\
 V_\lambda(z)&=\cos z-1
                       -R\{N_\lambda(-z)-n_\lambda\},\\
 B_\lambda(s)&=
 \begin{cases}U_\lambda(s),&s\ge0,\\V_\lambda(-s),&s\le0.
 \end{cases}
 \end{split}
\tag{5}
\]
Here all magnitudes are at most h. The middle calculation in
Section 4 of the TD0 span theorem, before adding TD, gives
\[
 f(t)+2+2\lambda-2Rn_\lambda
                  +B_\lambda(\theta_T-\theta_A)+y_T\le0.
\tag{6}
\]
It is the positive weighted sum of \(f(t)-a_A\le0\),
lambda times the actual AB inequality, and the actual BT2
inequality, with the A/B circles supported once each. In
particular, its signed T term is exactly \(+y_T\).

For clarity, the uniform weight range in (6) is justified
next; the cited TD0 proof printed only the weight .65.

## 2. The AB comparison is uniform on the stated weight interval

Both U and V in (5) are concave and vanish at zero, by the
whole-angle norm lemma in Section 3 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).
The following bounds hold uniformly on this weight interval:
\[
 \begin{gathered}
 U_\lambda(z)\ge-.545z,\qquad U_\lambda'(z)>-.72,\\
 V_\lambda'(z)>.64,\qquad V_\lambda(z)>.807z\quad(z>0).
 \end{gathered}
\tag{7}
\]
The positive-envelope bound and
\(V_\lambda(h)>.87\lambda\) are Sections 2--3 of
[the scalar-envelope theorem](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
Concavity gives the last inequality in (7), since
\(.87(.65)/.7>.807\).

For the derivative of V, differentiating
\(\lambda/N_\lambda(-z)\) in lambda gives
\[
 \frac{1-\lambda\sin z}{N_\lambda(-z)^3}>0.
\]
Thus its smallest derivative is at lambda .65 and z=h;
the TD0 span theorem proved that derivative greater than .64.
For U, concavity first reduces its derivative to z=h.
The lambda derivative at that endpoint is
\[
 \cos h-\sin h-
 \frac{R\cos h(1+\lambda\sin h)}{N_\lambda(h)^3}<0.
\]
Indeed \(\cos h-\sin h<.121\),
\(N_\lambda(h)^3<6\), and \(R\cos h>1.978(.7648)\).
Its minimum for lambda at most one is therefore at one.
The half-angle identity gives
\[
 U_1'(h)=\cos h-\sin h
       -(R/\sqrt2)\{\cos(h/2)-\sin(h/2)\}>-.72.
\tag{8}
\]
Using \(R/\sqrt2<1.4\) and the alternating Taylor bounds,
the exact reserve in (8) is greater than
\(25521012457/4608000000000\).

For AB0, the required width minimum is precisely Section 4
of [the small-wrong-sign capture theorem](HAND_G5_GLOBAL_SMALL_WRONG_INTERMEDIATE_SIGNS.md),
whose entire ratio domain is \(.65\le\lambda\le.92\).
It gives the U or V alternative in (6). For AB2, its two
circle norms are \(N_\lambda(d),N_\lambda(v)\), with
\(d+v=\theta_T-\theta_A\). The width increments dominate
the corresponding U/V increments, exactly as in the TD0
span calculation. Same-sign increments concentrate by
concavity. For opposite magnitudes P,N, (7) gives
\[
 \begin{array}{ll}
 U_\lambda(P)+V_\lambda(N)\ge V_\lambda(N-P),&P\le N,\\
 U_\lambda(P)+V_\lambda(N)\ge U_\lambda(P-N),&N\le P.
 \end{array}
\tag{9}
\]
The respective strict reserves per canceled unit are at
least \(.64-.545\) and \(.807-.72\). Thus the original
AB2 inequality gives (6) as well. All these comparisons
retain weak owner ties and arbitrary original B frames.

## 3. Negative TD2 angles supply a sufficient core charge

Suppose \(\theta_D-\theta_T=-z<0\). The actual BT2
projection is bounded by B's center norm, at most \(a_0\),
so
\[
                         y_T<a_0-1<.415.
\]
The actual TD2 inequality is
\[
                 b_D+y_T\cos z-a_T\sin z\ge W(z),
 \qquad W(z)=(1+\cos z+|\sin z|)/2.
\tag{10}
\]
Since \(b_D\le c<.9\), this implies \(y_T>0\) and
\(b_D+y_T>1\), hence \(y_T>.1\). True-core avoidance
and \(y_T<.415<1/2\) give \(a_T\ge7/12\). Consequently
the left side of (10), minus its demand, is at most
\[
                         .4-.085\cos z-K\sin z.
\]
This function decreases on \([0,h]\). At z=.3 it is
negative by the rational reserve
\[
 .085C_6(.3)+KS_7(.3)-.4
                         =18906887/14000000000>0.
\]
Thus
\[
                            0<z<.3.
\tag{11}
\]
Here and subsequently \(C_j,S_j\) are the degree-j
alternating Taylor polynomials for cosine and sine.

Add (10) to (6), with lambda .65. Its exact remaining T
force is \(-a_T\sin z-(1-\cos z)y_T\). The resulting
additional charge beyond the aligned TD demand \(1-c\)
is at least
\[
                    J(z)=K\sin z-.4(1-\cos z).
\tag{12}
\]
We need the whole-interval inequality
\[
                       J(z)\ge V_{.65}(z)
                                  \qquad(0\le z\le.3).
\tag{13}
\]
It is strict for positive z. Here is a short direct proof.
Put \(\lambda=.65\), \(b=1+\lambda^2\),
\(n(z)=\sqrt{b-2\lambda\sin z}\), and
\[
 D(z)=J(z)-V_\lambda(z)
       =K\sin z+.6(1-\cos z)+R\{n(z)-n(0)\}.
\]
The radical satisfies
\[
 n'''(z)=\frac{\lambda\cos z}{n(z)^5}
      \{b^2-b\lambda\sin z+\lambda^2\sin^2z-3\lambda^2\}.
\]
Throughout \([0,.3]\), \(n(z)>1.018\). Therefore
\[
 D'''(z)
 \le-KC_2(.3)+
 \frac{1.978788\lambda\{b^2-3\lambda^2+\lambda^2(.3)^2\}}
             {1.018^5}<-.1.
\tag{14}
\]
The last upper bound is less than \(-.10044\). Hence
D' is concave. Its endpoint bounds are
\[
 \begin{split}
 D'(0)&\ge K-1.978788(.65)/1.192686>.004,\\
 D'(.3)&\ge KC_6(.3)+.6S_7(.3)
                  -1.978788(.65)C_4(.3)/1.018>.005.
 \end{split}
\tag{15}
\]
All radical comparisons here are positive square checks;
in particular \(1.018^2<b-2\lambda S_5(.3)\).
Equations (14)--(15) imply D'>.004, and D(0)=0 proves
(13) on its entire interval.

Now suppose, toward contradiction, that
\(\alpha=\theta_H-\theta_D\ge.22\), and put
\(u=\theta_A-\theta_D=\alpha-t>.13\).
The middle argument in (6) is z-u. If z<=u, concavity
and (13) give
\[
 V_\lambda(u-z)+J(z)
       \ge V_\lambda(u-z)+V_\lambda(z)\ge V_\lambda(u).
\]
If z>=u, (7) gives instead
\[
 U_\lambda(z-u)+J(z)
       \ge V_\lambda(u)+(.64-.545)(z-u)
       \ge V_\lambda(u).
\tag{16}
\]
Thus the necessary stress reduces to
\[
 f(t)+2+2\lambda+\cos u-c
           -R\{n_\lambda+N_\lambda(-u)\}\le0.
\tag{17}
\]
This is exactly the impossible scalar (23)--(25) of the
TD0 span theorem: it is greater than .0057 whenever
\(0\le t\le.09\) and \(u\ge.22-t\). This excludes every
negative TD2 angle in a purported long-span input.

## 4. Positive TD2 angles have an exact axis support

The aligned TD case is already (17), so now put
\(w=\theta_D-\theta_T>0\). Continue to suppose
\(\alpha=\theta_H-\theta_D\ge.22\), and define
\[
 v=\theta_A-\theta_T,\qquad
 u=\alpha-t,
 \qquad v=u+w>.13.
\]
The original frame interval, with H>D>T, gives
\[
                  t+v\le.7,
             \qquad 0<w\le t+v-.22\le.48.
\tag{18}
\]
No intermediate-order theorem or E hypothesis is needed
for this observation.

The remaining signed T force after adding TD2 to (6) is
\[
                          a_T\sin w-(1-\cos w)y_T.
\]
Its maximum over all sorted contained T states, including
both signs, is
\[
                          a_0\sin w.
\tag{19}
\]
Indeed replace \(-y_T\) by \(|y_T|\) for an upper bound.
The force ratio is \(\tan(w/2)\). On \([0,.48]\) it
is less than \(1/(2\sqrt{Q-1/4})\), so the maximizing
shifted circle corner is its tangent-zero endpoint. The
last ratio comparison follows already from
\[
 1-.24^2/2-2(1.915)(.24)=13/250>0,
 \qquad \sqrt{Q-1/4}<1.915.
\]
This is an upper support over a superset of the true-core
states, so no new radial or sign assumption is involved.

Put \(k=a_0-1/2\) and
\[
 C(w)=W(w)-c-a_0\sin w
      =1-c-k\sin w-\tfrac12(1-\cos w).
\tag{20}
\]
It decreases on \([0,.48]\). It is also strictly concave
there, since
\[
 .5C_6(.48)-.914576S_5(.48)
                   =32294026751/1525878906250>0.
\tag{21}
\]
Choose the continuous weight
\[
                         \lambda(v)=.59+.47v.
\tag{22}
\]
For \(.13\le v\le.7\), it lies in
\([.6511,.919]\), inside the domain of Section 2. Keeping
that weight fixed during the scalar comparisons, (6) and
(19) give the necessary inequality
\[
 F(t,v,w):=f(t)+1+2\lambda+\cos v
       -R\{n_\lambda+N_\lambda(-v)\}+C(w)\le0.
\tag{23}
\]
Because C decreases, (18) implies
\[
                     F(t,v,w)\ge F(t,v,t+v-.22).
\]
For fixed v the expression on the right is concave in t:
both f and C are strictly concave on their respective
intervals. Its possible t values are exactly contained in
\[
             \max(0,.22-v)\le t\le\min(.09,.7-v).
\tag{24}
\]
Thus it suffices to bound the four intrinsic boundary
expressions of this polygon:
\[
 \begin{array}{ll}
 w=0,\ t=.22-v,&.13\le v\le.22,\\
 t=0,\ w=v-.22,&.22\le v\le.7,\\
 t=.09,\ w=v-.13,&.13\le v\le.61,\\
 t=.7-v,\ w=.48,&.61\le v\le.7.
 \end{array}
\tag{25}
\]
These are scalar comparisons on the original stress. They
do not assert that the original frames have a boundary
form, or construct any moved witness.

## 5. The aligned boundary follows from the fixed-weight scalar

On the first boundary in (25), lambda ranges only from
.6511 to .6934. At fixed t,v the lambda derivative of the
aligned scalar is
\[
 2-R\left\{\frac\lambda{\sqrt{1+\lambda^2}}
       +\frac{\lambda-\sin v}{\sqrt{1+\lambda^2-2\lambda\sin v}}
        \right\}>-.122
\tag{26}
\]
for \(.65\le\lambda\le.7\), \(.13\le v\le.22\).
Both ratios increase with lambda, and the second decreases
with v; its denominator is positive. At \((.7,.13)\),
the radical lower bounds 1.22065 and 1.1439 give (26):
\[
 2.122-1.978788
   \left\{\frac{.7}{1.22065}
       +\frac{.7-S_7(.13)}{1.1439}\right\}>0.
\]
Their two square reserves are respectively
\(5431/400000000\) and \(29940949/6000000000000\).
The fixed-weight aligned scalar at lambda .65 is greater
than .0057 by the TD0 span theorem. Increasing lambda to
(22) therefore leaves the uniform positive reserve
\[
                   .0057-.122(.0434)=1013/2500000>0.
\tag{27}
\]
This proves the first boundary in (25).

## 6. Three whole-interval polynomial certificates

Here are explicit certificates for the other three continuous
boundaries. They use positive quadratic tangent bounds for
the two radicals, followed by a Chebyshev coefficient norm on
one whole interval in each case. No angular partition or
inventory of sampled rows is used.

Write
\[
 \overline R=1.978788,\qquad
 \overline c=.899215,\qquad \overline k=.914576.
\tag{28}
\]
These are upper bounds for R,c,k by positive squaring; the
reserves are
\[
 \overline R^2-Q=121809/62500000000,
 \quad 2(\overline c+1/2)^2-Q=104649/20000000000,
 \quad (\overline k+1)^2-(Q-1/4)=4921/3906250000.
\]
For the appropriate boundary functions t=t(v), w=w(v),
put
\[
 \begin{split}
 E(v)={}&2-\overline c+2\lambda
   +(1.5-\overline c)C_6(t)+KS_7(t)+C_6(v)\\
 &\hspace{20mm}-\overline k S_5(w)+\tfrac12 C_6(w),\\
 p_0(v)&=1+\lambda^2,\qquad
 p_1(v)=1+\lambda^2-2\lambda S_7(v).
 \end{split}
\tag{29}
\]
For positive polynomial masses r_0,r_1 define
\[
 P(v)=2r_0r_1E-
 \overline R\{r_1(p_0+r_0^2)+r_0(p_1+r_1^2)\}.
\tag{30}
\]
The elementary positive identity
\(\sqrt p\le(p+r^2)/(2r)\) shows that
\(P>0\) implies \(F(t(v),v,w(v))>0\). All Taylor
bounds in (29) have the indicated signs on these entire
intervals; both radicands are positive.

For \(t=0,\ w=v-.22\), use \(x=v-.46\),
\(|x|\le.24\), and
\[
 \begin{split}
 r_0&=1.284507+.294988x+.052114x^2,\\
 r_1&=.966507-.571273x-.305135x^2.
 \end{split}
\tag{31}
\]
The constant coefficients less the absolute nonconstant
terms at radius .24 exceed 1.2107 and .8118. The degree-ten
polynomial (30), expanded in \(T_j(x/.24)\), has coefficients
\(a_j\) satisfying the exact rational inequality
\[
                         a_0-\sum_{j=1}^{10}|a_j|>.022.
\tag{32}
\]

For \(t=.09,\ w=v-.13\), use \(x=v-.37\),
\(|x|\le.24\), and
\[
 \begin{split}
 r_0&=1.258389+.285312x+.055427x^2,\\
 r_1&=1.015415-.515190x-.317442x^2.
 \end{split}
\tag{33}
\]
The analogous mass lower bounds exceed 1.1867 and .8734.
Its degree-ten coefficients in \(T_j(x/.24)\) obey
\[
                         a_0-\sum_{j=1}^{10}|a_j|>.032.
\tag{34}
\]

For \(t=.7-v,\ w=.48\), use \(x=v-.655\),
\(|x|\le.045\), and
\[
 \begin{split}
 r_0&=1.343925+.313998x+.045503x^2,\\
 r_1&=.843959-.682916x-.263049x^2.
 \end{split}
\tag{35}
\]
The mass lower bounds exceed 1.3297 and .8126. Its
degree-eleven coefficients in \(T_j(x/.045)\) obey
\[
                         a_0-\sum_{j=1}^{11}|a_j|>.066.
\tag{36}
\]
For complete exact coefficient recovery in (32),(34),(36),
expand the explicitly defined (30) as \(P=\sum b_nx^n\).
At the stated radius r, the coefficients are
\[
 \begin{split}
 a_0&=\sum_{k\ge0}b_{2k}r^{2k}2^{-2k}{2k\choose k},\\
 a_j&=\sum_{\substack{n\ge j\\n-j\ {\mathrm{even}}}}
      b_nr^n2^{1-n}{n\choose(n-j)/2}\qquad(j\ge1).
 \end{split}
\tag{37}
\]
Thus the three inequalities are finite rational polynomial
identities and coefficient norm bounds. Direct multiplication
in (29)--(37) gives respective norm lower bounds greater
than .022368, .032412 and .066023. Since
\(|T_j(\xi)|\le1\) for \(|\xi|\le1\), each certificate
proves positivity over its complete interval.

Equations (27),(32),(34),(36), followed by the fixed-v
concavity in (24), show that the right side of (23) is
strictly positive everywhere in a purported positive-TD2
long-span input. This contradicts its necessary sign.

## 7. Scope and use in the primary entry

Negative, zero and positive TD2 errors have all been covered.
Hence (3) holds under exactly the original-data assumptions
of Section 1. Combined with the TD0 result, it is available
for arbitrary actual AB and TD transverse owners and either
original T sign.

This is a strict original-data span bound; it changes no
state and creates no equality identification between an
ancestor and a descendant. When E lies between D and H,
its positive EH1 angle is automatically less than .22,
and the same-q H/G transport in
[the aligned-HG entry theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md)
then supplies its independently proved strict H-circle loss.
Outside E frames still require their actual mixed-owner
transports. No replacement of those witnesses, no angle
mesh, numerical acceptance premise, Lean compilation or
CI result is used here.
