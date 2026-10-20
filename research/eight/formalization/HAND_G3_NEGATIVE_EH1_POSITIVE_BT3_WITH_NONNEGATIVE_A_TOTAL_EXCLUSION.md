# Negative EH1 with positive BT3, arbitrary TD0 and nonnegative A total

## 1. Original scope and conclusion

Use the actual high-GA G0--G2 boundary-neighbor cycle with
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\]
The sorted outer roles H,G,B,D have signed tangents respectively
positive, negative, negative and negative. A and T have arbitrary
signs and radial kinds. E has negative signed tangent. Retain the
actual weak witnesses
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=3,\quad TD=0,\quad DE=2,\quad EH=1.                 \tag{1}
\]
The BT3 error is \(z\ge0\), while the TD0 error is arbitrary.
The selected A primary total a is nonnegative: it may be zero,
one nonnegative primary, or the signed sum of two primaries whose
individual signs are arbitrary. The EH1 error is \(-s\), with
\[
 0\le s\le u:=\frac14,\qquad
 a_E=\frac7{12},\qquad 0\le b_E=-y_E\le\frac{39}{250}.       \tag{2}
\]
These closed E conditions contain every genuine sole negative
EH1. If the actual secondary EH0 is already available, select it
and use the nonnegative-E theorem instead. The exact entry
alternative is in Section 2 of
[the mixed-negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).

Assume all original adjacent inequalities, all actual circles,
and the captured real-error variation bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.                           \tag{3}
\]
No order of the real frames is assumed.

**Theorem.** There is no such necessary system.

The proof keeps the original TD0 argument in D's two-angle
support. It applies after any already proved reduction preserving
(1)--(3). All terminating decimals below are exact rationals.

## 2. The actual force identity and the two EH charges

Put
\[
 \begin{gathered}
 L=\frac16,\quad v=\frac1{10},\quad
 \eta=.293,\quad K=\frac{13}{12},\quad\beta=.656,\\
 c_0=\sqrt{Q/2}-\frac12,\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\\
 f(z)=\cos z+\eta\sin z,\quad
 W(t)=\frac{1+\cos t+|\sin t|}{2},\quad
 \overline S(x,y)=R\sqrt{x^2+y^2}-\frac{x+y}{2}.
 \end{gathered}                                               \tag{4}
\]
Give the seven inequalities the weights
\[
                  (k,l,l,m,c,1,p),\qquad c=mf(z).              \tag{5}
\]
The exact contribution of the actual T state is
\[
 m(a_T\sin z-y_T\cos z)+cy_T
          =m\sin z(a_T+\eta y_T)\le m\sigma\sin z.             \tag{6}
\]
This is the same shifted-circle support identity as Section 2 of
[the positive-BT theorem](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
It allows either sign and either radial kind of T.

The signed A comparison supplies \(lj(a)\), including two
oppositely signed A primaries. The exact support charge j and
its signed-pair combination are proved in
[the A-primary combination](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
We use
\[
 j''(t)\le-\frac12\cos t+.92\sin t,
 \qquad
 j(t)=\frac{\cos t-1}{2}+(\tfrac12-a_0)\sin t
                  \quad(0\le t\le\tfrac14).                  \tag{7}
\]
On the displayed small interval the curvature coefficient .92 can be
replaced by .915. The two support branches have matching first
derivatives.

For \(0\le s\le v\), take \(p=1\). The actual E force from
DE2 and EH1 is \(-a_E\sin s+b_E(1-\cos s)\). Its net charge,
after removal of the EH primary argument, is at least
\[
                 g(s):=K\sin s-\beta(1-\cos s),
 \qquad g'(s)>1.012,\qquad g''(s)<0.                           \tag{8}
\]
This is the direct calculation in Section 2 of
[the small-negative-EH theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SMALL_ERROR_EXCLUSION.md).

For \(v\le s\le u\), take
\[
             p=1.005,\qquad\varepsilon=p-1=.005.
\]
The same calculation with the H support retained gives
\[
 \begin{split}
 H_p(s)={}&p\{1+\beta\cos s+K\sin s\}-(1+\beta)\\
          &-R\{\sqrt{p^2+k^2}-\sqrt{1+k^2}\}.
 \end{split}                                                  \tag{9}
\]
For \(.6\le k\le.8\), the exact bounds from Sections 2--3 of
[the far-negative-EH theorem](HAND_G3_CORE_E_NEGATIVE_EH1_REMAINING_ERROR_EXCLUSION.md)
give
\[
 H_p(s)\ge G(s):=p g(s)-.00022,
 \qquad G'(s)>.8917,\qquad G''(s)<0.                           \tag{10}
\]
They also compare the remaining H argument with the ordinary
pair \((k,1)\): a negative argument costs at least \(V_{k,1}\),
and a positive argument costs at least \(U_{k,1}-\varepsilon t\).
These force comparisons involve only E,H and the HG edge;
they do not use the BT or TD owner. Consequently all ordinary
blocks below may use their unmodified pairs, with an additional
lower charge \(-\varepsilon P\) on the total positive mass.
For the small-s range set \(\varepsilon=0\).

## 3. Four ordinary blocks and the remaining variation

For \(0<x\le y\), write
\[
 \begin{split}
 N_{x,y}(t)&=\sqrt{x^2+y^2+2xy\sin t},\\
 U_{x,y}(t)&=x(\cos t+\sin t-1)-R\{N_{x,y}(t)-N_{x,y}(0)\},\\
 V_{x,y}(t)&=y(\cos t-1)-R\{N_{x,y}(-t)-N_{x,y}(0)\},\\
 \Psi_{x,y}(P,N)&=x(\cos P+\sin P-1)+y(\cos N-1)\\
       &\hspace{18mm}-R\{N_{x,y}(P-N)-N_{x,y}(0)\}.
 \end{split}                                                  \tag{11}
\]
The four ordinary coefficient pairs are
\[
                H:(k,1),\quad G:(k,l),\quad
                B:(l,m),\quad D:(1,c),                       \tag{12}
\]
ordered when U,V or \(\Psi\) is evaluated. D includes both the
actual TD0 and DE2 errors. Its full-circle normalization is the
same four-block normalization as in the positive-BT theorem.

Put \(\theta=a+z\le h\). After the actual primary comparisons,
the remaining positive and negative masses satisfy
\[
 P\le h-\theta,\qquad N\le h-s,\qquad N-P=\theta-s.            \tag{13}
\]
For a signed A pair its removed positive variation is at least a;
discarding its removed negative variation only weakens these
caps. Missing primary arguments are virtual zeros in the scalar
minimization, without any change of original witness.

For full D support define the baseline, including the A charge,
\[
 \begin{split}
 B(a,z)={}&k+2l+mW(z)+c+2-m\sigma\sin z+lj(a)\\
       &-\overline S(1,k)-\overline S(k,l)
        -\overline S(l,m)-\overline S(1,c).
 \end{split}                                                  \tag{14}
\]
For small total \(\theta\le L\) in Section 4 only, replace
the last term by \(-(1+c)c_0\), and denote that baseline by
\(B_s(a,z)\). There \(c\ge1\), so it is the exact sorted
zero-angle D support.

The ordinary pairs used below all have smaller-to-larger ratio
at least 1/2. The separate concavity and simplex concentration
of Section 3 of
[the four-block concentration note](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
therefore apply. With full D support they give the alternatives
\[
 \begin{array}{ll}
 V_i(\theta-s),&s\le\theta,\\
 U_i(s-\theta)-\varepsilon(s-\theta),&s\ge\theta,\\
 \Psi_i(h-\theta,h-s)-\varepsilon(h-\theta),&\\
 U_i(h-\theta)+V_j(h-s)-\varepsilon(h-\theta).&
 \end{array}                                                  \tag{15}
\]
Each is added to \(B+g(s)\) or \(B+G(s)\). Equal indices in
the separated alternative are harmless enlargements.

In every family, the negative D singleton satisfies
\[
               V_{\min(1,c),\max(1,c)}(t)\ge V_{k,1}(t),       \tag{16}
\]
by the established D comparison: its hypotheses are
\(k\le1\) and \(k\le c<1.2\). Thus no pure negative D endpoint
will be needed.

## 4. Small EH magnitude and small total

Suppose \(s\le v\), \(\theta\le L\), and choose
\[
        k=.5866+.4956\theta,\qquad l=1,
        \qquad m=1.1642-.8874\theta.                           \tag{17}
\]
The exact range proof in Section 3 of the positive-BT theorem
gives
\[
 .5866\le k\le.6692,\qquad
 1.0163\le m\le c\le1.1642.                                  \tag{18}
\]
The all-sign sorted-D inequality in
[the sorted-D envelope](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md)
retains \((1+c)c_0\) and gives
\[
                     D\ge-.65P_D+V_{k,1}(N_D).                \tag{19}
\]
Use (19) as a separately concave enlarged D block. The same
simplex argument gives (15), with a D positive term \(-.65P\)
and a D negative term \(V_H(N)\). D's mixed endpoint is included
among the separated alternatives.

For pure positive alternatives, the exact uniform derivative
bound (10)--(11) of the small-negative-EH theorem is
\(U_i'(t)>-.5q_i\) for \(0\le t\le v\). Hence
\[
      g'(s)+U_i'(s-\theta)>1.012-.5(1.1642)>0.                \tag{20}
\]
The D linear alternative increases as well, since
\(1.012-.65>0\). Thus \(s\ge\theta\) reduces to \(s=\theta\).

For \(s\le\theta\), the pure negative minimum is \(V_H\):
H and G coincide; B dominates H by the low-angle coordinatewise
comparison; and (19) supplies the same H term for D. Since
\(g(s)+V_H(\theta-s)\) is concave in s, its minimum is at
zero or \(\min(\theta,v)\).

The B same-block term dominates the corresponding pure term by
the universal same-block comparisons, since \(m<1.5\). For H
and G the saturated stress has s derivative
\[
             g'(s)+\sin(h-s)-RN_{k,1}'(s-\theta).              \tag{21}
\]
Writing \(D_0=RN'(0)\), \(C_0=-RN''(0)\), the exact norm
curvature inequalities give \(RN'(s-\theta)\le D_0+C_0\theta\).
Positive squaring at \(k=.6692\) gives
\(D_0<1.101\), \(C_0<.51\). Both quantities increase with k
on (18). As \(h-s\ge.6\), (21) is greater than
\[
                1.012+.564-1.101-.51/6=.39>0.                 \tag{22}
\]
These same-block stresses reduce to \(s=0\).

In separated terms, negative B may be replaced by H on all of
\([0,h]\): the universal endpoint chord gives
\(V_B(t)\ge(.87/h)t>1.101t\ge V_H(t)\). Negative D already
has the H bound. For \(N\ge.6\), concavity and monotonicity in
k give
\[
                         V_{k,1}'(N)<.75.                    \tag{23}
\]
Here is a short rational check of (23). At \(k=.6692\), the
denominator in \(V'(.6)\) exceeds .8318 because
\[
 1+k^2-2k(.56465)-.8318^2=\frac{2623}{12500000}>0.
\]
Using \(.56464<\sin(.6)<.56465\), \(\cos(.6)<.82534\),
\(R<1.978788\), the difference from .75 is greater than
\(18695481373/25993750000000\). Thus every separated stress,
including the D linear one, increases in s by more than
\(1.012-.75\), and also reduces to \(s=0\).

At \(s=0\), the complete low-total envelope and scalar proof
in the positive-BT theorem already give
\(B_s(a,z)+V_H(\theta)>0\) for every split. No transport to
that endpoint configuration is asserted: this is a previously
proved inequality between the same scalar functions.
The only new obligations are
\[
 \begin{array}{ll}
 B_s(a,z)+g(\theta)>0,&0\le\theta\le v,\\
 B_s(a,z)+g(v)+V_H(\theta-v)>0,&v\le\theta\le L.
 \end{array}                                                  \tag{24}
\]
Hold \(\theta,k,m\) fixed. The added terms in (24) do not
depend on the split. The exact sorted-D baseline contributes
\((1-c_0)c-c_0\), whose second derivative is negative.
The low split proof in Section 10 of the sorted-D envelope
therefore applies unchanged, with second derivative below
\(-.8\). Only \((a,z)=(\theta,0),(0,\theta)\) remain.
Section 8 proves all four resulting functions positive.

## 5. Small EH magnitude and large total

Suppose \(s\le v\), \(L\le\theta\le h\). Put \(x=\theta-L\)
and choose
\[
 \begin{split}
 k&=.6692+.5218x-.5956x^2+.4216x^3,\\
 l&=1+.0175x-1.0932x^2+1.278x^3,\\
 m&=1.0163-.0209x-1.1486x^2+1.4069x^3.
 \end{split}                                                  \tag{25}
\]
These are the positive-BT large-total family at e=0. Its proved
range bounds give, for all \(0\le z\le\theta\),
\[
 p_i/q_i>2/3,\quad q_{\max}/q_{\min}<6/5,\quad
 .9<m/l<1.1,\quad k\le c<1.2,\quad c/l<1.15.                  \tag{26}
\]
Here \(s<\theta\). Every same-block term in (15) dominates
its pure negative counterpart. For a separated term, the
universal inequalities \(U_i(P)\ge-.545q_iP\) and
\(V_j'(t)>(2/3)q_j\) give a nonnegative excess, because
\[
                     \frac23-.545\frac65>0.                  \tag{27}
\]
Using (16), only
\[
                B(a,z)+g(s)+V_i(\theta-s),\quad i=H,G,B       \tag{28}
\]
remain. Each is concave in s, so it suffices to take \(s=0,v\).
At zero these are precisely the positive scalar alternatives
already proved in the positive-BT theorem.

For \(s=v\), the V term is independent of z. The varying D
part is \(H(c)=\tfrac32c-R\sqrt{1+c^2}\), with
\(H''<0\), \(H'>-.021\), and \(c''=-c\). By (26), its
composition contributes at most \(.02415l\) to the split
curvature. The j and T-width terms contribute less than
\(-.08576l\). These are exactly the whole-interval estimates
in Section 5 of the positive-BT theorem. Thus every function
in (28) has split second derivative below \(-.06161l\).
The six new endpoint functions have \(s=v\), \(i=H,G,B\),
and \((a,z)=(\theta,0),(0,\theta)\). Section 8 proves them all.

## 6. Far EH magnitude and low total

Suppose \(v\le s\le u\), \(0\le\theta\le u\). Use p and G
from (10), and choose
\[
                 k=.605,
       \qquad l=1-.36\theta,\qquad m=1.11-.77\theta.            \tag{29}
\]
Here
\[
 \begin{gathered}
 .91\le l\le1,\quad .9175\le m\le c\le1.11,\quad
 1<m/l\le1.11,\quad c/l<1.17,\\
       \min_i p_i\ge.605,\quad\max_i q_i\le1.11,
                              \quad q_i/p_i<5/3.
 \end{gathered}                                               \tag{30}
\]
The proof is the elementary range proof of
[the far-low concentration lemma](HAND_G3_CORE_E_NEGATIVE_EH1_FAR_LOW_ANGLE_CONCENTRATION.md),
with its base c renamed m and its tilted coefficient renamed c.
The new fourth pair D obeys these same bounds, so the ordinary
comparisons in that proof now apply to all four blocks.

For clarity, the concentration conclusions can be checked
directly. Since \(N=h-s\le.6\), the same-block differences
exceed \(.032P\) when \(P\le N\), and \(.022N\) when
\(N\le P\). These pay the extra \(\varepsilon\) charge.
Negative B dominates H by the universal chord and \(l\ge.91\);
negative D dominates H by (16). Every pure U stress increases
in s since
\[
                 .8917-.72(1.11)-.005=.0875>0.                \tag{31}
\]
For the surviving H/G pure V stresses, concavity in s leaves
only \(s=v\) or \(s=\theta\).

Every separated H/G stress also increases in s. The uniform
rectangle estimate from Section 4 of the far-low lemma is
\[
 V'_{\kappa,q}(N)<.876
 \quad(.6\le\kappa\le.68,\ .91\le q\le1.3,
                               \ .45\le N\le.6),             \tag{32}
\]
so its derivative is greater than \(.0157\). At \(s=v\), put
\(P=h-\theta\). Every positive alternative, including D, is
at least \(-.60995P\), while the H/G negative endpoint is
greater than \(31581/70000\). For \(\theta\le v\) their sum
is positive and hence dominates the charged H pure U term.
For \(v\le\theta\le u\), subtracting
\(V_H(\theta-v)\le1.025(\theta-v)\) leaves at least
\[
                         \frac{64203}{2800000}>0.             \tag{33}
\]
These are the same strict secants as the far-low lemma; they
use only (30), so include the new ordinary D positive term.

Finally \(U_G\ge U_H\), because \(l\le1\) and U decreases
in its larger coefficient. Writing \(Z(s)=B(a,z)+G(s)\), the
remaining exact functions are
\[
 \begin{array}{ll}
 Z(v)+U_i(v-\theta)-\varepsilon(v-\theta),
                         &i=H,B,D,\quad0\le\theta\le v,\\
 Z(v)+V_H(\theta-v),\quad Z(v)+V_G(\theta-v),\quad Z(\theta),
                         &v\le\theta\le u.
 \end{array}                                                  \tag{34}
\]

The additional D pure U function requires its own split check.
In its domain \(\theta\le v\), one has \(m\ge1.033\) and
\(c\ge m>1\), so its smaller coefficient is exactly 1.
Putting \(\delta=v-\theta\), the c-dependent part is
\[
 H_U(c)=\frac32c+\cos\delta+\sin\delta-1
                     -R\sqrt{1+c^2+2c\sin\delta}.             \tag{35}
\]
It is concave in c and \(H_U'(c)>-.04\) for
\(c\le1.11\), \(\delta\le.1\). Indeed
\((c+t)/\sqrt{1+c^2+2ct}\) increases in both c and t, and
\[
 1.54^2(1+1.11^2+2(1.11)(.1))-Q(1.11+.1)^2
                             =\frac{54571}{625000}>0.         \tag{36}
\]
For every other function in (34), the c-dependent part is H
from Section 5, also concave with derivative above -.04.
Since \(c''=-c\), all these compositions contribute at most
\(.04c\). Using (30), \(\cos a,\cos z\ge31/32\),
\(\sin a+\sin z\le\theta\le1/4\), and (7), their entire
split second derivative divided by l is at most
\[
 -\frac{31}{32}+.916(1.11)\frac14+.04(1.17)
                      =-\frac{8347}{12500}<-.66.              \tag{37}
\]
Thus only the two split endpoints remain. There are twelve
functions in (34), counting both endpoints, all certified in
Section 8. The D positive function has been retained explicitly.

## 7. Far EH magnitude and high total

For \(u\le\theta\le h\), choose
\[
      k=.505+.4\theta,\qquad
      l=.9525-.17\theta,\qquad m=.9645-.188\theta.              \tag{38}
\]
These agree with (29) at u. The elementary bounds are
\[
 \begin{gathered}
 .605\le k\le.785,\quad .8335\le l\le.91,\quad
 .8329\le m\le.9175,\quad .99<m/l<1.01,\\
 .95m<c<1.043m<1,\quad k<c,\quad k<\min(l,m),\\
      \min_i p_i\ge.605,\quad\max_i q_i=1,
                         \quad p_i/q_i>.6.
 \end{gathered}                                               \tag{39}
\]
The bounds on f use its concavity and its two endpoints;
\(1+\eta^2<1.043^2\). The comparison k<c is the same
tilted-coefficient comparison proved for the far-EH family.
The fourth pair D is again included in (39).

Here \(s\le u\le\theta\), and saturated \(N=h-s\le.6\).
The same-block comparison exceeds \(.032P\). The uniform
derivative inequality proved in Section 5 of the far-EH theorem,
\[
        V'_{x,y}(t)>1.03x
              \quad(x/y\ge.6, 0\le t\le.6),                 \tag{40}
\]
gives for separated terms
\[
 U_i(P)+V_j(N)-\varepsilon P
     \ge V_j(N-P)+\{1.03(.605)-.545-.005\}P
     =V_j(N-P)+.07315P.                                      \tag{41}
\]
Thus, after (16), the only functions are
\[
                    B(a,z)+G(s)+V_i(\theta-s),
                              \quad i=H,G,B.                 \tag{42}
\]
They are concave in s, so only \(s=v,u\) remain.

For fixed \(\theta,s\), every V term in (42) is independent
of z. Since \(c<1\), the c-dependent H is concave and
increasing: \(H'(c)\ge1.5-R/\sqrt2>0\). Its composition
with c is concave. The other curvature terms are at most
\[
 m\{-\tfrac12\cos z+.916\sin z\}
       +l\{-\tfrac12\cos a+.92\sin a\}<-.08576l,              \tag{43}
\]
using the weaker \(.9<m/l<1.1\), \(a+z\le h\), and
\(\cos a+\cos z\ge1+\cos h>1.7648\).
The j transition has a continuous first derivative. Hence
the minimum is at one of the two split endpoints. The twelve
functions, from three negative pairs, two s values and two
split endpoints, are all positive by the following exact checks.

## 8. Compact whole-interval polynomial certificates

This section specifies all 34 endpoint polynomials by formulas.
Each coefficient aggregate is applied to its entire analytic
interval; there is no angle subdivision or coefficient-row list.

Write \(C_j,S_j\) for the alternating cosine and sine polynomials
ending in degree j, and use the rational upper constants
\[
 \overline R=1.978787508,\quad\overline a=1.414575672,\quad
 \overline\sigma=1.415477291,\quad\overline c=.899214066.       \tag{44}
\]
Their positive-square comparisons with \(R,a_0,\sigma,c_0\)
are proved in the positive-BT theorem. Set
\[
 J(t)=\frac{C_{10}(t)-1}{2}+(\tfrac12-\overline a)S_9(t).
\]
For the small-total families (17),(29), take \(J_*=J\).
For (25), take \(J_*=J-.086(\theta-L)^4\); for (38), take
\(J_*=J-.302(\theta-L)^6\). The whole-domain inequalities
\(j(\theta)\ge J_*\) are respectively the exact axis formula,
the positive-BT large-total support bound, and the sixth-order
support bound in Section 6 of the far-EH theorem.

At the A split endpoint put \(C=m\). At the T split endpoint put
\[
                         C=m\{C_{12}(\theta)+\eta S_9(\theta)\}.
                                                                    \tag{45}
\]
In both cases C is a polynomial upper bound for the actual
tilted coefficient. For family (17), the nonradical baseline
polynomials are
\[
 \begin{split}
 A_A={}&2k+3l+\frac52-\overline c
                +(\frac52-\overline c)m+lJ_*,\\
 A_T={}&2k+3l+\frac52-\overline c\\
       &+m\{1+(\tfrac32-\overline c)C_{10}(\theta)
          +(\tfrac12+\eta(1-\overline c)-\overline\sigma)
                                                   S_9(\theta)\}.
 \end{split}                                                  \tag{46}
\]
Use three squared norms
\[
             P_H=1+k^2,\quad P_G=k^2+l^2,\quad P_B=l^2+m^2.
                                                                    \tag{47}
\]
For each other family use
\[
 \begin{split}
 A_A&=2k+3l+3+3m+lJ_*,\\
 A_T&=2k+3l+3+m\{1+2C_{10}(\theta)
                    +(\tfrac12+\tfrac32\eta-\overline\sigma)
                                                   S_9(\theta)\},
 \end{split}                                                  \tag{48}
\]
and append \(P_D=1+C^2\) to (47). These formulas collect all
circle half-shifts before making their Taylor replacements.

Let
\[
 g_*(s)=K S_{11}(s)+\beta(C_{10}(s)-1),\qquad
 G_*(s)=p g_*(s)-.00022.                                      \tag{49}
\]
Use \(g_*\) for (17),(25) and \(G_*\) for (29),(38).
Add this gain to A. At an equal-angle endpoint Z, set
\(s=\theta\) and make no further change. For a negative
endpoint \(V_i\), set \(\delta=\theta-s\), subtract from
the corresponding squared norm respectively
\[
                  2kS_{11}(\delta),\quad
                  2klS_{11}(\delta),\quad
                  2lmS_{11}(\delta),                         \tag{50}
\]
and add to A respectively
\[
             C_{10}(\delta)-1,\quad
             l\{C_{10}(\delta)-1\},\quad
             q_*\{C_{10}(\delta)-1\}.                         \tag{51}
\]
The third case occurs only in families (25),(38), and uses
\[
                         q_*=l+.15(h-\theta)\ge\max(l,m).     \tag{52}
\]
For (25) this is the already proved positive-BT bound.
For (38), \(q_*-m\) is linear and has minimum .0006 at h.
Thus (51) has the lower-bound direction.

The positive endpoints occur only in (29) with \(s=v\),
\(\delta=v-\theta\ge0\). For H,B,D respectively, add to
the corresponding squared norm
\[
                     2kS_9(\delta),\quad
                     2lmS_9(\delta),\quad
                     2C S_9(\delta),                         \tag{53}
\]
and add to A respectively
\[
 (k,l,1)_i\{C_{10}(\delta)+S_{11}(\delta)-1\}
                                            -\varepsilon\delta.
                                                                    \tag{54}
\]
Here the smaller coefficients are exactly k,l,1, by (30) and
the \(c>1\) observation before (35). Every squared-norm
polynomial is an upper bound for its actual squared norm.

The complete intrinsic endpoint set is:

| Family | Whole interval for \(\theta\) | Gain argument and alternatives | Number, including A/T splits |
|---|---|---|---:|
| (17) | \([0,v]\) | \(s=\theta\), Z | 2 |
| (17) | \([v,L]\) | \(s=v\), \(V_H\) | 2 |
| (25) | \([L,h]\) | \(s=v\), \(V_H,V_G,V_B\) | 6 |
| (29) | \([0,v]\) | \(s=v\), \(U_H,U_B,U_D\) | 6 |
| (29) | \([v,u]\) | \(s=v\), \(V_H,V_G\); \(s=\theta\), Z | 6 |
| (38) | \([u,h]\) | \(s=v,u\), \(V_H,V_G,V_B\) | 12 |

For each row let b be its left endpoint and use the native
variable \(x=\theta-b\in[0,D]\). For every squared norm P put
\(P_0=P(0)\), and choose the unique positive multiple \(\rho\)
of \(10^{-12}\) satisfying
\[
  (\rho-\tfrac12 10^{-12})^2\le P_0
                       <(\rho+\tfrac12 10^{-12})^2.           \tag{55}
\]
This is an exact integer prescription by positive rational
squaring. Define the rational cubic
\[
 w=([P]_{\le3}-P_0)/P_0,\qquad
       r=\rho[1+w/2-w^2/8+w^3/16]_{\le3}.                    \tag{56}
\]
There is no approximation premise for r: it is an explicitly
specified polynomial, used only after its positivity check.
For the resulting A, squared norms and masses define
\[
 \mathcal N=2A\prod_i r_i
          -\overline R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.     \tag{57}
\]
Positive masses and
\(\sqrt P\le(P+r^2)/(2r)\) show that each original endpoint
stress is at least \(\mathcal N/(2\prod_i r_i)\).

Here are compact exact coefficient bounds for the full endpoint
families. All unqualified numerator bounds apply simultaneously
to every listed A/T, sign and gain endpoint of that family.

| Family | Every mass exceeds | Whole-interval positivity certificate |
|---|---:|---|
| (17) | 1.15 | \(\mathcal N>.0049\) |
| (25), H or G | .83 | \(\mathcal N(0)>.0065\) and \((\mathcal N(x)-\mathcal N(0))/x>.004\) |
| (25), B | .83 | \(\mathcal N>.054\) |
| (29) | 1.01 | \(\mathcal N>.0122\) |
| (38) | .75 | \(\mathcal N>.0116\) |

For reproducibility, every displayed aggregate is the following
finite rational coefficient sum. If \(F(x)=\sum_n f_nx^n\), set
\[
 a_{n0}=4^{-n}\binom{2n}{n},\qquad
 a_{nj}=2\,4^{-n}\binom{2n}{n-j}\quad(1\le j\le n),
\]
zero for other indices, and
\[
 b_j=\sum_n f_nD^na_{nj},\qquad
       \mathcal C_D(F)=b_0-\sum_{j>0}|b_j|.                   \tag{58}
\]
The shifted Chebyshev identity and \(|T_j|\le1\) give
\(F\ge\mathcal C_D(F)\) on the entire interval.
Apply (58) directly to every mass and to the numerator, except
for H/G in (25), where it is applied to the exact first quotient.
Equations (44)--(58), including the integer prescription (55),
give all coefficients without a fitted or sampled value.
The maximum numerator degree is 39.

## 9. Completion

Sections 4--5 cover \(0\le s\le v\), with their zero-s scalar
endpoints inherited from the already proved positive-BT theorem
and all new endpoints proved in Section 8. Sections 6--7 cover
\(v\le s\le u\), and Section 8 proves every remaining endpoint.
All scalar relaxations therefore have strictly positive demand
minus support, contradicting the nonpositive weighted stress
required by the original separating inequalities.

This proves the theorem for arbitrary actual TD0 error, either
HG owner, all selected nonnegative A totals, and all weak ties.
The genuine negative-EH entry cut lies inside the closed domain
proved here. Every circle and witness used is original; only
the scalar lower bound has been concentrated. The result does
not assert a simultaneous negative A total or a negative DE3
endpoint. It uses no angle mesh, optimizer certificate, Lean
compilation or CI.
