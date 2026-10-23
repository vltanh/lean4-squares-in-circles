# The remaining genuine negative EH1 interval with positive intermediate errors

## 1. Scope

Use the fixed-original-witness G0--G2 necessary system at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\]
The four sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative. Retain
\[
 HG\in\{0,2\},\qquad BT=2,\quad TD=2,\quad DE=2,\quad EH=1.
\tag{1}
\]
The TD2 error is \(z\ge0\). The EH1 error is \(-s\), where
\[
 v:=\frac1{10}\le s\le u:=\frac14,\qquad
       a_E=\frac7{12},\quad 0\le b_E\le\frac{39}{250}.
\tag{2}
\]
These closed E conditions contain every genuine negative EH1:
the negative-primary entry argument supplies them whenever an
actual EH0 cannot already be selected. See Section 2 of
[the mixed-negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).

At A permit no primary, a single nonnegative GA3 or AB2, or both
GA3 and AB2 with nonnegative signed total \(a\). The secondary A
owners keep arbitrary errors. A and T may have either sign and
either radial kind. Put \(\theta=a+z\). Assume the actual adjacent
inequalities and the captured variation conditions
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{3}
\]

There is no such necessary system. No frame order is assumed.
Together with
[the small-error theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SMALL_ERROR_EXCLUSION.md),
this excludes the whole genuine negative-EH interval in the
stated A/TD class.

All decimal constants in this proof are exact rationals.

## 2. A constant EH multiplier

Use the supports and the ordinary norm functions of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md):
\[
\begin{gathered}
 K=\frac{13}{12},\quad \eta=\frac{293}{1000},\quad
 \beta=\frac{82}{125},\quad p=\frac{201}{200},\quad
 \varepsilon=\frac1{200},\\
 W(t)=\frac{1+\cos t+|\sin t|}{2},\quad
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2},\\
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 a_0=\sqrt{Q-\frac14}-\frac12.
\end{gathered}
\tag{4}
\]
The exact positive-A support function is
\[
 j(a)=
 \begin{cases}
 \frac12(\cos a-1)+(\frac12-a_0)\sin a,
                         &a\le a_{\rm ax},\\
 \sin a-2R\sin(a/2),&a\ge a_{\rm ax},
 \end{cases}
 \qquad a_{\rm ax}>1/2.
\tag{5}
\]
For two signed A primaries of nonnegative total, use
[their established combination](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
It gives the same \(l j(a)\) bound.

Give the original seven inequalities the weights
\[
                  (k,l,l,m,c,1,p),\qquad
                    m=c(\cos z+\eta\sin z).
\tag{6}
\]
The coefficients \(k,l,c\) will depend only on \(\theta\).
They remain fixed during every E-angle or A/TD split comparison.

DE2 contributes \(+b_E\); EH1 at \(-s\) contributes
\(-p a_E\sin s-p b_E\cos s\), besides the H primary force \(p\).
Since
\[
            p\cos s\le p C_4(v)<1,
 \qquad 1-pC_4(v)>.0000208,
\tag{7}
\]
the E force is at most
\(-p(7/12)\sin s+(1-p\cos s)(39/250)\).
After collecting the shifted H support constant, the change
from the unit-EH baseline is therefore at least
\[
\begin{split}
 H_p(s)={}&p\{1+\beta\cos s+K\sin s\}-(1+\beta)\\
          &-R\{\sqrt{p^2+k^2}-\sqrt{1+k^2}\}.
\end{split}
\tag{8}
\]
This is a direct sum of the original forces; no replacement
EH witness has been introduced.

All coefficient families below satisfy \(.6\le k\le.8\).
Positive squaring gives
\[
             \frac{Rr}{\sqrt{r^2+k^2}}<1.7
                     \qquad(1\le r\le p).
\]
Consequently, with
\[
 g(s)=K\sin s-\beta(1-\cos s),\qquad
                     G(s)=p g(s)-.00022,
\tag{9}
\]
one has \(H_p(s)\ge G(s)\). Indeed the constant loss is at
most \((p-1)1.7\), and
\((p-1)(1+\beta-1.7)=-.00022\).
The function G is strictly concave and
\[
                         G'(s)>.8917
                         \qquad(v\le s\le u).
\tag{10}
\]
For (10), its derivative decreases; substitute \(C_6(u)\)
and \(S_5(u)\) at the right endpoint.

## 3. Restoring the three ordinary norm blocks

For \(0<\xi\le\zeta\), write
\[
\begin{split}
 N_{\xi,\zeta}(t)&=\sqrt{\xi^2+\zeta^2+2\xi\zeta\sin t},\\
 U_{\xi,\zeta}(t)&=\xi(\cos t+\sin t-1)
                    -R\{N_{\xi,\zeta}(t)-N_{\xi,\zeta}(0)\},\\
 V_{\xi,\zeta}(t)&=\zeta(\cos t-1)
                    -R\{N_{\xi,\zeta}(-t)-N_{\xi,\zeta}(0)\},\\
 \Psi_{\xi,\zeta}(P,N)&=\xi(\cos P+\sin P-1)+\zeta(\cos N-1)\\
 &\hspace{18mm}-R\{N_{\xi,\zeta}(P-N)-N_{\xi,\zeta}(0)\}.
\end{split}
\tag{11}
\]
The three unmodified pairs are H=\((k,1)\), G=\((k,l)\),
and B=\((\min(l,m),\max(l,m))\).

For HG2 the H angular force is
\((p+k\sin t,k\cos t)\). At a negative argument its increment
is at least \(V_{k,1}\). To see this, first replace its
coefficient \(k(\cos t-1)\) by the smaller \(1(\cos t-1)\).
The remaining norm gain
\[
 \sqrt{r^2+k^2}-\sqrt{r^2+k^2-2rk\sin t}
\]
increases in \(r\in[1,p]\), by positive squaring:
the derivative comparison reduces to
\(\sin t\le2rk/(r^2+k^2)\). Here \(k/r\ge1/2\), so the
right side is at least \(4/5>\sin h\).

For a positive H argument,
\[
                 U_{k,p}(t)\ge U_{k,1}(t)-\varepsilon t.
\tag{12}
\]
Indeed
\[
 \left|\partial_r U'_{k,r}(t)\right|
 =\frac{Rk^2\cos t(k+r\sin t)}
         {(k^2+r^2+2kr\sin t)^{3/2}}<1.
\tag{13}
\]
One uniform positive-square certificate for (13) is
\[
 Q(.8)^4\{.8+p(.645)\}^2<\{1+(.8)^2\}^3.
\]
The ratio \(k^2(k+A)/(1+k^2)^{3/2}\), with
\(A=p(.645)\), increases for \(k\le.8\): its derivative
has positive numerator \(k(3k+2A-Ak^2)\).
Thus this endpoint bound covers the full k interval.
Integrate (13) in r and then t.

For HG0 the H angular argument is absent. Allowing the missing
argument to vary, as a virtual zero, only enlarges the scalar
minimization. Thus either HG owner permits the same three
ordinary blocks, with an extra lower charge
\(-\varepsilon P\) on the total remaining positive mass.

Use full-circle support also for D at zero. The baseline is
\[
\begin{split}
 B_0(a,z)={}&k+2l+m+cW(z)+2-c\sigma\sin z+l j(a)\\
 &-\overline S(1,k)-\overline S(l,k)
       -\overline S(m,l)-\overline S(1,c).
\end{split}
\tag{14}
\]
The exact sorted-D minorants from Section 4 of the TD2
concentration theorem remain valid: a positive D argument
has lower bound \(-d_0P_D\), where \(d_0=\sqrt{Q/2}-1<.4\);
a negative D argument has lower bound \(V_H(N_D)\).
Replacing only its zero-angle support by the larger full-circle
support weakens the same lower stress bound and leaves both
minorants valid.

After removing the A primary arguments, TD and EH, (3) gives
\[
        P\le h-\theta,\qquad N\le h-s,\qquad N-P=\theta-s.
\tag{15}
\]
For opposite-signed A primary errors, their removed positive
variation is at least a; removing their negative variation
only weakens the stated cap. The usual virtual-angle enlargement
also covers the absence of an A primary.

Separate concavity in each norm block and the two simplex
concentrations now apply to the unmodified pairs. Their
intrinsic alternatives, added to \(B_0+G(s)\), are
\[
\begin{array}{ll}
 V_i(\theta-s),&s\le\theta,\\
 U_i(s-\theta)-\varepsilon(s-\theta),&s\ge\theta,\\
 \Psi_i(h-\theta,h-s)-\varepsilon(h-\theta),&\\
 U_i(h-\theta)+V_j(h-s)-\varepsilon(h-\theta).&
\end{array}
\tag{16}
\]
The positive D minorant is initially included in the positive
alternatives. This is a relaxation of the same weighted sum
of original inequalities, so a feasible system requires at
least one of these lower stresses to be nonpositive.

## 4. The low total-angle family

For \(0\le\theta\le u\), choose
\[
                k=.605,\qquad l=1-.36\theta,\qquad
                         c=1.11-.77\theta.
\tag{17}
\]
The whole-angle reduction proved in
[the far-low concentration lemma](HAND_G3_CORE_E_NEGATIVE_EH1_FAR_LOW_ANGLE_CONCENTRATION.md)
applies exactly to (8), (14)--(17), including full D support.
Its coefficient ranges are
\[
 .91\le l\le1,\quad .9175\le c\le1.11,\quad
                  c\le m\le1.11,\quad 1<m/l<1.17.
\]
It removes every same-block and separated alternative, using
strict derivative and endpoint comparisons; it does not retain
an artificial \(s=u\) endpoint.

Put \(Z(s)=B_0(a,z)+G(s)\). The resulting obligations are,
at each of the two split endpoints
\((a,z)=(\theta,0)\) and \((0,\theta)\),
\[
\begin{array}{ll}
 Z(v)+U_H(v-\theta)-\varepsilon(v-\theta),&
                          0\le\theta\le v,\\
 Z(v)+U_B(v-\theta)-\varepsilon(v-\theta),&
                          0\le\theta\le v,\\
 Z(v)+V_H(\theta-v),\quad Z(v)+V_G(\theta-v),\quad Z(\theta),
                    &v\le\theta\le u.
\end{array}
\tag{18}
\]
There are ten functions. Section 7 gives their explicit positive
whole-interval numerator certificates.

## 5. The high total-angle family

For \(u\le\theta\le h\), choose
\[
       k=.505+.4\theta,\qquad
       l=.9525-.17\theta,\qquad
       c=.9645-.188\theta.
\tag{19}
\]
These agree with (17) at u. Their endpoint bounds are
\[
\begin{gathered}
 .605\le k\le.785,\quad .8335\le l\le.91,\quad
 .8329\le c\le.9175,\qquad .99<c/l<1.01,\\
 .95c<m<1.043c,\qquad k<\min(l,m),\qquad \max(l,m)<1.
\end{gathered}
\tag{20}
\]
For the m bounds use concavity of
\(\cos z+\eta\sin z\), its two endpoints, and
\(1+\eta^2<1.043^2\). In particular
\[
       \min_i p_i\ge.605,\quad \max_i q_i=1,\quad
       p_i/q_i>.6,\quad q_i/p_i<5/3,\quad m/l<23/20.
\tag{21}
\]
The original concentration admissibility conditions
\(k\le l\le2k,\ k\le c\le2\) are immediate.

Here \(s\le u\le\theta\), so \(P\le N\) at every saturated
alternative, and \(N=h-s\le.6\).
The exact same-block identity gives
\[
\begin{split}
 \Psi_i(P,N)-V_i(N-P)
 =p_i\{(1-r\cos N)(\cos P-1)+(1-r\sin N)\sin P\},
 \quad r=q_i/p_i.
\end{split}
\tag{22}
\]
This decreases with r. At \(r=5/3\) the first term is
nonnegative, because \((5/3)\cos(.6)>1\).
Using \(\sin(.6)<.565\) and \(\sin P>.94P\),
\[
             \Psi_i(P,N)-V_i(N-P)>.032P
                                            \qquad(P>0).
\tag{23}
\]
This pays \(\varepsilon P\). At \(P=0\) equality is harmless.

For separated alternatives we use the uniform derivative bound
\[
 V'_{\xi,\zeta}(t)>1.03\xi
       \quad\left(\frac35\le\frac{\xi}{\zeta}\le1,\
                    0\le t\le\frac35\right).
\tag{24}
\]
Concavity of V reduces to \(t=.6\). Write \(r=\xi/\zeta\).
The exact Taylor bounds
\[
 .56464<\sin(.6)<.56465,\qquad \cos(.6)>.82533
\]
reduce (24), by positive squaring, to positivity of
\[
 P(r)=Q r^2(.82533)^2
       -(1.03r+.56465)^2(1+r^2-2r(.56464)).
\tag{25}
\]
At \(r=.6+x\), \(0\le x\le.4\), its coefficients are
\[
\begin{split}
 a_0&=\frac{3560337820289}{625000000000000},&
 a_1&=\frac{89945678458213}{62500000000000},\\
 a_2&=\frac{9306058820721}{25000000000000},&
 a_3&=-\frac{313910731}{125000000},&
 a_4&=-\frac{10609}{10000}.
\end{split}
\]
They satisfy
\[
 a_0>.0056965,\quad a_2>0,\quad
            a_1+a_3(.4)^2+a_4(.4)^3>.9694>0.
\tag{26}
\]
Thus \(P(.6+x)>0\) on the whole interval.

The universal positive bound \(U_i(P)\ge-.545q_iP\),
together with (21), (24), gives
\[
\begin{split}
 U_i(P)+V_j(N)-\varepsilon P
 &\ge V_j(N-P)+\{1.03(.605)-.545-.005\}P\\
 &=V_j(N-P)+.07315P.
\end{split}
\tag{27}
\]
The D positive minorant is covered by the same bound because
\(d_0<.4<.545\). Hence all high alternatives reduce to
\[
 B_0(a,z)+G(s)+V_i(\theta-s),
                                  \qquad i=H,G,B.
\tag{28}
\]
For each fixed split this is concave in s, so only
\(s=v,u\) remains.

For either retained s, the B-dependent part is
\[
 \frac32m-R\sqrt{l^2+m^2}
\]
or
\[
 \frac32m+\max(l,m)(\cos\delta-1)
               -R\sqrt{l^2+m^2-2lm\sin\delta},
                  \qquad \delta=\theta-s.
\tag{29}
\]
Both are concave and increasing for \(m/l\le23/20\) and
\(0\le\delta\le h\), as proved in Section 6 of
[the two-positive split lemma](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
Those local derivative comparisons use only the displayed
ratio and angle ranges; the balanced-envelope hypotheses from
its preceding section are not needed here.
Since \(m''(z)=-m(z)\), their compositions are concave.
The remaining second derivative is at most
\[
 c\{-\tfrac12\cos z+.916\sin z\}
       +l\{-\tfrac12\cos a+.92\sin a\}
        <-\frac{531}{25000}l<0.
\tag{30}
\]
Use \(a+z\le h\), \(\sin a+\sin z\le h\), each cosine
greater than .7648, and \(.9<c/l<1.1\).
The possible derivative jump at \(m=l\) is downward.
Thus the minimum of (28) is at one of the two A/TD split
endpoints. There are twelve high endpoint functions:
three pairs, two s endpoints, and two split endpoints.

## 6. Exact polynomial conventions and common baselines

Write \(S_j,C_j\) for the alternating sine and cosine
polynomials ending in degree j. Put
\[
\begin{gathered}
 S_-=S_{11}(\theta),\quad S_+=S_9(\theta),\quad
 C_-=C_{10}(\theta),\quad C_+=C_{12}(\theta),\\
 \overline R=1.978787508,\quad
 \overline a=1.414575672,\quad
 \overline\sigma=1.415477291,\qquad L=\frac16,\\
 J_0=\tfrac12(C_--1)+(\tfrac12-\overline a)S_+,\qquad
 J_1=J_0-.302(\theta-L)^6,\\
 G_*(x)=p\{K S_{11}(x)+\beta(C_{10}(x)-1)\}-.00022.
\end{gathered}
\tag{31}
\]
Positive squaring proves the three radical upper bounds.
The exact support comparison in Section 5 of
[the negative-DE endpoint theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md)
gives \(j(\theta)\ge J_0\) on \([0,u]\) and
\(j(\theta)\ge J_1\) on \([u,h]\). The sixth-order allowance
uses only
\[
 \frac{\overline R\,h(h-\tfrac12)^2}{8(h-L)^6}<.302.
\]
Also \(G_*(x)\le G(x)\) on every argument interval used below.

Superscripts A and T denote the split endpoints
\((a,z)=(\theta,0)\) and \((0,\theta)\).
For T define
\[
\begin{gathered}
 m_-=c(C_-+\eta S_-),\quad
 m_+=c(C_++\eta S_+),\quad
 \mu=c(C_4(\theta)+\eta S_5(\theta)),\\
 B=2k+3l+\frac32m_-+\frac c2+3
       +\frac c2(1+C_-+S_-)-c\overline\sigma S_+.
\end{gathered}
\tag{32}
\]
For A define
\[
 m_-=m_+=\mu=c,\qquad
                  B=2k+3l+3c+3+lJ,
\tag{33}
\]
where \(J=J_0\) in the low family and \(J=J_1\) in the high
family. These B polynomials include all four shifted support
constants.

The unrotated squared-norm upper bounds and positive auxiliaries
are
\[
\begin{gathered}
 P_H=1+k^2,\quad P_G=k^2+l^2,\quad
 P_B=m_+^2+l^2,\quad P_D=1+c^2,\\
 r_H=.8+.6k,\quad r_G=.62k+.7846l,\quad
 r_B=.7071(l+\mu),\quad r_D=.72+.694c.
\end{gathered}
\tag{34}
\]
For polynomials \(E,r_i,P_i\), with \(r_i>0\), define
\[
\begin{split}
 D&=2\prod_i r_i,\\
 \mathcal N(E;\mathbf r;\mathbf P)
       &=DE-\overline R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.
\end{split}
\tag{35}
\]
The elementary inequality
\(\sqrt{P_i}\le(P_i+r_i^2)/(2r_i)\) shows that the associated
stress is at least \(\mathcal N/D\).
All unmentioned entries of \(\mathbf r,\mathbf P\) in the
formulas below are the corresponding entries of (34).
The notation \(\mathcal N_i(E;r,P)\) replaces just entry i;
\(\mathcal N_0(E)\) replaces none.

For an interval \(I=[b,c]\), define its coefficient aggregate by
\[
 f\left(\frac{b+c}{2}+\frac{c-b}{2}x\right)
       =\sum_{j=0}^{n}a_jT_j(x),\qquad
       \mathcal C_I(f)=a_0-\sum_{j=1}^{n}|a_j|.
\tag{36}
\]
This is a lower bound for f on I. The coefficients are obtained
by polynomial expansion, using
\[
 x^n=2^{1-n}\!\!\sum_{0\le j<n/2}\binom nj T_{n-2j}(x)
       +\begin{cases}2^{-n}\binom n{n/2},&n\text{ even},\\
                     0,&n\text{ odd}.
         \end{cases}
\tag{37}
\]
For \(n=0\) this formula gives the constant one.
Thus every aggregate below is one finite rational coefficient
sum over its whole interval.

## 7. The ten low endpoint numerators

Use (17) and the low common data (31)--(34).
For \(\theta\in[0,v]\), put \(\delta=v-\theta\), and define
\[
\begin{split}
 P_{H,+}&=P_H+2kS_9(\delta),\\
 r_{H,+}&=.836C_2(\delta)+.548\{k+S_3(\delta)\},\\
 N_{LUH}&=\mathcal N_H\bigl(
 B+G_*(v)+k\{C_{10}(\delta)+S_{11}(\delta)-1\}
                -\varepsilon\delta;\ r_{H,+},P_{H,+}\bigr),\\
 P_{B,+}&=P_B+2lm_+S_9(\delta),\\
 r_{B,+}&=.64lC_2(\delta)+.768\{\mu+lS_3(\delta)\},\\
 N_{LUB}&=\mathcal N_B\bigl(
 B+G_*(v)+l\{C_{10}(\delta)+S_{11}(\delta)-1\}
                -\varepsilon\delta;\ r_{B,+},P_{B,+}\bigr).
\end{split}
\tag{38}
\]
The B positive coefficient is l because \(l<m\) throughout
the low family.

For \(\theta\in[v,u]\), put \(\delta=\theta-v\), and define
\[
\begin{split}
 P_{H,-}&=P_H-2kS_{11}(\delta),\\
 r_{H,-}&=.89C_2(\delta)+.456\{k-S_3(\delta)\},\\
 N_{LVH}&=\mathcal N_H\bigl(
             B+G_*(v)+C_{10}(\delta)-1;\ r_{H,-},P_{H,-}\bigr),\\
 P_{G,-}&=P_G-2klS_{11}(\delta),\\
 r_{G,-}&=.89lC_2(\delta)+.456\{k-lS_3(\delta)\},\\
 N_{LVG}&=\mathcal N_G\bigl(
           B+G_*(v)+l\{C_{10}(\delta)-1\};\ r_{G,-},P_{G,-}\bigr),\\
 N_{LZ}&=\mathcal N_0\bigl(B+G_*(\theta)\bigr).
\end{split}
\tag{39}
\]

Every auxiliary has its corresponding aggregate greater
than .6. The exact positive aggregate bounds are:

| Split | Numerator | Interval | Degree | Lower aggregate |
|---|---|---|---:|---:|
| A | \(N_{LUH}\) | \([0,v]\) | 17 | \(>.0441112\) |
| A | \(N_{LUB}\) | \([0,v]\) | 18 | \(>.0508864\) |
| A | \(N_{LVH}\) | \([v,u]\) | 17 | \(>.0293761\) |
| A | \(N_{LVG}\) | \([v,u]\) | 17 | \(>.0165940\) |
| A | \(N_{LZ}\) | \([v,u]\) | 14 | \(>.0145527\) |
| T | \(N_{LUH}\) | \([0,v]\) | 31 | \(>.0098274\) |
| T | \(N_{LUB}\) | \([0,v]\) | 28 | \(>.0145059\) |
| T | \(N_{LVH}\) | \([v,u]\) | 31 | \(>.0246572\) |
| T | \(N_{LVG}\) | \([v,u]\) | 31 | \(>.0220630\) |
| T | \(N_{LZ}\) | \([v,u]\) | 28 | \(>.0201415\) |

These prove all ten inequalities (18).

## 8. The twelve high endpoint numerators

Use (19), the high common data, and \(s=v\) or \(s=u\).
Put \(\delta=\theta-s\). To bound the B cosine coefficient, set
\[
                         q_*=l+.15(h-\theta).
\tag{40}
\]
This is at least \(\max(l,m)\). For A, the linear difference
\(q_*-c\) has its minimum .0006 at h. For T, positive Taylor
bounds and one exact aggregate give
\[
 \mathcal C_{[u,h]}
       \{q_*-c(C_4(\theta)+\eta S_5(\theta))\}>.0006290.
\tag{41}
\]
Since \(\cos\delta-1\le0\), replacing \(\max(l,m)\) by
\(q_*\) is a lower-bound replacement.

Define
\[
\begin{split}
 P_{H,-}&=P_H-2kS_{11}(\delta),\\
 r_{H,-}&=.94C_4(\delta)+.3412\{k-S_5(\delta)\},\\
 N_{HH}^{s}&=\mathcal N_H\bigl(
             B+G_*(s)+C_{10}(\delta)-1;\ r_{H,-},P_{H,-}\bigr),\\
 P_{G,-}&=P_G-2klS_{11}(\delta),\\
 r_{G,-}&=.895lC_4(\delta)+.446\{k-lS_5(\delta)\},\\
 N_{HG}^{s}&=\mathcal N_G\bigl(
           B+G_*(s)+l\{C_{10}(\delta)-1\};\ r_{G,-},P_{G,-}\bigr),\\
 P_{B,-}&=P_B-2lm_-S_{11}(\delta),\\
 r_{B,-}&=.82lC_4(\delta)+.572\{\mu-lS_5(\delta)\},\\
 N_{HB}^{s}&=\mathcal N_B\bigl(
          B+G_*(s)+q_*\{C_{10}(\delta)-1\};\ r_{B,-},P_{B,-}\bigr).
\end{split}
\tag{42}
\]
Each squared-norm polynomial is an upper bound: positive
terms use upper Taylor bounds, and subtracted positive
products use lower ones. Every auxiliary has its
\([u,h]\) aggregate greater than .6.

All twelve whole-interval coefficient comparisons are positive:

| Split | s | Numerator | Degree | \(\mathcal C_{[u,h]}\) |
|---|---:|---|---:|---:|
| A | \(v\) | \(N_{HH}^{v}\) | 19 | \(>.0255999\) |
| A | \(v\) | \(N_{HG}^{v}\) | 20 | \(>.0155563\) |
| A | \(v\) | \(N_{HB}^{v}\) | 20 | \(>.1028199\) |
| T | \(v\) | \(N_{HH}^{v}\) | 33 | \(>.0302465\) |
| T | \(v\) | \(N_{HG}^{v}\) | 34 | \(>.0223385\) |
| T | \(v\) | \(N_{HB}^{v}\) | 29 | \(>.0474660\) |
| A | \(u\) | \(N_{HH}^{u}\) | 19 | \(>.0104322\) |
| A | \(u\) | \(N_{HG}^{u}\) | 20 | \(>.0132153\) |
| A | \(u\) | \(N_{HB}^{u}\) | 20 | \(>.0132561\) |
| T | \(u\) | \(N_{HH}^{u}\) | 33 | \(>.0147124\) |
| T | \(u\) | \(N_{HG}^{u}\) | 34 | \(>.0198910\) |
| T | \(u\) | \(N_{HB}^{u}\) | 29 | \(>.0166633\) |

These prove (28) at every intrinsic E-angle and A/TD split
endpoint. Section 5 therefore proves positivity throughout
the high family.

## 9. Completion

The low concentration lemma reduces (16) to (18), and Section 7
proves all those functions positive. Section 5 reduces the
high family to (28) at \(s=v,u\) and the two split endpoints;
Section 8 proves every resulting function positive.
All norm denominators are positive.
This contradicts the nonpositive weighted stress required by
the original separating inequalities and proves Section 1.

The result uses intrinsic concavity endpoints and explicit
whole-interval rational coefficient sums. It has no sampled-angle
or optimization premise.
With the small-error theorem it covers every genuine negative
EH1 in the stated nonnegative-A-total, nonnegative-TD2 class.
It retains BT2 and DE2; it makes no further assertion about
simultaneous negative E primaries, a negative A-primary total,
or an arbitrary TD0 error.
