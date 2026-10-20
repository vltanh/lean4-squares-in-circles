# A fixed negative-EH multiplier on the far low-total interval

## 1. Scalar scope and conclusion

Use the constants and the functions \(S,\overline S,N,U,V,\Psi,j\)
of [the negative-DE concentration note](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md):
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad K=\frac{13}{12},\quad \eta=\frac{293}{1000},
 \quad d_0=\sqrt{Q/2}-1<.4.
\tag{1}
\]
This is a scalar concentration lemma for the fixed-EH-multiplier
reduction. Its inputs are
\[
 0\le\theta=a+z\le\frac14,\quad
 \frac1{10}\le s\le\frac14,\quad p=\frac{201}{200},
 \quad \varepsilon=\frac1{200},
\tag{2}
\]
and the following coefficients, held fixed when s or the split
\(a+z=\theta\) varies:
\[
 k=\frac{121}{200}=.605,\qquad
 l=1-.36\theta,\qquad c=1.11-.77\theta,\qquad
 m=c(\cos z+\eta\sin z).
\tag{3}
\]
Write
\[
\begin{split}
 B_0(z)={}&k+2l+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(l,k)
          -\overline S(m,l)-\overline S(1,c),\\
 g(s)&=K\sin s-.656(1-\cos s),\\
 C(s)&=B_0(z)+l j(a)+p g(s)-.00022.
\end{split}
\tag{4}
\]
The full D-circle support is used throughout, including when
\(c>1\). This is a lower bound for demand minus actual support.
The three ordinary norm pairs are H=\((k,1)\), G=\((k,l)\),
and B=\((l,m)\).

The geometric input is the fixed-multiplier force bound with
H correction
\[
 H_p(s)=p[1+.656\cos s+K\sin s]-1.656
       -R\{\sqrt{p^2+k^2}-\sqrt{1+k^2}\}.
\tag{5}
\]
Its positive H singleton is bounded by \(U_{k,p}\), its negative
H singleton by \(V_{k,1}\). The D singleton has positive bound
\(-d_0P\) and a negative bound at least \(V_{k,1}\).
The remaining ordinary arguments satisfy
\[
 P\le h-\theta,\quad N\le h-s,\quad P-N=s-\theta.
\tag{6}
\]
These are explicit inputs; this note does not infer them from a
three-block theorem with a different original owner.

We prove that its scalar minimum reduces to the ten functions
in Section 6. Only \(s=.1\) and the intrinsic crossing
\(s=\theta\) remain, followed by \(z=0,\theta\).
Every decimal below denotes an exact rational.

## 2. Coefficient ranges and the H correction

The coefficient bounds are
\[
 .91\le l\le1,\quad .9175\le c\le1.11,\quad
 c>l,\quad c\le m\le1.11,\quad 1< m/l<1.17.
\tag{7}
\]
Indeed, \(c-l=.11-.41\theta\ge.0075\), and
\(\cos z+\eta\sin z\ge1\) on \([0,.25]\).
Also
\[
 m\le c(1+\eta\theta)
       =1.11-.44477\theta-.22561\theta^2,
\]
while
\[
 1.17l-c(1+\eta\theta)
              =.06+.02357\theta+.22561\theta^2>0.
\tag{8}
\]
Thus all three pairs have smaller coefficient at least .605,
larger coefficient at most 1.11, and ratio \(q_i/p_i<5/3\).
The usual admissibility bounds \(k\le l\le2k\),
\(k\le c\le2\), and \(1/2\le l/m\le2\) hold.

The norm derivative bound
\[
 \frac{Rr}{\sqrt{r^2+k^2}}<1.7
                   \qquad(1\le r\le201/200)
\]
holds by positive squaring; the reserve at \(r=201/200\) is
\(2193061/100000000\). Consequently
\[
                         H_p(s)\ge p g(s)-.00022.
\tag{9}
\]
Its constant difference from \(p g(s)\) is at least
\(.005(1.656-1.7)=-.00022\).

Moreover
\[
 U_{k,p}(t)\ge U_{k,1}(t)-\varepsilon t
                    \qquad(0\le t\le h).
\tag{10}
\]
Differentiate first in t and then in the larger coefficient:
\[
 \left|\partial_r U_{k,r}'(t)\right|
 =\frac{Rk^2\cos t(k+r\sin t)}
        {(k^2+r^2+2kr\sin t)^{3/2}}<1.
\tag{11}
\]
For example its numerator is below 1.216 and its denominator
above 1.58, even on the larger range
\(.6\le k\le.68,\ 1\le r\le1.005\).
Integrate in r and then t, using \(U_{k,r}(0)=0\).
We may therefore use three unmodified ordinary pairs and
subtract \(\varepsilon P\) from the total remaining positive
mass. This only enlarges the negative charge from the actual
positive H contribution.

## 3. Ordinary-angle concentration

Separate concavity of U, V and \(\Psi\), including virtual
singleton arguments, gives the alternatives
\[
\begin{array}{ll}
 V_i(\theta-s),&s\le\theta,\\
 U_i(s-\theta)-\varepsilon(s-\theta),&s\ge\theta,\\
 \Psi_i(h-\theta,h-s)-\varepsilon(h-\theta),&\\
 U_i(h-\theta)+V_j(h-s)-\varepsilon(h-\theta).&
\end{array}
\tag{12}
\]
They are added to \(C(s)\). The positive D term may initially
be included among the positive alternatives.
Missing singleton arguments are enlarged only algebraically;
no new original separating witness is asserted.
Replacing the exact zero-angle D support by the full-circle
support in (4) weakens the same inequality and therefore
preserves the stated D minorants.

The D positive term can be omitted:
\[
 U_H'(0)=k-\frac{Rk}{\sqrt{1+k^2}}<-.4.
\tag{13}
\]
The squared reserve is
\[
 Qk^2-(k+.4)^2(1+k^2)
                 =\frac{85580943}{1600000000}>0.
\]
Concavity gives \(U_H(t)<-.4t<-d_0t\) for \(t>0\).

Every B negative term is dominated by H:
\[
 V_B(t)\ge\frac{.87}{h}l\,t
              >1.025t\ge V_H(t)\qquad(t>0).
\tag{14}
\]
Use the universal \(V_{p,q}(h)>.87p\), concavity, \(l\ge.91\),
and \(V_H'(0)<1.025\). The squared reserve for the last slope
bound is \(3156041/1600000000\).
At t=0 all comparisons are non-strict.

All same-block terms are dominated by the corresponding pure
terms, including the \(\varepsilon\) charge. Every ratio is
less than \(5/3\), every smaller coefficient exceeds .6, and
\(N=h-s\le.6\). For \(P\le N\), the exact difference is
\[
 \Psi(P,N)-V(N-P)
 =p_i[(1-r\cos N)(\cos P-1)+(1-r\sin N)\sin P],
 \quad r=q_i/p_i.
\tag{15}
\]
It decreases with r. At \(r=5/3\) the first term is
nonnegative, and the second gives
\[
 \Psi(P,N)-V(N-P)
 \ge .6(1-\tfrac53\sin .6)\,.94P>.032P.
\tag{16}
\]
This pays \(\varepsilon P\).
For \(P\ge N\), the standard exact difference estimate gives
\[
\begin{split}
 \Psi(P,N)-U(P-N)
 &\ge p_i[(\phi(h)-r)(1-\cos N)+\phi'(h)\sin N]\\
 &>.6[.12-(\tfrac53-1.409)(.31)]\,.94N>.022N.
\end{split}
\tag{17}
\]
We used \(\tan(N/2)<.31\) and \(\sin N\ge.94N\).
This pays the extra charge \(\varepsilon N\).
At a zero mass the corresponding comparison is non-strict.

## 4. The negative angle and the separated alternatives

First,
\[
                         p g'(s)>.8917
                         \qquad(.1\le s\le.25).
\tag{18}
\]
Its derivative is negative, so substitute \(C_6(.25)\) and
\(S_5(.25)\) at the right endpoint.

The universal derivative inequality
\(U_i'(t)>-.72q_i\) on \(0\le t\le h\), proved in the
negative-DE concentration note, shows that every charged
pure-U function increases in s:
\[
 \frac{d}{ds}\{C(s)+U_i(s-\theta)-\varepsilon(s-\theta)\}
 >.8917-.72(1.11)-.005=.0875.
\tag{19}
\]
For \(s\le\theta\), every pure-V function is concave in s:
both \(p g(s)\) and \(V_i(\theta-s)\) are concave.
Its minimum is at \(s=.1\) or \(s=\theta\).

Every separated H/G alternative also increases in s. We use
the elementary whole-rectangle estimate
\[
 V'_{\kappa,q}(N)<.876
 \quad(.6\le\kappa\le.68,\ .91\le q\le1.3,\ .45\le N\le.6).
\tag{20}
\]
Concavity reduces to \(N=.45\). The derivative increases
with \(\kappa\), so set \(\kappa=.68\). It then decreases
with q. Its q derivative is
\[
 -\sin N+\frac{R\kappa^2\cos N(\kappa-q\sin N)}
                  {(\kappa^2+q^2-2\kappa q\sin N)^{3/2}}.
\tag{21}
\]
While the numerator in the second term is positive, that
term decreases with q. At q=.91 it is below .36, whereas
\(\sin .45>.4349\). If that numerator becomes nonpositive,
the sign is immediate. Thus q=.91 is the worst endpoint.
Using \(\sin .45<.435,\ \cos .45<.90045\), its norm is above
.8672, and
\[
 V'_{.68,.91}(.45)
 <-.91(.4349)
       +\frac{1.978788(.68)(.91)(.90045)}{.8672}<.876.
\tag{22}
\]
For (21), the norm cube is above .652 and the positive
numerator is below \(.36(.652)\).
Thus every separated derivative exceeds
\(.8917-.876=.0157\). The positive-mass charge is constant
in s for these alternatives.

It remains to discard separated alternatives at \(s=.1\).
Put \(P=h-\theta\). The universal U lower bound and the
coefficient ranges give
\[
 U_i(P)-\varepsilon P\ge-.60995P.
\]
Meanwhile the same endpoint-chord bound used in (14) gives,
for j=H,G,
\[
                    V_j(.6)>\frac{31581}{70000}.
\tag{23}
\]
For \(0\le\theta\le.1\), the separated increment is therefore
greater than
\[
 \frac{31581}{70000}-.60995(.7)
                    =\frac{33869}{1400000}>0.
\tag{24}
\]
It dominates the charged H pure-U term, which is nonpositive.
For \(.1\le\theta\le.25\), use
\(V_H(\theta-.1)\le1.025(\theta-.1)\). The difference between
the separated bound and that H pure-V term is at least
\[
\begin{split}
 \frac{31581}{70000}-.60995(.7-\theta)-1.025(\theta-.1)
 &\ge\frac{64203}{2800000}>0.
\end{split}
\tag{25}
\]
Hence no separated scalar certificate is needed.

All saturation has now been removed. The only s values
are .1 and the intrinsic crossing \(\theta\), when
\(\theta\ge.1\). In the pure-U alternatives, G is redundant
because \(l\le1\) and U decreases in its larger coefficient:
\(U_{k,l}\ge U_{k,1}\).

## 5. The full A/TD split

Perform these s reductions before varying the split.
At each retained s value the G/H terms are constant in the
split. After the B-negative replacement (14), the B-dependent
part is either
\[
 H_0(m)=\tfrac32m-R\sqrt{l^2+m^2}
\]
or
\[
 H_U(m)=\tfrac32m+l(\phi(t)-1)
              -R\sqrt{l^2+m^2+2lm\sin t},\quad 0\le t\le h.
\tag{26}
\]
Both are concave and have derivative greater than -.48.
Consequently composition with \(m(z)\), where \(m''=-m\),
contributes second derivative at most .48m.

The remaining split-dependent terms are
\(cW(z)-c\sigma\sin z+l j(a)\).
Since \(a+z=\theta\le.25<1/2\), the axis branch of j applies.
Use \(m<1.043c,\ \cos a,\cos z\ge31/32,\ \sigma-.5<.916\),
\(a_0-.5<.915\), and the weaker convenient \(c/l\le1.5\).
Their total second derivative divided by l is at most
\[
 1.5(.48\cdot1.043-\tfrac{31}{64})
       -\frac{31}{64}+1.374\theta
 \le-.1164775<0.
\tag{27}
\]
The combined estimate
\(.916(c/l)\sin z+.915\sin a\le1.374(a+z)\)
uses the fixed sum, so it remains valid up to \(\theta=.25\).
Every retained exact alternative is strictly concave on the
entire split interval. Its minimum is at \(z=0\) or \(z=\theta\).
The common H correction and positive-mass charge are independent
of the split.

## 6. The ten endpoint functions

At either \(z=0\) or \(z=\theta\), write
\[
 Z(s)=B_0(z)+l j(\theta-z)+p g(s)-.00022.
\tag{28}
\]
For \(0\le\theta\le.1\), certify
\[
 Z(.1)+U_H(.1-\theta)-.005(.1-\theta),\qquad
 Z(.1)+U_B(.1-\theta)-.005(.1-\theta).
\tag{29}
\]
For \(.1\le\theta\le.25\), certify
\[
 Z(.1)+V_H(\theta-.1),\qquad
 Z(.1)+V_G(\theta-.1),\qquad Z(\theta).
\tag{30}
\]
There are four low and six upper functions, counting both
split endpoints. The coincident values at \(\theta=.1\)
agree. Their positivity is a separate scalar-certificate
task. This reduction uses whole-interval inequalities and
intrinsic extrema, without a sampled-angle premise.
