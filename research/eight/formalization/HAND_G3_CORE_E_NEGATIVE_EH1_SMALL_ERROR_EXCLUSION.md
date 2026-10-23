# A small genuine negative EH1 with positive intermediate errors

## 1. Scope

Use the fixed-original-witness G0--G2 boundary, the circle ceiling
\(Q=9789/2500\), and the variation bound \(h=7/10\). The four
sorted outer states H, G, B and D have signed tangents respectively
positive, negative, negative and negative. Retain

\[
 HG\in\{0,2\},\qquad BT=2,\qquad TD=2,\qquad DE=2,\qquad EH=1.
\tag{1}
\]

The TD2 error is \(z\ge0\), and the EH1 error is \(-s\), where
\(0\le s\le v:=1/10\). At A permit no primary, a single
nonnegative GA3 or AB2, or both GA3 and AB2 with nonnegative
signed total \(a\). Secondary A owners retain arbitrary errors.
Put \(\theta=a+z\). A and T have either sign and either radial
kind. Assume the genuine negative-EH entry conditions

\[
          a_E=\frac7{12},\qquad 0\le b_E\le\frac{39}{250}.
\tag{2}
\]

The negative-primary entry argument gives (2) whenever an actual
negative EH1 cannot already be replaced by an actual EH0; see
Section 2 of
[the mixed-negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
The closed conditions in (2) are a harmless enlargement.

There is no such necessary system satisfying the actual adjacent
inequalities and

\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{3}
\]

This result has no frame-order assumption. It uses only these
inputs and so also applies after a transport preserving them.
The rest of the genuine negative-EH interval, \(v<s<1/4\), is
not asserted by this note.

## 2. The retained E contribution

Use the constants, circle supports, and functions of
[the negative-DE endpoint theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md):

\[
 R=\sqrt Q,\quad K=\frac{13}{12},\quad
 \eta=\frac{293}{1000},\quad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\quad L=\frac16.
\]

Give both E edges multiplier one. The EH1 projection is
\(a_H-a_E\sin s-b_E\cos s\), while DE2 supplies \(+b_E\).
After the EH primary argument is removed from the H norm, its
net demand contribution is at least

\[
 \begin{split}
 W(s)-1+\frac7{12}\sin s-b_E(1-\cos s)
 &\ge g(s),\\
 g(s)&:=K\sin s-\frac{82}{125}(1-\cos s).
 \end{split}
\tag{4}
\]

The H force remaining from EH is its unrotated primary force.
Thus the three ordinary norm blocks and the exact D minorant are
unchanged. With weights \((k,l,l,m,c,1,1)\), where
\(m=c(\cos z+\eta\sin z)\), the baseline is

\[
\begin{split}
 B_0(a,z)={}&k+2l+m+cW(z)+2-c\sigma\sin z+l j(a)\\
 &-\overline S(1,k)-\overline S(l,k)
       -\overline S(m,l)-S(1,c).
\end{split}
\tag{5}
\]

Here \(j\) is the exact positive-A support function. Its signed
two-primary version is the established comparison in
HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md.

Use precisely the two continuous coefficient families (16)--(17)
of the negative-DE endpoint theorem, with their printed whole
interval range proofs. They depend on \(\theta\), and are held
fixed during every subsequent split or E-angle variation.

After deleting the A-primary arguments, TD and EH, the remaining
positive and negative masses obey

\[
 P\le h-\theta,\qquad N\le h-s,\qquad N-P=\theta-s.
\tag{6}
\]

The three pairs are H: \((k,1)\), G: \((k,l)\), and
B: \((\min(l,m),\max(l,m))\). Use their functions \(U_i,V_i\)
from (11) of the endpoint theorem and the joint increment

\[
 \Psi_i(P,N)=p_i(\cos P+\sin P-1)+q_i(\cos N-1)
       -R\{N_i(P-N)-N_i(0)\}.
\tag{7}
\]

The established two simplex concentrations apply with (6).
They leave pure V terms for \(s\le\theta\), pure U terms for
\(s\ge\theta\), and the intrinsic same-block and separated
terms at \(P=h-\theta,N=h-s\). A positive D allocation has its
usual lower bound \(-(c_0-1/2)P\). Each resulting stress is
\(B_0+g(s)\) plus the indicated increment.

## 3. Low total angle: reduction in s

For \(0\le\theta\le L\), the coefficient family gives

\[
 \frac23<k<.757,\quad 1<l\le c\le m<1.864,\quad
 l<1.352,\quad k/l<.68,\quad m/l<1.38.
\tag{8}
\]

The new ratio follows directly by writing \(x=L-\theta\):
the polynomial \(.68l-k\) has positive constant, and its
linear-plus-quadratic part is positive on \([0,L]\).
The bound on m, including arbitrary \(z\le\theta\), is
proved in Section 5 of
[the negative-DE concentration note](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md).

Throughout \(0\le s\le v\),

\[
                  g'(s)>1.012,\qquad g''(s)<0.
\tag{9}
\]

Indeed \(g'\) decreases and
\(K C_{10}(v)-.656 S_9(v)>1.012\).

Every pure U term increases for \(s\ge\theta\). To see this,
the whole-interval concavity of U reduces its derivative to
\(t=v\). If \(r=p/q\in[1/2,1]\), then

\[
 \frac{U'(v)}q
 =r(\cos v-\sin v)
       -\frac{Rr\cos v}{\sqrt{1+r^2+2r\sin v}}>-.5.
\tag{10}
\]

A fully rational check uses \(\cos v-\sin v>.895\),
\(\sin v>.0998\), and \(\cos v\le1\). Squaring the positive
sides gives the polynomial

\[
\begin{split}
 &(\tfrac12+.895r)^2(1+r^2+.1996r)-Qr^2\\
 &\quad=\frac14+.9449r-2.685933r^2
                       +1.05488459r^3+.801025r^4.
\end{split}
\tag{11}
\]

At \(r=.75+w\), \(|w|\le.25\), its quadratic coefficient
after absorbing higher terms exceeds \(1.4764\). Its completed
square exceeds \(.1459\). Thus (10) holds uniformly, and
the pure U derivative exceeds
\(1.012-.5(1.864)=.08\). The positive D term has the stronger
derivative bound \(1.012-.4>0\).

For pure V terms the least is \(V_H\), by Section 6 of the
negative-DE concentration note. This comparison uses only
\(0\le\theta-s\le L\) and the unchanged pair ranges.
The function \(g(s)+V_H(\theta-s)\) is concave in s, so its
minimum is at zero or \(\min(\theta,v)\).

The H and B same-block terms dominate their corresponding pure
terms by the general comparisons (24) of that note, since their
larger-to-smaller ratios are below 1.5. The remaining G
same-block term has derivative

\[
             g'(s)+l\sin(h-s)-RN'_{k,l}(s-\theta).
\tag{12}
\]

Let \(D_0=RN'(0)\) and \(C_0=-RN''(0)\). From \(k/l<.68\),
positive squaring gives

\[
                  D_0/l<1.113,\qquad C_0/l<.518.
\tag{13}
\]

The established monotonicity of \(-RN''\) gives
\(RN'(s-\theta)\le D_0+C_0\theta\). Since
\(h-s\ge.6\) and \(\sin(.6)>.564\), (12) is larger than

\[
        1.012-(1.113+.518/6-.564)(1.352)>.153.
\tag{14}
\]

Hence this term reduces to \(s=0\).

In every separated term, negative B can be replaced by negative
H: concavity and the endpoint bound for V give
\(V_B(t)\ge(.87/h)lt>1.195t\ge V_H(t)\).
For the remaining H and G negative allocations, Section 7.1 of
the negative-DE concentration note proves the universal bound

\[
 V'_{k,q}(d)
 <1.20039875-.41011d-\frac{d^2}{6}+\frac{d^3}{6}
      \quad(.36\le d\le h),
\tag{15}
\]

for \(k\le.757\) and \(1\le q\le1.352\). The right side
decreases and equals \(.93033275<.931\) at \(d=.6\).
Thus the separated stress derivative is greater than
\(1.012-.931=.081\), and again its minimum is at \(s=0\).

At \(s=0\), all required low endpoint functions are exactly
the four already certified functions (12) of the negative-DE
endpoint theorem. The only new low obligations are therefore

\[
 \begin{cases}
 B_0+g(\theta)>0,&0\le\theta\le v,\\
 B_0+g(v)+V_H(\theta-v)>0,&v\le\theta\le L.
 \end{cases}
\tag{16}
\]

The low split-concavity proof applies to (16), with the fixed
negative argument \(\theta-v\) in place of \(\theta\).
Its norm curvature and the bound \(H'(m)>-.48\) are unchanged.
Thus it suffices to check the two A/T split endpoints.

## 4. High total angle

For \(L\le\theta\le h\), one always has \(s<\theta\).
The unchanged coefficient family satisfies

\[
       p_i/q_i>2/3,\qquad q_{\max}/q_{\min}<29/25.
\tag{17}
\]

Put \(\delta=\theta-s\). The same-block comparisons give
\(\Psi_i(P,N)\ge V_i(\delta)\). For a separated term,
the uniform bounds \(U_i(P)\ge-.545q_iP\) and
\(V'_j(t)>(2/3)q_j\) give an excess over the pure V term of
at least

\[
       \{\tfrac23q_{\min}-.545q_{\max}\}P
                                  >.0344q_{\min}P\ge0.
\tag{18}
\]

The positive D alternative is included since \(q_{\max}\ge1\)
and \(c_0-1/2<.4\).
Every stress therefore reduces to
\(B_0+g(s)+V_i(\theta-s)\). This is concave in s, so only
\(s=0\) and \(s=v\) remain. The former are the three already
certified functions (15) at \(s=0\).

For \(s=v\), split concavity is valid uniformly for every
\(\delta\in[0,h]\): the B-dependent functions are
\(\tfrac32m-R\sqrt{l^2+m^2}\) and

\[
 \tfrac32m+\max(l,m)(\cos\delta-1)
                    -R\sqrt{l^2+m^2-2lm\sin\delta}.
\tag{19}
\]

They are concave and increasing for \(m/l\le23/20\).
The remaining curvature is the same strict bound from Section 6
of the two-positive split theorem, using \(.9<c/l<1.1\).
Consequently the new high obligations are exactly

\[
             B_0+g(v)+V_i(\theta-v)>0
                    \quad(i=H,G,B)
\tag{20}
\]

at both A/T split endpoints. Full D support may be used as a
lower stress bound, as in the earlier endpoint theorem.

## 5. Exact polynomial certificates for the ten new endpoints

Use the explicit coefficient families and all polynomial
conventions of Sections 3 and 6--9 of the negative-DE endpoint
theorem. In particular, \(\mathcal N\) is its rational norm
numerator (40), \(\mathcal C_I\) is its Chebyshev coefficient
lower aggregate, and \(\mathcal Q_I\) is its quadratic
completion. The elementary Taylor conventions are
\(S_-=S_{11}\), \(S_+=S_9\), \(C_-=C_{10}\), \(C_+=C_{12}\).

Write \(\delta=\theta-v\), and denote their shifted versions
by \(S_{\delta,-}=S_{11}(\delta)\),
\(C_{\delta,-}=C_{10}(\delta)\), and so forth. Put

\[
                 g_*=KS_{11}(v)+.656C_{10}(v)-.656<g(v).
\tag{21}
\]

For each low A/T endpoint, use exactly B, \(P_H,P_G,P_B\)
and \(r_H,r_G,r_B\) from (46)--(50) of that theorem.
On \([0,v]\), define

\[
 N_{LZ}=\mathcal N\left(
 B+KS_-+.656(C_--1);\ (r_H,r_G,r_B);\ (P_H,P_G,P_B)\right).
\tag{22}
\]

On \([v,L]\), define

\[
\begin{gathered}
 r_{H,\delta}=.89C_2(\delta)+.456\{k-S_3(\delta)\},\\
 P_{H,\delta}=P_H-2kS_{\delta,-},\\
 N_{LH}=\mathcal N\left(
 B+g_*+C_{\delta,-}-1;\
 (r_{H,\delta},r_G,r_B);\ (P_{H,\delta},P_G,P_B)\right).
\end{gathered}
\tag{23}
\]

For each high A/T endpoint, use exactly B, \(m_-,\mu\),
the unrotated norm polynomials and auxiliaries, and \(q_*\)
from (58)--(63) of that theorem. Define

\[
\begin{split}
 P_{H,\delta}&=P_H-2kS_{\delta,-},\\
 P_{G,\delta}&=P_G-2klS_{\delta,-},\\
 P_{B,\delta}&=P_B-2lm_-S_{\delta,-},\\
 r_{H,\delta}&=.93C_4(\delta)+.3676\{k-S_5(\delta)\},\\
 r_{G,\delta}&=.93lC_4(\delta)+.3676\{k-lS_5(\delta)\},\\
 r_{B,\delta}&=.83lC_4(\delta)+.56\{\mu-lS_5(\delta)\}.
\end{split}
\tag{24}
\]

The three numerators are

\[
\begin{split}
 N_{HH}&=\mathcal N\left(B+g_*+C_{\delta,-}-1;\
 (r_G,r_B,r_{H,\delta},r_D);\ (P_G,P_B,P_{H,\delta},P_D)\right),\\
 N_{HG}&=\mathcal N\left(B+g_*+l(C_{\delta,-}-1);\
 (r_H,r_B,r_{G,\delta},r_D);\ (P_H,P_B,P_{G,\delta},P_D)\right),\\
 N_{HB}&=\mathcal N\left(B+g_*+q_*(C_{\delta,-}-1);\
 (r_H,r_G,r_{B,\delta},r_D);\ (P_H,P_G,P_{B,\delta},P_D)\right).
\end{split}
\tag{25}
\]

All auxiliaries have the corresponding whole-interval lower
aggregate greater than .6. Every squared-norm polynomial is an
upper bound: positive terms use upper Taylor approximations,
while subtracted positive products use lower ones.
The B cosine coefficient remains a lower-bound replacement
because \(q_*\ge\max(l,m)\) and \(\cos\delta-1\le0\).

The following exact rational coefficient comparisons complete
the proof. They are single whole-interval aggregates, without
evaluation nodes.

| Split endpoint | Numerator | Interval | Degree | Positive aggregate |
|---|---|---|---:|---:|
| A | \(N_{LZ}\) | \([0,v]\) | 18 | \(\mathcal C>.08991\) |
| T | \(N_{LZ}\) | \([0,v]\) | 32 | \(\mathcal Q>.0183947\) |
| A | \(N_{LH}\) | \([v,L]\) | 19 | \(\mathcal C>.0094417\) |
| T | \(N_{LH}\) | \([v,L]\) | 33 | \(\mathcal Q>.0027740\) |
| A | \(N_{HH}\) | \([L,h]\) | 28 | \(\mathcal C>.0007429\) |
| A | \(N_{HG}\) | \([L,h]\) | 31 | \(\mathcal C>.0045860\) |
| A | \(N_{HB}\) | \([L,h]\) | 32 | \(\mathcal C>.0923872\) |
| T | \(N_{HH}\) | \([L,h]\) | 42 | \(\mathcal C>.0008161\) |
| T | \(N_{HG}\) | \([L,h]\) | 45 | \(\mathcal C>.0049256\) |
| T | \(N_{HB}\) | \([L,h]\) | 41 | \(\mathcal C>.0344132\) |

Every denominator of \(\mathcal N\) is positive. These bounds
prove (16) and (20). Together with the already certified
\(s=0\) endpoints, they contradict the necessary nonpositive
weighted stress and establish the claim in Section 1.
