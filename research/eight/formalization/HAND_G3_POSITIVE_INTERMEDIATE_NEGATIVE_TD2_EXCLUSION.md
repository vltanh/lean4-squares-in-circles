# A positive intermediate error and a nonpositive original TD2 error

## 1. Original scope

Retain the original G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]
The original sorted outer states H, G, B and D have signed
tangents respectively positive, negative, negative and negative.
A, T and E may have either sign and either radial kind.
Consider either original-owner pattern

* GA2, AB2, BT2, TD2, DE2, EH0, with \(a=d_{AB}\ge0\);
* GA3, AB0, BT2, TD2, DE2, EH0, with \(a=d_{GA}\ge0\).

In both cases \(HG\in\{0,2\}\), and write
\[
                         d_{TD}=-s,\qquad s\ge0.
\tag{2}
\]
There is no such original cycle. No frame order is assumed.

The total-variation inequality gives \(0\le a,s<h\).
Use the support notation \(S,\overline S,W,j\) from
[the positive-intermediate TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md):
\[
 \begin{gathered}
 c_0=\sqrt{Q/2}-\tfrac12,\qquad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\\
 W(t)=\tfrac12(1+\cos t+|\sin t|),\\
 j(a)=W(a)-1-S(\sin a,1-\cos a).
 \end{gathered}
\tag{3}
\]
Every decimal in this note is an exact rational.

## 2. A secant weight cancels T's signed tangent

Use weights \(k,l,l,c,c\sec s,1,1\) in cyclic order.
In particular BT keeps weight c, while the actual TD2
inequality has weight \(c\sec s>0\).

Write D's tangent as \(-b_D\), and keep T's tangent \(y_T\)
signed. The original TD2 projection and the algebraic
zero-error TD0 projection are
\[
 P_{TD2}=-a_T\sin s+y_T\cos s+b_D,\qquad
 P_{TD0}^{\rm virt}=y_T+b_D.
\tag{4}
\]
Their weighted difference is
\[
 c\sec s\,P_{TD2}-cP_{TD0}^{\rm virt}
          =-ca_T\tan s+c(\sec s-1)b_D.
\tag{5}
\]
The signed tangent cancels exactly. After including the
demand difference \(c\sec s\,W(s)-c\), the gain in
demand minus projection is
\[
 c\left\{(a_T+\tfrac12)\tan s
                 +(\tfrac12-b_D)(\sec s-1)\right\}.
\tag{6}
\]

The unconditional entry bounds are \(a_T>447/800\) and
\(b_D\le c_0<.9\). The first follows from the true-core
boundary and sorting, as explained in Section 2 of
HAND_G3_FOUR_CUTS_AT_ONE_THIRTY_SECOND.md; it does not
require that note's later mismatch hypothesis.
Also
\[
                         \tan(s/2)<\frac{183}{500}
                    \qquad(0<s\le h).
\tag{7}
\]
Indeed monotonicity reduces (7) to \(s=h\), where the
alternating Taylor comparison is
\[
 \frac{183}{500}C_6(7/20)-S_5(7/20)
                  =\frac{7007815411}{7680000000000}>0.
\tag{8}
\]
Use \(\sec s-1=\tan s\,\tan(s/2)\) and \(\tan s\ge s\).
The gain in (6) is at least
\[
 c\left\{\frac{847}{800}-\frac25\frac{183}{500}\right\}s
       =\frac{18247}{20000}cs\ge\frac9{10}cs.
\tag{9}
\]
The gain is zero at \(s=0\), where the same inequality holds.

For the A error, the unchanged comparison in Section 2 of
the positive-intermediate TD0 theorem contributes \(lj(a)\)
and algebraically removes that rotation from G or B.
After both algebraic removals, the remaining angular vector
has
\[
 \sum d_i^{\rm virt}=s-a,\qquad
 \sum(d_i^{\rm virt})_+\le h-a,\qquad
 \sum(-d_i^{\rm virt})_+\le h-s.
\tag{10}
\]
All reference forces are those of the secondary-owner
four-circle expression, with its TD argument zero.
These are identities and support relaxations inside one
weighted sum of the actual inequalities. No virtual
projection is claimed to be an original witness.

## 3. The range \(0\le a\le1/6\)

Take the fixed weights and charge from Section 3 of the
positive-intermediate TD0 theorem:
\[
 k=\frac{39}{50},\quad l=\frac{63}{50},\quad
 c=\frac95,\quad \lambda=\frac{103}{100}.
\tag{11}
\]
Its individual charged circle bounds do not require the
angular sum to vanish. They give a zero baseline
\(B_0>13/400\), and make the virtual four-circle stress
plus \(\lambda\sum d_i^{\rm virt}\) at least \(B_0\).
Therefore the actual stress is greater than
\[
 \frac{13}{400}+\lambda a+lj(a)
                     +\left(\frac9{10}c-\lambda\right)s.
\tag{12}
\]
The last coefficient is \(59/100>0\). The exact low
A support and the calculation already proved there give
\[
 \frac{13}{400}+\lambda a+lj(a)
                         >\frac{49}{15000}>0.
\tag{13}
\]
This excludes the complete low-a range, with no additional
restriction on s.

## 4. Fixed high-angle weights and two variation endpoints

For \(1/6\le a<h\), use the single fixed triple
\[
                    k=\frac34,\qquad l=\frac{19}{20},
                    \qquad c=\frac{27}{20}.
\tag{14}
\]
Use the full-circle bounds for H, G and B and retain the
actual diagonal D support at zero. The baseline is
\[
\begin{split}
 B_0={}&k+2l+2c+2
       -\overline S(1,k)-\overline S(l,k)
       -\overline S(c,l)-(1+c)c_0\\
 &>-.024.
\end{split}
\tag{15}
\]

There are three ordinary coefficient pairs
\[
                       (k,l),\qquad(k,1),\qquad(l,c).
\tag{16}
\]
For each, let \(N_i,U_i,V_i\) be the norm and the positive
and negative increments defined in the TD2 concentration
lemma. All three ratios \(p_i/q_i\) exceed \(2/3\).
The actual one-error D block has the valid lower bound
\[
                 U_D(P)+V_H(N),\qquad
                 U_D(P)=-(c_0-\tfrac12)P.
\tag{17}
\]
This is Section 4 of
HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md.
Its force is exactly the virtual D force
\((\cos d,c+\sin d)\) here; the use of (17) makes no
assumption about an original TD2 error.

The full-circle blocks are separately concave in their
normalized positive and negative arguments. As in that
lemma, negative variation first concentrates in one block
and positive variation then concentrates in one block.
For fixed \(a,s\), the remaining scalar parameter is the
positive variation P, with
\[
       \max(0,s-a)\le P\le h-a,\qquad N=P+a-s.
\tag{18}
\]
Its dependence is concave, so only the endpoints in (18)
remain.

For \(s\le a\), the first endpoint gives \(V_i(a-s)\).
For \(s\ge a\), it gives \(U_i(s-a)\), with \(U_D\)
also allowed. At the other endpoint, \(P=h-a\) and
\(N=h-s\). If the two signs occupy one ordinary block,
the increment is
\[
 p_i\{\cos(h-a)+\sin(h-a)-1\}
 +q_i\{\cos(h-s)-1\}
        -R\{N_i(s-a)-N_i(0)\}.
\tag{19}
\]
If they occupy different blocks, it is
\[
                        U_i(h-a)+V_j(h-s),
\tag{20}
\]
again allowing the linear \(U_D\) and identifying the
D negative increment with \(V_H\).

For fixed a, every one of these alternatives, after
adding the linear gain \(9cs/10\), is concave in s on
each of the intervals \([0,a]\) and \([a,h]\).
For (19) this is the negative-variable concavity with
its positive variable fixed; for (20) it is concavity
of \(V_j\). The first-endpoint alternatives use the
concavity of \(V_i,U_i\), or linearity of \(U_D\).
Consequently only
\[
                              s=0,\qquad s=a,\qquad s=h
\tag{21}
\]
must be checked. This is a whole-domain concentration,
not an assumption on the original errors.

## 5. The envelope at a nonnegative negative-variation excess

For the fixed pairs (16), the exact derivative bound
\[
                            V_i'(b)>\frac45,
                            \qquad 0\le b\le h
\tag{22}
\]
holds. Each \(V_i\) is concave, so it suffices to check
its right derivative at h:
\[
       V_i'(h)=-q_i\sin h+
                    \frac{Rp_iq_i\cos h}{N_i(-h)}.
\tag{23}
\]
Using \(\cos h>.7648,\sin h<.645,R>1.978787\), the
three bounds \(N_i(-h)<.7396,.7722,1.0357\), in the
order (16), give lower bounds respectively greater
than .8451, .8248 and 1.0032.

The universal scalar-envelope inequalities give
\[
 U_i(b)\ge-\frac{109}{200}q_i b,\qquad
 M_i(\theta)\ge V_i(\theta)
                 \quad(0\le\theta\le h).
\tag{24}
\]
They apply because \(p_i/q_i>2/3\).
Also \(U_D(b)\ge-.4b\).
For any nonnegative excess \(\theta=N-P\), the
separated alternatives are bounded below by
\[
\begin{split}
 \min_iV_i(\theta)+
       \left(\frac45-\frac{109}{200}\frac{27}{20}\right)b
   &=\min_iV_i(\theta)+\frac{257}{4000}b\\
   &\ge\min_iV_i(\theta).
\end{split}
\tag{25}
\]
The same-block alternatives are likewise at least
\(V_i(\theta)\), by (24) and concavity between zero
positive variation and its maximal possible value.

Thus at \(s=0\) the scalar envelope is bounded below by
\(\min_i V_i(a)\). At \(s=a\), it is nonnegative because
all \(V_i(0)=0\). At \(s=h\), there is no negative
variation, and the envelope is
\(\min\{U_G(h-a),U_H(h-a),U_B(h-a),U_D(h-a)\}\).
It remains to prove positivity of
\[
\begin{array}{ll}
 s=0:&B_0+lj(a)+V_i(a),\\
 s=a:&B_0+lj(a)+\dfrac9{10}ca,\\
 s=h:&B_0+lj(a)+\dfrac9{10}ch+U_i(h-a).
\end{array}
\tag{26}
\]

## 6. Whole-interval A support bounds

The exact A support formula is
\[
 j(a)=
 \begin{cases}
 (\cos a-1)/2+(\tfrac12-a_0)\sin a,&a\le\alpha_0,\\
 \sin a-2R\sin(a/2),&a\ge\alpha_0,
 \end{cases}
 \qquad
 \alpha_0=2\arctan\frac1{2\sqrt{Q-1/4}}.
\tag{27}
\]
Its values and first derivatives agree at the transition.
The earlier split-concavity lemma proves
\(\alpha_0>1/2\); also \(\alpha_0<103/200=.515\).
For the upper bound, use
\(\sqrt{Q-1/4}>1.9\) and
\[
 \tan(103/400)\ge\frac{103}{400}
                 +\frac13\left(\frac{103}{400}\right)^3
                         >\frac5{19}.
\tag{28}
\]

The following bounds hold on the complete interval
\([0,h]\), on each smooth branch:
\[
             j''<\frac1{50},\qquad
             -\frac{61}{50}<j'<-\frac{69}{100}.
\tag{29}
\]
On the first branch,
\[
 j''=-\tfrac12\cos a+(a_0-\tfrac12)\sin a
 \le-\tfrac12C_6(.515)+.915S_5(.515)<.02.
\tag{30}
\]
The expression preceding the Taylor bounds increases
with a. On the second branch \(j''<0\).
For the lower bound on \(j'\), the first branch has
\(|j'|\le\sqrt{1/4+.915^2}<1.05\); the second has
\(j'=\cos a-R\cos(a/2)>.7648-1.98>-1.22\).
For the upper bound, the first branch satisfies
\[
 j'\le-(a_0-\tfrac12)\cos a
             <-.9145(.7648)<-.69,
\]
and the second satisfies
\[
 j'\le1-1.97\{1-(.35)^2/2\}<-.69.
\]
The \(C^1\) join preserves every concavity conclusion
made from these branchwise bounds.

Let \(L=1/6\) and \(d=h-L=8/15\).
The universal norm derivative bounds of Section 3 of
the TD2 concentration lemma give
\[
 \begin{split}
 V_i''(a)&<-(.7648-.7)q_i=-.0648q_i,\\
 U_i''(b)&<-.1p_i\qquad(0\le b\le d).
 \end{split}
\tag{31}
\]
For the second assertion, that lemma bounds
\(-RN_i''(b)\) by \(.762p_i+.921p_i b\).
The concave function
\(\cos b+\sin b-.762-.921b\) is greater than .1:
at zero its value is .238, and at d this follows
from \(C_6(d)+S_7(d)-.762-.921d>.1\).

Consequently the three \(s=0\) scalars in (26) are
strictly concave in a:
\[
               (lj+V_i)''<\frac{l}{50}-.0648q_i
                                    \le-.04256.
\tag{32}
\]
Each ordinary \(s=h\) scalar is also strictly concave:
\[
           \frac{d^2}{da^2}\{lj(a)+U_i(h-a)\}
                         <\frac{l}{50}-.1p_i\le-.056.
\tag{33}
\]
The \(s=a\) scalar is strictly increasing, since
\[
                      lj'(a)+\frac9{10}c
                              >-1.22l+.9c=.056.
\tag{34}
\]
The \(s=h\) scalar involving \(U_D\) is strictly
decreasing, since its derivative is
\[
                        lj'(a)+c_0-\tfrac12
                                  <-.69l+.4=-.2555.
\tag{35}
\]

## 7. Exact endpoint reserves and the contradiction

All scalar comparisons from Section 6 therefore reduce
to \(a=L\) or \(a=h\). The A values satisfy
\[
                         j(L)>-.159,\qquad j(h)>-.713.
\tag{36}
\]
The first follows from the tangent-zero formula using
\(C_6(L),S_5(L)\). The second uses
\[
          S_7(h)-2(1.978788)S_5(h/2)>-.713
\]
in the interior formula.

Here are the remaining explicit norm bounds, in the
order G, H, B of (16):
\[
\begin{array}{c|ccc}
 &G&H&B\\ \hline
 N_i(0)\ge&1.2103&1.25&1.6507\\
 N_i(0)\le&1.2104&1.25&1.6508\\
 N_i(-L)<&1.1085&1.1462&1.5165\\
 N_i(-h)<&.7396&.7722&1.0357\\
 N_i(d)<&1.4797&1.5249&2.0073
\end{array}
\tag{37}
\]
The H zero value is exactly \(5/4\); all other
zero inequalities are strict. Positive squaring with
\(S_7\) for a negative argument and \(S_9\) for a
positive argument proves every bound.
Together with \(R<1.978788\) and \(c_0<.899215\),
the zero bounds give \(B_0>-.0233484756>-.024\).

For all three ordinary pairs, (36)--(37) and the
alternating cosine bounds give
\[
             B_0+lj(L)+V_i(L)>.006,\qquad
             B_0+lj(h)+V_i(h)>.006.
\tag{38}
\]
For the tightest of these six comparisons, the explicit
G right-endpoint lower bound is
\[
 -.024-\frac{19}{20}(.713)
 +\frac{19}{20}\{C_6(h)-1\}
 +1.978787(1.2103-.7396)>.0066>.006.
\tag{39}
\]

For every ordinary \(s=h\) scalar, the left endpoint
is greater than .32:
\[
 B_0+lj(L)+\frac9{10}ch+U_i(d)>.32.
\tag{40}
\]
The same bounds give this directly by substituting
\(C_6(d)+S_7(d)\), the last row of (37), and
the zero lower bounds.
At the right endpoint all positive increments vanish,
and the common lower bound is
\[
 -.024-l(.713)+\frac9{10}ch
                  =\frac{2983}{20000}>.149.
\tag{41}
\]
By (35), (41) also bounds the D positive alternative
throughout the interval.

Finally the increasing \(s=a\) scalar has left-endpoint
lower bound
\[
 -.024-l(.159)+\frac9{10}cL
                  =\frac{549}{20000}>.027.
\tag{42}
\]

Equations (32)--(42) prove positivity of every expression
in (26) on the whole high-a interval. Concavity in s
from Section 4 extends this to every \(0\le s\le h\).
This contradicts the nonpositive stress required by
the actual weighted separating inequalities.

Together with (13), the proof excludes both patterns in
Section 1 for all nonnegative A intermediate errors
and all nonpositive original TD2 errors. Combining it
with the positive-TD2 endpoint theorem and the arbitrary-TD0
theorem covers either TD owner for each of these two
positive-intermediate patterns. Every comparison retains
the original outer-circle data and actual signed T
coordinate; no sign, radial-kind or frame-order
assumption on A, T or E has been added.
