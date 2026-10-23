# Two nonnegative primary totals and a nonpositive TD2 error

## 1. Scope and the remaining TD sign

Retain the original scope and the selected A/E-primary totals a,e
of
[the nonnegative-total theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).
Thus the four sorted outer states H,G,B,D have signed tangents
respectively positive, negative, negative and negative; E is
nonpositive and may have either radial kind; A and T have either
sign and either radial kind. Retain BT2, either HG0 or HG2, and
the actual GA2/GA3, AB0/AB2, DE2/DE3, EH0/EH1 alternatives.
The selected primary totals a,e are nonnegative, including a
signed sum of two primary errors when both alternatives are
present at one intermediate state.

Now retain TD2 of error −s, where s≥0. As usual put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 h=\frac7{10},\quad L=\frac16,\quad d=h-L=\frac8{15},
\]
\[
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,\qquad d_0=c_0-\frac12<.4.
\tag{1}
\]
The original angular vector satisfies
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{2}
\]

**Theorem.** There is no such original cycle.

Together with the cited companion, this excludes every TD0/TD2
owner and error when the selected A and E totals are nonnegative.
BT2 is still retained. Neither negative A total nor negative E
total is an assertion here.

## 2. Exact secant gain and the small-total range

Use the same support charge
\[
 j(t)=W(t)-1-S(\sin t,1-\cos t),\qquad
 W(t)=\frac{1+\cos t+|\sin t|}{2}
\tag{3}
\]
as in the companion. Equal A multipliers l and equal E multipliers
one give the exact lower charge lj(a)+j(e), including the signed
two-primary cases. Set
\[
                             \delta=a+e\le h.
\tag{4}
\]

Give BT2 weight c and TD2 weight c sec s. The signed T tangent
cancels exactly in their difference from the virtual zero-angle
TD0 expression. The pointwise demand-minus-projection gain is
\[
 c\{(a_T+\tfrac12)\tan s+(\tfrac12-b_D)(\sec s-1)\}
                             \ge\gamma cs,
 \qquad \gamma=\frac{18247}{20000}.
\tag{5}
\]
This is Section 2 of
[the positive-A negative-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md).
It uses only the unconditional original bounds
\(a_T>447/800\), \(b_D<.9\), and
\(\tan(s/2)<183/500\) for s≤h. T's sign is unrestricted.

After the A/E comparisons and this TD deletion, the ordinary
angular vector has signed sum s−δ and variations
\[
                  P\le h-\delta,\qquad N\le h-s,
                                      \qquad N-P=\delta-s.
\tag{6}
\]
Deleting a signed primary pair removes positive variation at
least its nonnegative total; deleting its negative variation
only enlarges (6). Missing arguments may be inserted as virtual
zeros in the reference norm blocks.

For δ≤L choose the fixed small-A family
\[
             (k,l,c)=(.78,1.26,1.8),\qquad\lambda=1.03.
\]
The companion proves j(a)+j(e)≥j(δ), so l≥1 and j(e)≤0 give
\[
                              lj(a)+j(e)\ge lj(\delta).
\tag{7}
\]
The existing charged ordinary-circle proof at this family applies
to the signed sum s−δ. Its lower bound is therefore greater than
\[
              \frac{13}{400}+\lambda\delta+lj(\delta)
                              +(.9c-\lambda)s
                         >\frac{49}{15000}>0,
\tag{8}
\]
because .9c−λ=.59. This closes the whole small-total range.

## 3. A family depending only on the E total

For L≤δ≤h use
\[
                    k=.75+.14e,\qquad
                    l=.95+.45e,\qquad c=1.35.
\tag{9}
\]
These weights are fixed while s and the ordinary variation are
concentrated. The actual seven multipliers are
\[
                           (k,l,l,c,c\sec s,1,1).
\tag{10}
\]
Since 0≤e≤δ≤h,
\[
 .75\le k\le.848<.85,\qquad .95\le l\le1.265<c,
\]
\[
 l-k=.20+.31e>0,
       \qquad\tfrac32k-l=.175-.24e\ge.007>0.
\tag{11}
\]
The three ordinary pairs
\[
                   H=(k,1),\quad G=(k,l),\quad B=(l,c)
\tag{12}
\]
are ordered, and every smaller-to-larger ratio exceeds 2/3.
In particular the largest q-coefficient is c=1.35.

With \(\overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2\), the
reference zero-angle baseline is
\[
 B(e)=k+2l+2c+2
       -\overline S(1,k)-\overline S(k,l)-\overline S(l,c)
                                      -(1+c)c_0.
\tag{13}
\]
The exact sorted D support is diagonal at zero because c>1.
Its remaining one-angle force is (cos v,c+sin v), or the same
force with v inserted as a virtual zero if DE was primary.
The established D minorant is
\[
                        U_D(P)+V_H(N),\qquad U_D(P)=-d_0P.
\tag{14}
\]
Its hypotheses k≤.85 and k≤c≤2 hold by (11). Thus this use
retains the exact zero-angle D support in (13).

For the pairs (12), define
\[
\begin{split}
 N_i(t)&=\sqrt{p_i^2+q_i^2+2p_iq_i\sin t},\\
 U_i(t)&=p_i(\cos t+\sin t-1)-R\{N_i(t)-N_i(0)\},\\
 V_i(t)&=q_i(\cos t-1)-R\{N_i(-t)-N_i(0)\}.
\end{split}
\tag{15}
\]
The universal concentration lemma gives separate concavity of
each ordinary two-angle block, concavity of U_i and V_i, and
\[
                         U_i(t)\ge-.545q_it.
\tag{16}
\]

We also have, uniformly in e and t,
\[
                               V_i'(t)>.8.
\tag{17}
\]
Concavity reduces this to t=h. At fixed q its endpoint derivative
is strictly increasing in p, because
\[
 \partial_p V_{p,q}'(h)
          =\frac{Rq^2\cos h(q-p\sin h)}{N(-h)^3}>0.
\tag{18}
\]
For H and B it therefore suffices to take e=0. Using
\(R>1.978787\), \(\cos h>.7648\), \(\sin h<.645\), and
the norm upper bounds .7722 and 1.0357 gives respectively
\[
                     V_H'(h)>.824,
                                  \qquad V_B'(h)>1.
\tag{19}
\]

For the G pair put C=C_6(h), S_-=S_11(h), S_+=S_9(h).
Positive squaring reduces (17) to positivity of the quartic
\[
 P(e)=Qk^2l^2C^2-(.8+lS_+)^2\{k^2+l^2-2klS_-\}.
\tag{20}
\]
If \(P=\sum_{j=0}^4p_je^j\), its exact rational coefficients
satisfy
\[
 p_0>.0722,\quad p_1>.173,\quad p_2>.0101,
                   \quad p_3>-.0182,\quad p_4>-.0028.
\tag{21}
\]
Consequently
\[
                   P(e)>.0722-.0182h^3-.0028h^4>.065>0.
\]
All fractions in (20) are positive before squaring. This proves
(17) for every pair on the entire domain.

## 4. Concentrating the negative TD magnitude

Fix δ,e and hence the weights. The separate concavity argument
first puts all negative ordinary variation into one block,
then all positive variation into one block. The remaining
positive mass satisfies
\[
                       \max(0,s-\delta)\le P\le h-\delta,
                                      \qquad N=P+\delta-s.
\tag{22}
\]
Its dependence is concave, so only the two endpoints remain.
For s≤δ the first gives V_i(δ−s); for s≥δ it gives
U_i(s−δ), also permitting U_D. At the other endpoint the two
masses are P=h−δ and N=h−s, either in one ordinary block or
in different blocks. These are precisely the same-block and
separated formulas in Sections 4--5 of the cited negative-TD2
theorem, with δ replacing its A angle.

Adding the linear gain γcs preserves concavity in s separately
on [0,δ] and [δ,h]. The primary cost lj(a)+j(e) is constant
in this step. Hence only the intrinsic endpoints
\[
                                s=0,\quad s=\delta,\quad s=h
\tag{23}
\]
remain.

At s=0 or s=δ the ordinary negative excess is nonnegative.
Every same-block alternative dominates its pure V alternative
because p_i/q_i>2/3. For the separated alternatives, (16)--(17)
give the positive reserve
\[
                    .8-.545c=\frac{257}{4000}>0.
\tag{24}
\]
This also pays U_D, since d_0<.4<.545c. Thus at s=0 only
min_i V_i(δ) remains, and at s=δ the ordinary envelope is
nonnegative. At s=h no negative ordinary variation remains,
and only U_i(h−δ) or U_D(h−δ) remains.

It is therefore enough to prove the following eight functions
strictly positive on L≤δ≤h, 0≤e≤δ, with a=δ−e:
\[
\begin{array}{ll}
 F_{Vi}=B(e)+lj(a)+j(e)+V_i(\delta),&i=H,G,B,\\[2pt]
 F_=B(e)+lj(a)+j(e)+\gamma c\delta,&\\[2pt]
 F_{Ui}=B(e)+lj(a)+j(e)+\gamma ch+U_i(h-\delta),&i=H,G,B,\\[2pt]
 F_D=B(e)+lj(a)+j(e)+\gamma ch-d_0(h-\delta).&
\end{array}
\tag{25}
\]

For the three F_V functions there is an additional exact
one-variable concavity. At fixed e, both weights are fixed,
and the universal whole-interval derivative bounds give
\[
                         j''<.02,\qquad V_i''<-.0648q_i.
\]
They are proved in Section 6 of the negative-TD2 theorem and
hold across the C^1 support transition. Thus
\[
              \partial_\delta^2 F_{Vi}
                    <.02(1.265)-.0648(.95)=-.03626<0.
\tag{26}
\]
At fixed e the permitted δ interval is [max(L,e),h]. Its
two endpoints therefore leave exactly the three boundary curves
\[
 \delta=L, 0\le e\le L;\qquad
 \delta=h, 0\le e\le h;\qquad
 \delta=e, L\le e\le h.
\tag{27}
\]
The other five functions in (25) will be bounded directly on
the whole continuous domain.

## 5. Exact polynomial lower bounds

Use the exact rational upper bounds
\[
 \overline R=1.978787508,
 \quad\overline a=1.414575672,
 \quad\overline c=.899214066.
\tag{28}
\]
Positive squaring proves
\(\overline R^2>Q\),
\((\overline a+1/2)^2>Q-1/4\), and
\((\overline c+1/2)^2>Q/2\).
The support envelope
\[
 J(u)=\frac{C_{10}(u)-1}{2}
        +(\frac12-\overline a)S_9(u)-.029u^4
                                  \le j(u),\quad0\le u\le h
\tag{29}
\]
is proved in Section 5 of the companion. In particular its
quartic reserve is
\(.029-\overline R(h-1/2)^2/(8h^3)>0\).

Put t=δ−L and a=L+t−e. The polynomial domain is the full
trapezoid
\[
                           0\le t\le d,\qquad0\le e\le L+t.
\tag{30}
\]
The common polynomial nonradical part is
\[
 A_0=2k+3l+\tfrac52c+\tfrac52-(1+c)\overline c
                                      +lJ(a)+J(e).
\tag{31}
\]
Start with
\[
                 P_H=1+k^2,\quad P_G=k^2+l^2,
                                      \quad P_B=l^2+c^2.
\tag{32}
\]
The following rules specify the eight polynomial families.

* For V_i add \(q_i(C_{10}(\delta)-1)\) to A_0 and replace
  just P_i by \(P_i-2p_iq_iS_{11}(\delta)\).
* For the equality endpoint add \(\gamma c\delta\) to A_0,
  leaving all P unchanged.
* For U_i put b=h−δ, add
  \(\gamma ch+p_i\{C_{10}(b)+S_{11}(b)-1\}\) to A_0,
  and replace P_i by \(P_i+2p_iq_iS_9(b)\).
* For the D endpoint add
  \(\gamma ch-(\overline c-1/2)(h-\delta)\) to A_0,
  leaving all P unchanged.

The charge changes are lower bounds; the three P polynomials
are upper bounds for their actual squared norms. In particular
S_11 is used for the subtracted sine and S_9 for the added sine.

For every P let P_0=P(0,0), define
\[
 w=\frac{[P]_{\le3}-P_0}{P_0},\qquad
 r=\rho\left[1+\frac w2-\frac{w^2}{8}+\frac{w^3}{16}\right]_{\le3},
\tag{33}
\]
where truncation is by total degree in (t,e). The three default
ρ constants, in H,G,B order, are
\[
                       1.25,\quad1.210371844,\quad1.650757402.
\tag{34}
\]
At the one replaced V norm use respectively
\[
                       1.146148246,\quad1.108421405,\quad1.516402460;
\]
at the one replaced U norm use respectively
\[
                       1.524831081,\quad1.479688932,\quad2.007252551.
\tag{35}
\]
These are fixed rational masses, not approximate-root premises.
Their whole-domain coefficient lower bounds give r>.72 in every
case. The elementary inequality
\(\sqrt P\le(P+r^2)/(2r)\) consequently applies.

For the appropriate nonradical polynomial A define
\[
 {\cal N}=2A r_Hr_Gr_B
            -\overline R\sum_{i=H,G,B}(P_i+r_i^2)
                                             \prod_{j\ne i}r_j.
\tag{36}
\]
Each function in (25) is at least
\({\cal N}/(2r_Hr_Gr_B)\). All numerator degrees are twenty,
except the three U numerators, whose degrees are twenty-one.

## 6. Whole-domain and boundary certificates

For clarity, every coefficient bound used here has an explicit
rational formula. Define
\[
 A_{n0}=4^{-n}\binom{2n}{n},\qquad
 A_{nj}=2\,4^{-n}\binom{2n}{n-j}\quad(1\le j\le n),
\tag{37}
\]
zero otherwise. Then \(u^n=\sum_jA_{nj}T_j(2u-1)\), where
\(|T_j|\le1\) on [−1,1]. For a polynomial
\(P(t,e)=\sum p_{ij}t^ie^j\), substitute
\[
                          t=du,\qquad e=(L+du)v,
                              \quad0\le u,v\le1.
\tag{38}
\]
This covers (30), and its tensor coefficients are exactly
\[
 b_{kl}=\sum_{ij}p_{ij}
       \sum_{r=0}^j\binom jr L^{j-r}d^{i+r}A_{i+r,k}A_{jl}.
\tag{39}
\]
Thus
\[
                            P\ge b_{00}
                                  -\sum_{(k,l)\ne(0,0)}|b_{kl}|.
\tag{40}
\]
For a one-variable polynomial \(P(x)=\sum p_ix^i\) on [0,D],
use \(b_j=\sum_i p_iD^iA_{ij}\) and the corresponding lower
bound \(b_0-\sum_{j\ge1}|b_j|\).

Equations (28)--(40) give the following whole-trapezoid numerator
lower bounds directly:

| Function | Whole-domain numerator lower bound |
| --- | ---: |
| equality endpoint | .028 |
| U_H | .525 |
| U_G | .625 |
| U_B | .587 |
| D | .553 |

For each V_i restrict its numerator to the three intrinsic curves
(27). In the first use e as variable on [0,L]; in the second use
e on [0,h]; in the third substitute e=L+t and use t on [0,d].
The exact lower coefficient bounds are

| Index | δ=L | δ=e | δ=h |
| --- | ---: | ---: | ---: |
| H | .0808 | .1218 | .0234 |
| G | .0667 | .1230 | .0179 |
| B | .3357 | .4414 | .510 |

All entries except the H and G entries at δ=h follow directly
from the one-variable coefficient formula above. For those two,
write the restricted polynomial as
\[
                     P(.35+v)=\sum_j a_jv^j,
\]
and put
\[
                       q=a_2-\sum_{j\ge3}|a_j|(.35)^{j-2}.
\tag{41}
\]
In both cases q>0, and
\[
                   P\ge a_0+a_1v+qv^2
                          \ge a_0-\frac{a_1^2}{4q}.
\tag{42}
\]
The two exact completed-square lower bounds exceed .0234 and
.0179 respectively. This proves every entry of the table on its
whole interval.

These formulas also reproduce the mass lower bounds following
(35) and the quartic coefficient inequalities (21). Every number
in the tables is a rational outward bound for an explicitly
defined finite coefficient sum. No angle sample, subdivision,
or Bernstein basis is used.

## 7. Conclusion in the stated owner class

The five whole-domain bounds prove the corresponding five
functions in (25) positive everywhere. The nine boundary bounds,
together with the exact concavity (26), prove all three F_V
functions positive as well. The concentration (22)--(24) then
contradicts the necessary weighted inequality for every original
s in [0,h]. Equation (8) already covered δ≤L.

The E state has been used only in its single support charge j(e).
All secant and circle comparisons are pointwise in the original
states. The proof changes no center or original witness and
assumes no additional frame order. It uses no numerical acceptance
premise, state mesh, Lean compilation, or CI.
