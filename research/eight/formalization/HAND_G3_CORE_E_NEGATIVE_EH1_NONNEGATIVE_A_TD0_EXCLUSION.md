# A genuine negative EH1 with nonnegative A total and arbitrary TD0

## 1. Scope and conclusion

Use the fixed-original-witness G0--G2 necessary system at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 h=\frac7{10},\quad L=\frac16,\quad v=\frac1{10},\quad u=\frac14.
\tag{1}
\]
The sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},\quad
 BT=2,\quad TD=0,\quad DE=2,\quad EH=1.
\tag{2}
\]
The original TD0 error is arbitrary. EH1 has error \(-s\), and
the genuine negative-EH entry conditions are
\[
             0\le s\le u,\qquad a_E=\frac7{12},\qquad
                              0\le b_E\le\frac{39}{250}.
\tag{3}
\]
At A permit no primary, a single nonnegative primary, or both
GA3 and AB2 with nonnegative signed total a. Secondary A
arguments remain arbitrary. A and T may have either sign and
either radial kind. Assume the actual adjacent inequalities and
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{4}
\]

There is no such necessary system. The range \(0\le a\le L\)
is already excluded, including all E-owner alternatives, by
[the fixed secant-H theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md).
This note proves the remaining range \(L\le a\le h\).
There is no frame-order hypothesis.

The proof uses the continuous weights and positive scalar
certificates of the two negative-EH/TD2 notes. It does not infer
an original TD2 witness. The new original TD0 argument is kept
in a fourth ordinary D-circle block, whose extra allocations
are removed explicitly below.

## 2. The fourth circle block

Use the notation \(j,U,V,\Psi,\overline S\) of
[the remaining-error EH theorem](HAND_G3_CORE_E_NEGATIVE_EH1_REMAINING_ERROR_EXCLUSION.md).
Set its total parameter equal to a and its TD2 parameter
algebraically to zero, so \(m=c\).
Give the original edges weights
\[
                         (k,l,l,c,c,1,p),
\tag{5}
\]
where \(p=1\) for \(s\le v\) and \(p=201/200\) for \(s\ge v\).
These multipliers are positive.

The equal BT and TD multipliers cancel T's signed tangent
for the actual TD0 owner, with no condition on its radial kind.
Writing \(t=d_{TD}\) and \(d=d_{DE}\), the D force is
\[
                    F_D=(\cos d+c\sin t,\ \sin d+c\cos t).
\tag{6}
\]
Its squared norm is \(1+c^2+2c\sin(t+d)\).
Thus D supplies an ordinary two-angle full-circle block with
pair
\[
 (p_D,q_D)=(\min(c,1),\max(c,1)).
\tag{7}
\]
The other pairs are
\[
       H=(k,1),\qquad G=(k,l),\qquad
                         B=(\min(l,c),\max(l,c)).
\tag{8}
\]
The angular coefficients before normalization are c on t and
one on d. The usual fixed-sum concavity and opposite-sign
interchange place positive variation on the smaller coefficient
and negative variation on the larger one. This gives exactly
the U, V and \(\Psi\) functions for (7), including either sign
of the original TD0 error.

After all half-shifts are collected, the unmodified baseline is
\[
\begin{split}
 {\cal B}(a)={}&2k+3l+3c+3+l j(a)\\
 &-R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
                      +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{9}
\]
It is exactly the pure-A full-D baseline in the negative-EH
endpoint certificates.

For \(s\le v\), the E contribution and H norm give the same
addition as in
[the small-error theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SMALL_ERROR_EXCLUSION.md):
\[
                  g(s)=\frac{13}{12}\sin s
                          -.656(1-\cos s).
\tag{10}
\]
For \(s\ge v\), Sections 2--3 of the remaining-error theorem give
\[
                G(s)=\frac{201}{200}g(s)-.00022
\tag{11}
\]
and the extra lower charge \(-\varepsilon P\), where
\(\varepsilon=.005\) and P is the remaining total positive mass.
Its fixed-p H singleton comparison and its E residual bound
are unchanged by the TD0 owner.

Deleting only the chosen A-primary arguments and EH from the
algebraic angular vector gives
\[
                  P\le h-a,\qquad N\le h-s,\qquad N-P=a-s.
\tag{12}
\]
The signed two-primary A comparison preserves this enlargement:
the deleted positive variation is at least a, and any deleted
negative variation weakens the displayed cap.

The two-simplex concentration proof works for four ordinary
blocks just as for three. It leaves pure U or V functions,
same-block functions at \(P=h-a,N=h-s\), and separated U/V
functions at those masses. In the far regime it subtracts
\(\varepsilon P\) throughout. The weighted inequalities require
one resulting lower stress to be nonpositive.

## 3. A negative D allocation is dominated by H

For every coefficient family used below,
\[
                            V_D(t)\ge V_H(t)
                                  \qquad(0\le t\le h).
\tag{13}
\]
When \(c\le1\), the pairs are \((c,1)\) and \((k,1)\), with
\(c>k\ge1/2\). The function \(V_{\xi,\zeta}(t)\) increases with
its smaller coefficient \(\xi\) for
\(\xi/\zeta\in[1/2,1]\).
If \(\xi-\zeta\sin t\le0\), the derivative sign is immediate.
Otherwise, positive squaring reduces it to
\[
 \zeta^2\sin t\{2\xi\zeta-(\xi^2+\zeta^2)\sin t\}\ge0.
\tag{14}
\]
The brace is nonnegative since
\(2\xi\zeta/(\xi^2+\zeta^2)\ge4/5>\sin h\).
This proves (13) when \(c\le1\).

The case \(c>1\) occurs here only in the small-s family, where
\(k\le.800408\) and \(c<1.022\).
The universal endpoint inequality \(V_{\xi,\zeta}(h)>.87\xi\)
and concavity give
\[
                        V_D(t)>\frac{87}{70}t
                                      \qquad(t>0).
\]
On the other hand
\[
 V_H(t)\le V_H'(0)t
      =\frac{Rk}{\sqrt{1+k^2}}t<1.24t.
\tag{15}
\]
The exact positive-square reserve at \(k=.800408\) is
\[
 1.24^2(1+.800408^2)-Q(.800408)^2
                      =\frac{110369107411}{7812500000000}>0.
\]
The two slopes differ by \(87/70-1.24=1/350\).
At \(t=0\) both functions vanish. This proves (13) in all cases.

## 4. The small EH interval

For \(0\le s\le v\) and \(L\le a\le h\), use the high family
from the negative-DE scalar theorem, exactly as in Section 4
of the small-EH theorem. With \(x=(15/8)(a-L)\), it is
\[
\begin{split}
 k&=.670158+.113718x+.006506x^2+.009026x^3+.001x^4,\\
 l&=1.005069-.146411x-.157739x^2+.162815x^3,\\
 c&=1.021248-.168873x-.165381x^2+.175944x^3.
\end{split}
\tag{16}
\]
Its already proved ranges include
\[
 \frac23<k\le.800408,\quad .863<l,\quad .862<c<1.022,\quad k<c.
\]
The old three pairs have
\(p_i/q_i>2/3\) and \(q_{\max}/q_{\min}<29/25\).
The D pair preserves both bounds:
\[
 \frac{p_D}{q_D}\ge\min(.862,1/1.022)>\frac23.
\tag{17}
\]
Moreover \(q_D=\max(c,1)\) is no larger than the old maximum
of \(1,l,c\), and is at least one, which is no smaller than
the old minimum. Thus neither extreme q changes.

Here \(s\le v<L\le a\), so the remaining excess is negative.
The same balanced comparison used in the small-EH theorem
therefore removes saturation for all four blocks:
same-block terms dominate their pure V term, while separated
terms exceed their pure V term by at least
\[
            \{2/3-.545(29/25)\}q_{\min}P
                                   >.0344q_{\min}P.
\tag{18}
\]
The new pure term \(V_D(a-s)\) is replaced by \(V_H(a-s)\)
using (13). Hence the only obligations are
\[
                  {\cal B}(a)+g(s)+V_i(a-s)>0,
                                  \qquad i=H,G,B.
\tag{19}
\]
These are precisely the high pure-A scalar functions from the
small-EH theorem, with its full D support.
Their concavity in s reduces to \(s=0,v\); its cited old
\(s=0\) certificates and its three new pure-A \(s=v\)
certificates are all positive.
Only their scalar definitions are reused; no original TD2
owner has been inferred.

## 5. The far EH interval with \(L\le a\le u\)

Now \(v\le s\le u\), and choose
\[
                k=.605,\qquad l=1-.36a,\qquad c=1.11-.77a.
\tag{20}
\]
These are the far-low weights at the pure-A endpoint.
On the current a interval,
\[
             .9175\le c\le\frac{589}{600}<1,\qquad c>l>k.
\tag{21}
\]
Thus D=\((c,1)\), and (13) removes every negative D allocation.

Every smaller-to-larger ratio of the four pairs exceeds .6,
every larger coefficient is at most one, and each same-block
ratio is below \(5/3\). The far-low same-block comparison,
which requires \(N=h-s\le.6\), applies to D as well. It pays
the extra \(\varepsilon\) charge and leaves its pure U or V
term.

The sole additional pure term is \(U_D(s-a)\) when \(s\ge a\).
It increases after adding G and the charge:
\[
 \frac{d}{ds}\{G(s)+U_D(s-a)-\varepsilon(s-a)\}
             >.8917-.72-.005=.1667>0.
\tag{22}
\]
Here \(U'_{\xi,\zeta}>-.72\zeta\) on \([0,h]\), the
D coefficient \(\zeta\) is one, and c is fixed while s varies.
Its minimum is therefore at \(s=a\), where it adds zero.

For a separated term with negative D, use (13) first.
For a separated positive D allocation, the far-low proof
also applies without change: \(U_D(P)\ge-.545q_DP\),
and \(q_D=1\le1.11\). The positive-mass charge is independent
of s. Its negative H/G part has
\(V'_{k,q}(h-s)<.876\), while \(G'>.8917\); thus the
separated function increases in s and reduces to \(s=v\).
At that endpoint the same estimates as (23)--(25) of
[the far-low concentration lemma](HAND_G3_CORE_E_NEGATIVE_EH1_FAR_LOW_ANGLE_CONCENTRATION.md)
dominate the H pure-V function with a strict reserve.
A negative B allocation is dominated by H exactly as there.

Consequently the only far-low obligations are
\[
 {\cal B}(a)+G(v)+V_H(a-v),\qquad
 {\cal B}(a)+G(v)+V_G(a-v),\qquad
                         {\cal B}(a)+G(a).
\tag{23}
\]
They are the A-split functions \(N_{LVH},N_{LVG},N_{LZ}\)
of the remaining-error theorem, already certified on the
larger interval \([v,u]\).
No new scalar certificate is needed.

## 6. The far EH interval with \(u\le a\le h\)

Choose the far-high family
\[
        k=.505+.4a,\qquad l=.9525-.17a,\qquad
                              c=.9645-.188a.
\tag{24}
\]
It has \(k<c<1\), so D=\((c,1)\).
All four pairs satisfy
\[
                p_i/q_i>.6,\qquad p_i\ge.605,\qquad q_i\le1.
\tag{25}
\]
The far-high concentration proof therefore applies to all four
blocks. Its same-block comparison has reserve \(>.032P\),
paying \(\varepsilon P\). Its universal derivative bound
\(V'_{\xi,\zeta}>1.03\xi\) on \([0,.6]\) gives the separated
reserve
\[
                         .07315P.
\]
There is no positive excess because \(s\le u\le a\).
After (13) removes the D pure-V term, the obligations are
\[
                    {\cal B}(a)+G(s)+V_i(a-s)>0,
                                      \qquad i=H,G,B.
\tag{26}
\]
Their concavity in s leaves \(s=v,u\).
These six functions are exactly the six high A-split
functions of the remaining-error theorem. All have positive
whole-interval numerator bounds.

## 7. Completion and retained scope

Sections 4--6 cover every \(s\in[0,u]\) when \(L\le a\le h\).
The fixed secant-H theorem covers \(0\le a\le L\).
Each branch contradicts the nonpositive weighted stress
required by the original necessary system, proving Section 1.

The proof retains the arbitrary actual TD0 argument in its
full-circle D block throughout. It uses only (2)--(4), ordinary
circle support, and the already certified continuous scalar
families. It introduces no additional angle sampling,
optimization premise, frame-order condition, or G1 premise
after a transport.

Together with the two negative-EH/TD2 notes, this closes a
single genuine negative EH1 with actual DE2, nonnegative
A-primary total, and either arbitrary TD0 or nonnegative TD2.
It does not assert the remaining simultaneous negative
E-primary, negative A-total, or large-A negative-TD2 cases.
