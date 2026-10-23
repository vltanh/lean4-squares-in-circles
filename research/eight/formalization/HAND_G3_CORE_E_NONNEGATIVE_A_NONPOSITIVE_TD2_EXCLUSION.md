# Every core E owner with nonnegative A total and nonpositive TD2

## 1. Scope and the new negative-E cases

Work on the fixed-original-witness G0--G2 necessary system at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 h=\frac7{10},\qquad L=\frac16,\qquad u=\frac14.
\tag{1}
\]
The sorted outer states H, G, B and D have signed tangents
positive, negative, negative and negative. E has nonpositive
tangent and is a true core state. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},\quad
 BT=2,\quad TD=2,\quad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
The TD error is nonpositive. At A allow the secondary pair,
one nonnegative primary, or both primaries with nonnegative
signed total a. Secondary A arguments have either sign.
A and T may have either sign and either canonical radial kind.

Assume the actual neighboring inequalities and the captured
variation conditions
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]
There is no such necessary system, for any choice and signs
of the E owners in (2). No frame order is assumed.

The new argument treats a negative DE3 together with either
an arbitrary actual EH0 or a genuine negative EH1. The other
E cases are joined in Section 6. For \(0\le a\le L\), the whole
statement already follows from
[the all-E fixed secant-H theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md).
It remains to prove the new negative-E cases for \(L\le a\le h\).

Use the fixed coefficients
\[
 \begin{gathered}
 k=\frac{717}{1000},\qquad l=\frac{457}{500},\qquad
 c=\frac{1193}{1000},\qquad M=\frac{209}{200}=1.045,\\
 K=\frac{13}{12},\qquad \beta=\frac{82}{125},\qquad
 \gamma=\frac{18247}{20000},\qquad \lambda=\gamma c=1.08843355.
 \end{gathered}
\tag{4}
\]
All decimals in this note are exact rationals.

## 2. A uniform derivative for the exact secant D correction

Let
\[
 \begin{split}
 c_0&=\sqrt{Q/2}-\frac12,\qquad d_0=c_0-\frac12<.4,\\
 S(f,g)&=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\}.
 \end{split}
\tag{5}
\]
For \(0\le n\le h\), put \(q=\sec n\) and
\[
 F_D(n)=\frac{q-1}{2}+K\tan n-\{S(q,c)-S(1,c)\}.
\tag{6}
\]
Then
\[
                         F_D(n)\ge Mn.
\tag{7}
\]

Here is a whole-interval support proof. The Taylor bound
\(\cos h>.7648\) gives \(q<1.308\), since
\[
                        1.308(.7648)-1=\frac{28}{78125}>0.
\tag{8}
\]
For \(q\le c\), the sorted support is diagonal:
\(S(q,c)=(q+c)c_0\). For \(q\ge c\), it is the interior
full-circle support
\[
                       S(q,c)=R\sqrt{q^2+c^2}-\frac{q+c}{2}.
\tag{9}
\]
There is no tangent-zero support branch. Indeed the
unconstrained shifted-circle maximizer has positive tangent
provided \(Qc^2>(q^2+c^2)/4\), and uniformly
\[
 Qc^2-\frac{1.308^2+c^2}{4}
                         =\frac{2993340959}{625000000}>0.
\tag{10}
\]
The two formulas match with their first derivatives at \(q=c\).

On the diagonal branch, differentiation gives
\[
                  F_D'(n)=\frac{K-d_0\sin n}{\cos^2 n}.
\tag{11}
\]
Writing \(y=\sin n\), its numerator minus \(M\cos^2n\)
is strictly larger than \(K-M-.4y+My^2\). Completing
the square gives
\[
 K-M-.4y+My^2\ge K-M-\frac{.16}{4M}
                                    =\frac7{125400}>0.
\tag{12}
\]

On the interior branch, direct differentiation of (6) and
(9) gives
\[
 F_D'(n)=
 \frac{K+\sin n\left(1-\dfrac{R}{\sqrt{1+c^2\cos^2n}}\right)}
      {\cos^2n}.
\tag{13}
\]
Here \(q\ge c\) forces \(\sin n>1/2\), because
\[
                         c^2-\frac43=\frac{269747}{3000000}>0.
\tag{14}
\]
Moreover
\[
 \frac{R}{\sqrt{1+c^2\cos^2n}}<1.47,
\]
as follows from
\[
 1.47^2\{1+c^2(.7648)^2\}-Q
                     =\frac{43181430291561}{976562500000000}>0.
\tag{15}
\]
The numerator in (13) minus \(M\cos^2n\) is therefore
larger than \(K-M-.47y+My^2\). This quadratic increases
for \(y\ge1/2\), and at \(y=1/2\) it equals
\[
                         K-M-\frac{.47}{2}+\frac M4=\frac{31}{480}>0.
\tag{16}
\]
Thus \(F_D'>M\) on both support branches. Since \(F_D(0)=0\),
integration proves (7), with a strict inequality for \(n>0\).

## 3. Exact collection of the three negative errors

First retain a DE3 error \(-n\le0\), and write the TD2
error as \(-t\le0\).

There are two E inputs:

* EH0 has arbitrary actual error. Its feasibility makes core E
  flat, \(a_E=7/12\), by Section 2.2 of
  [the negative-E transport note](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
  Put \(s=0\) to denote the absence of a removed EH primary.
  The actual EH0 error remains in the ordinary H block.
* EH1 has error \(-s\), where
  \[
          0\le s\le u,\qquad a_E=\frac7{12},\qquad
                                  0\le b_E\le\frac{39}{250}.
  \tag{17}
  \]
  These are the genuine negative-EH entry conditions from
  Section 2.1 of that same note. If an actual EH0 is already
  feasible, select it and use the preceding case instead.

Give the seven actual inequalities the multipliers
\[
                       (k,l,l,c,c\sec t,\sec n,1).
\tag{18}
\]
The published pointwise TD2 secant calculation gives, over
the algebraic zero-error TD0 projection, the gain
\[
 c\{(a_T+\tfrac12)\tan t+(\tfrac12-b_D)(\sec t-1)\}
                              \ge\lambda t.
\tag{19}
\]
This uses only \(a_T>447/800\), \(b_D<.9\), and
\(\tan(h/2)<183/500\); see Section 2 of
[the single-EH nonpositive-TD2 theorem](HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_NEGATIVE_TD2_EXCLUSION.md).
In particular the sign of T is unrestricted.

The exact secant DE3 projection is
\[
       \sec n\,P_{DE3}(-n)=\sec n\,a_D-\frac7{12}\tan n+b_E.
\tag{20}
\]
For EH0, the last term cancels its \(-b_E\) term.
For EH1 at \(-s\), the E force is instead
\[
              -\frac7{12}\sin s+b_E(1-\cos s).
\]
By (17), deleting this EH primary argument costs at least
\[
                         g(s)=K\sin s-\beta(1-\cos s).
\tag{21}
\]
It also removes the EH rotation from the H norm.

After (19), the actual D force is \((\sec n,c)\).
The change in its DE demand from the old zero-angle DE
demand is
\[
 \sec n\,W(n)-1+\frac7{12}\tan n
                              =\frac{\sec n-1}{2}+K\tan n.
\tag{22}
\]
Subtracting the exact change of the sorted D support gives
precisely \(F_D(n)\), not a full-circle replacement for its
diagonal baseline. Thus the combined negative-angle gain is
at least
\[
                         F_D(n)+g(s)+\lambda t.
\tag{23}
\]

Let
\[
                              w=n+s+t\le h.
\tag{24}
\]
By (7) and
\[
                       \lambda-M=\frac{868671}{20000000}>0,
\]
the gain (23) is at least
\[
                             Mw+\{g(s)-Ms\}.
\tag{25}
\]
At fixed w, \(0\le s\le\min(w,u)\). The function \(g(s)-Ms\)
is strictly concave, because
\(g''(s)=-K\sin s-\beta\cos s<0\).
Its minimum is at an endpoint of this actual interval.
Consequently (25) is bounded below by
\[
                           \min\{Mw,J_M(w)\},
\tag{26}
\]
where
\[
 J_M(w)=
 \begin{cases}
   g(w),&0\le w\le u,\\
   g(u)+M(w-u),&u\le w\le h.
 \end{cases}
\tag{27}
\]
For the EH0 input, \(s=0\), so the stronger linear bound
\(Mw\) alone applies.

This is a comparison inside the one positive weighted stress
(18). It changes no frame and asserts no virtual owner as an
original separating witness.

## 4. The unchanged ordinary-angle minimization

Delete the designated A-primary arguments and the DE, EH,
TD primary arguments accounted for above. For two signed
A primaries, their removed positive variation is at least a;
any removed negative A variation only enlarges the following
domain. The remaining masses satisfy
\[
                 P\le h-a,\qquad N\le h-w,\qquad N-P=a-w.
\tag{28}
\]
The selected A force costs at least \(l j(a)\), by the
[signed A-combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
Use exactly the support charge j, ordinary functions U and V,
and three coefficient pairs
\[
                     H=(k,1),\qquad G=(k,l),\qquad B=(l,c)
\tag{29}
\]
defined in Sections 2--3 of the single-EH nonpositive-TD2 theorem.

Its exact baseline is retained:
\[
 \begin{split}
 B_0={}&k+2l+2c+2-\overline S(1,k)-\overline S(l,k)
                   -\overline S(c,l)-(1+c)c_0>-.02093,\\
 \overline S(f,g)&=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
 \end{split}
\tag{30}
\]
The D support has already been evaluated at its actual force
and its correction extracted in (6). Its remaining angular
arguments are zero. For the ordinary minimization one may
adjoin the old D minorant with zero arguments and then allow
those arguments to vary. This enlarges the scalar domain.
It uses only the old minorant
\[
                          U_D(P)=-d_0P,\qquad V_D(N)=V_H(N);
\tag{31}
\]
it does not change the actual D support or subtract it twice.

All angle-concentration and saturation comparisons in
Sections 3--4 of the single-EH theorem therefore apply with
the same fixed pairs. In particular
\[
 \begin{gathered}
 V_i'>.767,\qquad U_i(x)\ge-.545q_i x,\qquad
 U_i'>-.64q_i\quad(0\le x\le h-L),\\
 .767-.545c=.116815>0,\qquad .767-.64c=.00348>0.
 \end{gathered}
\tag{32}
\]
They remove separated saturation for either sign of \(a-w\).
The ordinary same-block comparisons remove its saturation
as well. The linear D term is allowed in both separated
comparisons.

Feasibility would therefore force a nonpositive member of
the following family for at least one of the two choices
\(C(w)=Mw\) and \(C(w)=J_M(w)\):
\[
 \begin{array}{ll}
 B_0+l j(a)+C(w)+V_i(a-w),&0\le w\le a,\quad i=H,G,B,\\
 B_0+l j(a)+C(w)+U_i(w-a),&a\le w\le h,\quad i=H,G,B,D.
 \end{array}
\tag{33}
\]
It suffices to prove every member positive for both choices
of C, since (26) is their pointwise minimum.

## 5. Reusing the exact intrinsic endpoint bounds

The whole-interval facts needed from Section 5 of the
single-EH theorem are
\[
 \begin{gathered}
 j''<.02,\qquad -1.1<j'<-.69,\\
 V_i''<-.0648q_i,\qquad
 U_i''<-.1p_i\quad(0\le x\le h-L).
 \end{gathered}
\tag{34}
\]
They imply the same strict concavity in the A variable for
every ordinary U or V expression. The linear D term is
handled separately:
\[
             \frac d{da}\{l j(a)-d_0(w-a)\}<-.69l+.4=-.23066<0.
\tag{35}
\]
Its right endpoint has zero increment.

### 5.1 The piecewise gain \(J_M\)

At fixed a, concavity on the intervals cut by a and u reduces
w to
\[
                                0,\quad a,\quad u,\quad h.
\tag{36}
\]
The cut at u is retained; no global concavity across the
derivative jump is needed. At \(w=a\le u\), the old strict
concavity of \(l j(a)+g(a)\) applies. At \(w=a\ge u\),
\[
                         l j'(a)+M>M-1.1l=\frac{99}{2500}>0.
\tag{37}
\]
Thus the intrinsic endpoint list is exactly the eighteen
values in Sections 5--6 of the single-EH theorem, with only
its slope \(\lambda\) replaced by M after u.

The values \(I_i,II_i,III_i,IV_i,Z_L,Z_u\) from that theorem
are unchanged. Its three \(V_i^*\) values and \(Z_h\)
decrease by
\[
              (\lambda-M)(h-u)=\frac{7818039}{400000000}=.0195450975.
\tag{38}
\]
The published exact bounds therefore give
\[
 \begin{array}{c|ccc}
 i&H&G&B\\ \hline
 V_i^*(M)&>.28807&>.30608&>.23237
 \end{array}
 \qquad
                         Z_h(M)>.04535.
\tag{39}
\]
All unchanged values are strictly greater than .00468;
the smallest printed bound is the one for \(Z_L\).
Hence every value for the gain \(J_M\) is positive.

### 5.2 The linear gain \(Mw\)

Now the only w endpoints are \(0,a,h\).
For \(w=0\), the old \(I_i\) and \(II_i\) values apply.
For \(w=a\), the expression increases by (37), so its
minimum is at \(a=L\).
For \(w=h\), (34) reduces each ordinary U expression to
\(a=L,h\); (35) handles the linear D expression at \(a=h\).

The already certified rational enclosures
\[
 B_0>-.02093,\qquad j(L)>-.15866,\qquad j(h)>-.71283
\]
give the two no-increment bounds
\[
 \begin{split}
 B_0+l j(L)+ML&>\frac{616607}{75000000}>.00822,\\
 B_0+l j(h)+Mh&>\frac{2952169}{50000000}>.05904.
 \end{split}
\tag{40}
\]
Using the fixed \(U_i(h-L)\) enclosures in Section 7 of
the single-EH theorem gives
\[
 \begin{array}{c|ccc}
 i&H&G&B\\ \hline
 B_0+l j(L)+Mh+U_i(h-L)&>.30170&>.31971&>.24600.
 \end{array}
\tag{41}
\]
For completeness these use its same positive squaring
bounds for \(N_i(0)\), \(N_i(h-L)\), and
\[
 U_i(h-L)\ge
 p_i\{C_{10}(h-L)+S_{11}(h-L)-1\}
 -1.978787508\{n_{h-L,+}-n_{0,-}\}.
\]
Thus no new scalar interval subdivision or numerical
premise is introduced.

Equations (39)--(41) and the unchanged old endpoint bounds
prove strict positivity of every expression in (33).
This contradicts the nonpositive demand-minus-projection
stress required by the actual inequalities. It excludes
both new negative-E inputs of Section 3.

## 6. Every core E owner and error

We now remove the special E pattern of Section 3, while
keeping the nonnegative A total and nonpositive TD2 hypotheses.

If the E-primary total is nonnegative, including no primary
or one nonnegative primary, use
[the core-E nonnegative-total theorem](HAND_G3_CORE_E_NONNEGATIVE_PRIMARY_TOTAL_ALL_A_EXCLUSION.md).
It already allows every A and TD alternative and uses only
the retained necessary inequalities after a local transport.

Suppose the E-primary total is negative.

* A single negative EH1 with secondary DE2 is excluded by
  [the single-EH nonpositive-TD2 theorem](HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_NEGATIVE_TD2_EXCLUSION.md).
  If EH0 is already feasible, select it and invoke the
  [secondary-E all-A theorem](HAND_G3_HIGH_GA_ALL_A_PRIMARY_ALTERNATIVES_EXCLUDED.md).
  Otherwise the genuine entry conditions are (17).
* A single negative DE3 with secondary EH0 has flat core E,
  and is precisely the first input of Section 3.
* For two nonpositive E-primary errors, select actual EH0
  if feasible, reducing to the preceding case. Otherwise
  (17) holds and the simultaneous input of Section 3 applies.
  Aligned primary edges may be selected as their actual
  secondary witnesses.
* For two opposite-sign errors with negative sum, apply
  Sections 3--5 of
  [the negative-E transport theorem](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
  Negative DE and positive EH reach a single negative DE
  with an actual EH0 witness. Positive DE and genuine
  negative EH reach a single negative EH with an aligned
  DE2 witness. If EH0 was already feasible in the latter
  case, selecting it instead leaves one nonnegative DE
  primary, covered by the first paragraph of this section.

These E-only reductions preserve H, G, A, B, T and D,
their actual relevant inequalities, and the A-primary
total and TD error. They keep E on its true core with
circle value at most Q. They decrease positive and negative
variation together. All resulting necessary systems are
therefore in the already proved scopes; no original marker
estimate is reapplied.

This proves the theorem in Section 1. It retains BT2,
a nonnegative A-primary total, a nonpositive TD2 error,
and core E. It supplies no assertion about outer E or
about a negative A-primary total.
