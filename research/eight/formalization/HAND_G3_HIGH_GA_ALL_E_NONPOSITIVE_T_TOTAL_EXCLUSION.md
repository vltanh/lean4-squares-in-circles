# High GA: every E owner with a nonpositive signed T total

## 1. Statement and exact inputs

Use the actual G0--G2 boundary-neighbor cycle at
\[
 Q=9789/2500,\qquad h=7/10,
\]
in cyclic roles H,G,A,B,T,D,E. H,G,B,D are sorted outer states
with signed tangents respectively positive, negative, negative,
negative. E is nonpositive and can have either canonical radial
kind. A and T have arbitrary signs and radial kinds. Retain
actual weak witnesses
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
\]
\[
 BT\in\{2,3\},\quad TD\in\{0,2\},\quad
 DE\in\{2,3\},\quad EH\in\{0,1\},
\]
and the actual variation bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.                 \tag{1}
\]
A selected primary total is zero with no selected primary,
the actual error with one, and the signed sum with two.
The primary pairs are GA3/AB2, BT3/TD2, and DE3/EH1.

**Theorem.** If the selected T-primary total is nonpositive,
there is no such cycle. Every A/E total, every original error
sign and both E radial kinds are included. No real frame order
is assumed.

The [earlier nonpositive-T theorem](HAND_G3_HIGH_GA_NONPOSITIVE_T_PRIMARY_TOTAL_EXCLUSION.md)
already handles nonnegative E total, and every outer E without
an E-total sign condition. This note supplies the negative
core-E region. It does not assert a positive-T-total case.

Write
\[
 R=\sqrt Q,\quad c_0=\sqrt{Q/2}-1/2,\quad
 a_0=\sqrt{Q-1/4}-1/2,
\]
\[
 \phi(x)=\sin x+\cos x,\quad
 W(x)=\frac{1+\cos x+|\sin x|}{2},\quad M_0=41/100.
\]
All terminating decimals in this note are exact rationals.

## 2. Actual negative core-E totals reduce independently

Assume that E is core and its selected total is negative.
The [mixed-negative E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
handles opposite individual signs. The
[complete paired-negative transport](HAND_G3_PAIRED_NEGATIVE_CORE_E_COMPLETE_TRANSPORT.md)
handles two negative errors. A zero primary error already
supplies its aligned secondary witness.

These E-only reductions preserve all A/T states, errors and
witnesses, the four outer anchors, and both variation bounds.
Their actual boundary-neighbor scope, including the forbidden
high-GA E-zero endpoint, is supplied by the
[boundary-neighbor bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
If selecting an already feasible secondary leaves a nonnegative
E total, the earlier nonpositive-T theorem applies immediately.
Otherwise one reaches exactly one negative E primary:

* DE3 at error \(-n\), with actual EH0. Its core is flat:
  \(a_E=7/12\). Indeed EH0 forces \(b_E<a_0-1<.415<1/2\).
* EH1 at error \(-n\), with actual DE2. Select EH0 if feasible.
  Otherwise the genuine negative-EH entry theorem gives
  \[
  a_E=7/12,\quad b_E<39/250,\quad 0<n<1/4.       \tag{2}
  \]

The entry assertions and their pointwise proofs appear in
Sections 2.1--2.2 of the mixed-negative E note. They use the
current actual projections. No original marker label is
reused at a changed E.

It is therefore enough to exclude these two one-primary
systems. Below, n always denotes their remaining negative
E magnitude.

## 3. A stronger charge for an actual nonpositive T pair

Let BT3 and TD2 both be selected, with actual errors u,v and
\(u+v=-s\le0\). Put \(A=a_T\), \(Y=y_T\), and define
\[
 L_T=W(u)+W(v)-2-A(\sin u+\sin v)
                         -Y(\cos v-\cos u).       \tag{3}
\]
The paired-primary lemma in the earlier nonpositive-T note
gives
\[
 L_T\ge\phi(s)-1,\qquad
 L_T\le a_B+b_D-2<.315,\qquad 0\le s<M_0.       \tag{4}
\]
The last conclusion follows from
\(C_6(M_0)+S_7(M_0)-1>.315\).

For a nonnegative selected A total, one may first select an
actual BT2 if it is feasible. The complete BT2 theorem for
nonnegative A total then excludes every E and TD alternative.
In the remaining case BT2 is not feasible. We prove the
stronger whole-domain charge
\[
                              L_T\ge .9s.          \tag{5}
\]

### 3.1 The intrinsic endpoint formulas

Put \(C=\cos(s/2)\), \(S=\sin(s/2)\), and
\(\Delta=|u-v|/2\). For two nonpositive errors,
\(0\le\Delta\le s/2\), and (3) is bounded below by
\[
 (C+2AS)\cos\Delta-2|Y|S\sin\Delta-1.
\]
This expression decreases in \(\Delta\). Its right endpoint is
\[
            (A+1/2)\sin s-(1/2+|Y|)(1-\cos s).    \tag{6}
\]

For opposite individual signs,
\(s/2\le\Delta\le h-s/2\). The actual formula is
\[
 (C+2AS)\cos\Delta+(C\pm2YS)\sin\Delta-1.        \tag{7}
\]
Both coefficients are positive. In fact \(|Y|<.9\) and
\(s\le .41\) give
\[
 C-2|Y|S>1-(.205)^2/2-1.8(.205)>.6.
\]
Thus (7) is strictly concave in \(\Delta\), and its minimum
is at an intrinsic endpoint. At the far endpoint, the generic
sorted lower bound in the earlier paired-primary proof gives
\[
                L_T\ge\phi(h)-1>.409>.9M_0.       \tag{8}
\]
It remains to control the near endpoint, where one actual
primary error is zero. Formula (6) controls either orientation.
When \(u\ge0\), the near endpoint is \(u=0,v=-s\), and
its more precise value is
\[
            (A+1/2)\sin s-(1/2-Y)(1-\cos s).       \tag{9}
\]

### 3.2 The three actual radial/sign cases

If T is outer, \(A\ge c_0>.899\) and \(|Y|\le A\).
Formula (6), and either near endpoint of (7), are at least
\[
                         1.399\{\phi(s)-1\}.
\]
This concave function vanishes at zero. Its endpoint value
exceeds \(.9M_0\), so it is at least \(.9s\) throughout.

If T is core, the global nonpositive-zero-source theorem
forces \(Y>0\). If \(u\ge0\), (9) is bounded below by
\[
                  (847/800)\sin s-\tfrac12(1-\cos s).
                                                               \tag{10}
\]
Here \(A>447/800\) is the true-core primary bound. The
expression in (10) is concave and vanishes at zero.

If T is core and \(u<0\), the absence of an actual BT2
witness permits the identical genuine-negative-primary
comparison used in Section 6 of the earlier nonpositive-T
note. It gives
\[
                  A=7/12,\qquad0<Y<39/250.
\]
Thus (6) is bounded below by
\[
                  (13/12)\sin s-(82/125)(1-\cos s),
                                                               \tag{11}
\]
again a concave function vanishing at zero.

For reproducibility, the lower Taylor bounds at \(M_0=.41\)
give the following exact reserves above \(.9M_0\):
\[
\begin{aligned}
1.399\{C_6(M_0)+S_7(M_0)-1\}-.9M_0
 &=\frac{12214683945487069727}{168000000000000000000}>0,\\
\frac{847}{800}S_7(M_0)+\frac12 C_6(M_0)-\frac12-.9M_0
 &=\frac{222490110232680133}{19200000000000000000}>0,\\
\frac{13}{12}S_7(M_0)+\frac{82}{125}C_6(M_0)-\frac{82}{125}-.9M_0
 &=\frac{255770458509049703}{30240000000000000000}>0.
\end{aligned}                                                  \tag{12}
\]
Together with (8), concavity proves (5). At s=0 the generic
paired charge is already nonnegative.

This proof is also valid at a transported flat-core positive
T endpoint: its positivity is explicit, and any needed
genuine-BT cut is derived anew from the current projections.
It does not inherit an angle cut from a previous state.

## 4. Every nonpositive A total: a fixed stress

Suppose the selected A total is \(-r\le0\). Use
\[
 k=.78,\quad l=1.26,\quad c=1.8,\quad
 \lambda=.946,\quad B=13/400.
\]
The [fixed flat-core-E stress](HAND_G3_NEGATIVE_FLAT_CORE_E_FIXED_STRESS_EXCLUSION.md)
proves for its algebraic secondary expression
\[
                 \mathcal C(\mathbf d)+\lambda\sum_i d_i>B
                                                               \tag{13}
\]
on the entire variation domain, without requiring a zero
signed sum. Its full two-angle D block permits arbitrary
remaining TD0 and DE2 errors.

For a single negative A primary use its multiplier
\(l\sec r\). The pointwise gain is at least
\[
 lJ(r),\qquad
 J(x)=\frac{847}{800}\tan x-\frac{183}{200}(\sec x-1),
 \qquad J'(x)>.79.
\]
It therefore pays at least \((\lambda+.0494)r\).
For a negative A-primary pair the actual inequalities give
\(r<M_0\), as in (4). Equal weights give at least
\(l\{\phi(r)-1\}\). Concavity and the exact comparison
\[
 l\{C_6(M_0)+S_7(M_0)-1\}-(\lambda+.024)M_0
       =\frac{47985587177419}{400000000000000000}>0              \tag{14}
\]
show that this gain pays \((\lambda+.024)r\), including
opposite individual A errors. No A transport is needed.

For a T-primary pair of total \(-s\), the generic bound in
(4) suffices here; no BT2 availability test is required.
Its gain obeys
\[
 c\{\phi(s)-1\}\ge(3681/3500)s
                         =(\lambda+37/350)s.       \tag{15}
\]
For a single negative BT3 use multiplier \(c\sec s\).
Deleting its argument from the virtual BT2 expression gives
gain at least \(cJ(s)>1.422s>\lambda s\). The actual
TD0 argument stays in the full D block of (13). A retained
BT2 with nonpositive TD2 or arbitrary TD0 is already in the
complete BT2 all-A/E domains.

For either negative flat-core E primary use its secant
multiplier. Its gain is at least
\[
 g(n)=\frac{13}{12}\tan n-\frac{183}{200}(\sec n-1).
\]
The exact one-variable argument in Section 4.2 of the fixed
flat-core-E note proves
\[
                         B+g(n)-\lambda n>0\quad(0\le n\le h).
                                                               \tag{16}
\]
After deleting the designated primary arguments, the reference
signed sum is \(r+s+n\); both variations only decrease.
Combine (13)--(16). The actual positive weighted demand minus
projection is strictly positive, contradicting feasibility.
This excludes every nonpositive A total.

## 5. Nonnegative A total at most 1/6

Let \(0\le a\le1/6\). First consider a T-primary pair.
If actual BT2 is feasible, use the complete BT2 theorem for
nonnegative A total. Otherwise use (5).

Take \(k=.78,l=1.26,c=1.8\) and charge \(\lambda=1.03\).
The signed A comparison costs exactly \(lj(a)\), with j
the common sorted-circle primary support charge. The
[small-A secant-H/D theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md)
supplies the charged ordinary blocks and the strict baseline
\[
                        B_0+\lambda a+lj(a)>49/15000.          \tag{17}
\]
Its net secant gains are at least
\[
 \begin{array}{ll}
 (\lambda+1/625)n,&\text{genuine negative EH1},\\
 (21/20+1/390)n,&\text{negative DE3 with EH0}.
 \end{array}                                                   \tag{18}
\]
The T pair is given equal weights c. Deleting both actual
T-primary arguments leaves their exact gain \(cL_T\), which
by (5) is at least \(1.62s\). Both ordinary T arguments are
now virtual zeros. This is a restriction of the reference
angle domain used in (17), so its charged bounds still apply.

The remaining signed sum is \(s+n-a\); hence the positive
stress is at least the right side of (17), plus the positive
reserves in (18), plus \((1.62-1.03)s\). It is strictly
positive, a contradiction.

A single negative BT3 with arbitrary TD0 can also be handled
directly here. Its secant comparison gives \(cJ(s)>1.422s\),
which exceeds the same charge 1.03s. The small-A theorem
allows the full ordinary two-angle D block, so no TD0 argument
is deleted or assumed aligned. This completes the small-A case.

## 6. Large nonnegative A total with a T-primary pair

Now \(1/6\le a\le h\), and BT3/TD2 are both retained with
total \(-s\). Again select actual BT2 if available; otherwise
use (5). Choose the exact constants
\[
 k=.717,\quad l=.914,\quad c=1.193,\quad
 M=1.045,\quad K=13/12,\quad\beta=.656.
\]
The new T gain satisfies
\[
                  cL_T\ge .9cs=1.0737s>Ms.         \tag{19}
\]
Deleting both T arguments fixes B's primary coefficient c
and D's transverse coefficient c. The remaining three
full-circle pairs are exactly
\[
                      H=(k,1),\quad G=(k,l),\quad B=(l,c).
\]
Their ordinary increments U,V and the diagonal D minorant
are those in Sections 4--5 of
[the core-E nonpositive-TD2 theorem](HAND_G3_CORE_E_NONNEGATIVE_A_NONPOSITIVE_TD2_EXCLUSION.md).

For negative DE3 of magnitude n, give that witness multiplier
\(q=\sec n\). The actual D force is \((q,c)\). Its exact
sorted-support correction is
\[
 F_D(n)=\frac{q-1}{2}+K\tan n-
          \{S(q,c)-S(1,c)\}\ge Mn,                \tag{20}
\]
proved over the whole interval in Section 2 of that note.
EH0 stays in the ordinary H block. D has no remaining
actual angular argument; adjoining its old zero-valued
minorant only enlarges the scalar domain.

For genuine negative EH1, keep its weight one. By (2),
its exact lower charge is
\[
                  g_E(n)=K\sin n-\beta(1-\cos n),\qquad n<1/4.
                                                               \tag{21}
\]
Its rotation is removed from H. DE2 remains an arbitrary
ordinary D argument, while the TD argument is zero. This
is precisely the one-angle sorted-D domain of the
[single-EH nonpositive-TD2 theorem](HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_NEGATIVE_TD2_EXCLUSION.md).
No unproved two-angle extension is being used here.

Put \(w=s+n\le h\). The ordinary variations satisfy
\[
 P\le h-a,\quad N\le h-w,\quad N-P=a-w.          \tag{22}
\]
This remains valid for an A or T pair with opposite signs:
the removed positive variation is at least a and the removed
negative variation is at least w. Their individual values
are not assigned independent budgets.

For DE3, (19)--(20) give the combined gain \(Mw\).
For EH1, (19)--(21) give
\[
 Ms+g_E(n)\ge\min\{Mw,J_M(w)\},
\]
where
\[
 J_M(w)=
 \begin{cases}
 g_E(w),&0\le w\le1/4,\\
 g_E(1/4)+M(w-1/4),&1/4\le w\le h.
 \end{cases}                                                   \tag{23}
\]
Indeed \(g_E(n)-Mn\) is concave on
\(0\le n\le\min(w,1/4)\), so only its two endpoints are
needed. This is exactly the gain comparison already proved
in Section 3 of the core-E theorem.

Its ordinary-angle concentration now applies without change.
With its exact baseline \(B_0>-.02093\), feasibility would
force a nonpositive member, for some \(C(w)=Mw\) or
\(C(w)=J_M(w)\), of
\[
 \begin{array}{ll}
 B_0+lj(a)+C(w)+V_i(a-w),&w\le a,\quad i=H,G,B,\\
 B_0+lj(a)+C(w)+U_i(w-a),&w\ge a,\quad i=H,G,B,D.
 \end{array}                                                   \tag{24}
\]
Every expression (24) is strictly positive by Section 5
of that theorem. This is a literal reuse of its constants,
baseline, domain and scalar functions: its unchanged
intrinsic endpoint bounds exceed .00468; the shifted
piecewise-gain endpoints exceed .04535 or .23237; the
linear-gain zero-increment endpoints exceed .00822 and
.05904; and the remaining linear endpoints exceed .24600.
The retained D correction is subtracted exactly once.

Thus the same completed whole-domain scalar proof excludes
the present T-primary pair. The only replaced input is the
old single-TD gain, now supplied by the actual paired gain
(19), which is strictly stronger than M times its total.

## 7. A single negative BT3 with arbitrary TD0 at large A

Suppose BT3 is the only selected T primary and its error
is negative. If actual BT2 is feasible, the all-E BT2 theorem
for nonnegative A total applies. Otherwise the genuine entry
proof gives a positive flat-core T, with
\(y_T<39/250\) and the original BT magnitude below 1/4.

Use the reflected
[negative-core alignment transport](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md),
as in Section 6 of the earlier nonpositive-T note. It changes
only T, retaining the actual B/D witnesses, the two error sum,
all A/E data, containment and the true core. The new T frame
lies between the original three frames; both total variations
decrease or remain unchanged. It reaches either:

* BT alignment, where actual BT2 is available; or
* TD alignment, where actual TD2 is available and the remaining
  BT3 error is negative.

The first endpoint is excluded by the all-E BT2 theorem with
nonnegative A total. At the second, use the two current actual
T-primary inequalities to derive \(s<M_0\) anew from (4).
If BT2 has become feasible, again use that theorem. Otherwise
the current negative-BT entry comparison gives the current
positive flat-core and small-tangent data. Sections 3 and 6
therefore exclude this paired endpoint.

The transported BT magnitude is not assumed to be bounded
by its original value. No angle or sign cut is inherited
without the applicable pointwise or actual-state argument.

## 8. Finite assembly and remaining scope

Nonnegative E total and outer E were already covered. For a
negative core-E total, Section 2 reduces to the two one-primary
patterns, with every T/A datum unchanged.

If BT2 is retained, arbitrary TD0 is excluded by Section 6
of the complete paired-E note; nonpositive TD2 is excluded
by the all-A/E nonpositive-TD2 theorem. If BT3/TD2 form a
nonpositive pair, Section 4 handles nonpositive A total and
Sections 5--6 handle nonnegative A total. If BT3 is the only
T primary, its zero error is an actual BT2 tie, and its
negative error is covered by Sections 4, 5 and 7. These
alternatives exhaust every nonpositive selected T total.

This proves the theorem in Section 1 for every E owner,
radial kind and signed total. The remaining high-GA work has
strictly positive selected T total. No unrestricted theorem
or normal-primary entry is asserted by this note.

The proof uses exact actual-state inequalities and whole-domain
analytic comparisons. No Lean changes, compilation, CI, angle
mesh, sampled minimum or generated coefficient table is used.
