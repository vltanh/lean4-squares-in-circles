# Core E with nonnegative primary total: all A and TD alternatives

## 1. Original scope

Work on the fixed-original-witness G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
The sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=2,\quad TD\in\{0,2\}.
\tag{2}
\]
A and T may initially have either sign and either radial kind.
E is nonpositive and is a true core state. At the two E edges,
allow any of the following:

* DE2 and EH0 with arbitrary errors, putting \(e=0\);
* DE3 with error \(e\ge0\), and EH0 with arbitrary error;
* EH1 with error \(e\ge0\), and DE2 with arbitrary error;
* DE3 and EH1 with arbitrary individual signs and nonnegative
  signed sum \(e=d_{DE}+d_{EH}\).

**There is no such original cycle.** Every A-owner combination,
both TD owners, and every sign of their errors are covered.
No frame order is assumed. The theorem retains BT2 and the
nonnegative E-primary total just stated; it does not cover a
genuinely negative E-primary total or an outer E.

The original errors have
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]
Only the actual neighboring inequalities, true core and circle
conditions, and these variation bounds are used after any A-only
transport. In particular no original-marker estimate is reapplied
to a transported state.

## 2. The smaller support cost of a core E

Use
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 c_0=\sqrt{Q/2}-\tfrac12,
\]
and the sorted outer support and its one-primary charge
\[
\begin{split}
 S(f,g)&=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},\\
 j(t)&=W(t)-1-S(\sin t,1-\cos t)\qquad(0\le t\le h).
\end{split}
\tag{4}
\]
An actual true core point satisfies
\[
                         0\le b_E\le a_E\le\frac7{12}.
\tag{5}
\]
The half-angle argument in
[the signed E-primary theorem](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md)
may retain these actual coordinates before taking a support.
Indeed its two monotone branches both end at
\[
                   W(e)-1-a_E\sin e-b_E(1-\cos e).
\tag{6}
\]
For a single DE3, the transverse term has the favorable opposite
sign, so the same lower bound remains valid. For a single EH1,
(6) is its direct intermediate charge. Thus in every E-primary
case of Section 1, deleting the designated primary arguments from
the four-circle force expression costs at least
\[
\begin{split}
 J_C(e)
 &:=\frac{13}{12}(\cos e-1)-\frac1{12}\sin e\\
 &\ge-\left(\frac{13}{12}\frac7{20}+\frac1{12}\right)e
   =-\frac{37}{80}e.
\end{split}
\tag{7}
\]
Here \(\sin e\le e\) and
\(1-\cos e\le e^2/2\le(7/20)e\) hold on the whole interval.
When no E primary is selected, use \(J_C(0)=0\).

The E inequalities always have equal multiplier one in the stresses
used below. Their unrotated D and H forces are exactly those of the
secondary E expression after the designated arguments are set to zero.
Their remaining signed-tangent terms cancel at the actual shared E.
All unchanged secondary E arguments remain in the force expression.
This is an algebraic comparison inside one positive weighted sum;
it asserts no new E witness or new E frame.

## 3. A uniform slope bound for the positive A charge

The exact support formula from
[the signed E theorem, Section 3](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md)
is
\[
 j(t)=
 \begin{cases}
  (\cos t-1)/2+(\tfrac12-a_0)\sin t,&0\le t\le t_0,\\
  \sin t-2\sqrt Q\sin(t/2),&t_0\le t\le h,
 \end{cases}
\quad
 t_0=2\arctan\frac1{2\sqrt{Q-1/4}}.
\tag{8}
\]
The formulas agree at the intrinsic support transition. On both
pieces,
\[
                             j'(t)<-\frac{457}{500}.
\tag{9}
\]
For the axis piece, \(a_0>707/500=1.414\). The function
\(\tfrac12\sin t+\tfrac{457}{500}\cos t\) is positive and
concave on \([0,h]\). Its value at zero is \(457/500\), and
its value at h exceeds that number, since
\[
 \frac12(.6442)+\frac{457}{500}(.7648)-\frac{457}{500}
                      =\frac{133909}{1250000}>0.
\tag{10}
\]
The usual alternating Taylor estimates give the two sine and
cosine lower bounds used here. Hence the derivative of the
first expression in (8) is strictly below \(-457/500\).

For the circle-interior piece, its second derivative is
\[
 \sin(t/2)\{\sqrt Q/2-2\cos(t/2)\}\le0.
\]
It is strictly negative for \(t>0\), using
\(\sqrt Q<1.98\) and \(\cos(.35)>.939\).
Its derivative is therefore at most \(1-\sqrt Q<-.97<-.914\).
This proves (9), including a comparison across the support
transition by continuity. In particular
\[
              j(a+e)\le j(a)-\frac{457}{500}e
                  \qquad(a,e\ge0,\ a+e\le h).
\tag{11}
\]

Every positive-A scalar family used in the
[all-A assembly](HAND_G3_HIGH_GA_ALL_A_PRIMARY_ALTERNATIVES_EXCLUDED.md)
has equal GA/AB multiplier
\[
                              l\ge\frac{89}{100}.
\tag{12}
\]
For positive TD2, the low family has \(l>1\), and the high
family has \(l>.89\), as proved in
[the two-positive endpoint theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_COMPLETE_SCALAR_EXCLUSION.md).
For arbitrary TD0, its low fixed value is \(1.26\), and its
high family is the same one; see
[the TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md).
For nonpositive TD2, the two fixed values are \(1.26\) and
\(.95\), in
[the nonpositive-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md).
The equality cases \(a=0\) are included in their scalar domains.

Combining (7), (11), and (12) gives the useful absorption:
\[
\begin{split}
 l j(a)+J_C(e)
 &\ge l j(a+e)+
       \left(\frac{457}{500}l-\frac{37}{80}\right)e\\
 &\ge l j(a+e)+\frac{4387}{12500}e.
\end{split}
\tag{13}
\]
The coefficient is a uniform rational reserve, not an additional
condition on the actual A or E coordinates.

## 4. All nonnegative A-primary totals

First suppose that the A owner choices have one of the following
forms:

* GA2 and AB0, with arbitrary errors, putting \(a=0\);
* one positive primary GA3 or AB2, whose error is \(a\ge0\);
* both GA3 and AB2, with arbitrary individual signs and
  nonnegative signed sum a.

An unselected A secondary edge keeps its actual arbitrary error.
For two selected primaries use
[the signed A-combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md);
for one, use the direct support comparison. Their total charge
is at least \(l j(a)\). If neither is selected, that charge
is \(l j(0)=0\). Delete exactly those designated A arguments
and the designated E arguments from the algebraic expression,
leaving all other arguments unchanged. Put
\[
                                  a'=a+e.
\tag{14}
\]
The original variation bound gives \(a'\le h\). Choose the
positive-A scalar weights at this new value \(a'\), and at
the retained TD parameter when that family also depends on TD.
These weights are then fixed throughout the charge comparison.
By (13), the combined A and E charge is at least \(l j(a')\).

Here is the full variation join for the three TD alternatives.
For TD0, the remaining arguments have sum \(-a'\), positive
variation at most \(h-a'\), and negative variation at most h.
For TD2 with \(z=d_{TD}\ge0\), delete that argument as in the
two-positive theorem. The remaining sum is \(-a'-z\), with
positive variation at most \(h-a'-z\) and negative variation
at most h. In particular \(a'+z\le h\).
For TD2 with error \(-w\le0\), its secant comparison leaves
sum \(w-a'\), positive variation at most \(h-a'\), and negative
variation at most \(h-w\).
Each inequality follows because the deleted positive parts
are at least the corresponding nonnegative signed totals.
Deleting any negative parts only enlarges the permitted domain.

The four-circle force expression is exactly the one in the
corresponding positive-A proof: every deleted primary contributes
an unrotated outer force, and every undeleted secondary argument
remains. Extra missing arguments may be inserted as virtual
zeros in its full-circle blocks. Conversely, when \(a=0\) and
no A argument was deleted, both actual A secondary arguments
are allowed by that enlarged block domain. The scalar proof
does not require that an effective positive charge parameter
correspond to a newly asserted original A witness.

Thus (14) satisfies the strict scalar exclusion already proved
for arbitrary TD0, nonnegative TD2, or nonpositive TD2, as
appropriate. The extra reserve in (13) only strengthens that
contradiction. All the A cases listed in this section are excluded.

## 5. A genuine negative flat-core A primary

It remains to treat a single negative A primary after any actual
secondary-witness selection. The local
[negative-primary entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
gives either an actual feasible secondary witness, which reduces
to Section 4, or a positive flat-core A with \(a_A=7/12\).
Writing its signed tangent as \(b_A>0\), the genuine cases obey
\[
\begin{array}{c|cc}
 \text{primary}&\text{tangent bound}&\text{error magnitude}\\ \hline
 GA3&b_A<39/250&s<1/4\\
 AB2&b_A<1/2&s<19/50.
\end{array}
\tag{15}
\]
The other A edge has its secondary owner and arbitrary error.

At fixed actual A, subtract its zero-angle primary projection
and include the width difference. The exact demand-minus-projection
increments at error \(-s\) are
\[
\begin{split}
 g_G(s)&=\frac{13}{12}\sin s-(b_A+\tfrac12)(1-\cos s),\\
 g_B(s)&=\frac{13}{12}\sin s+(b_A-\tfrac12)(1-\cos s).
\end{split}
\tag{16}
\]
Both are zero at zero and satisfy, on their respective closed
angle intervals in (15),
\[
                           g'_O(s)>\frac45,\qquad O=G,B.
\tag{17}
\]
For G, use \(\cos s\ge1-s^2/2,\ \sin s\le s\):
\[
 g'_G(s)>
 \frac{13}{12}\frac{31}{32}-\frac{82}{125}\frac14
 =\frac45+\frac{4103}{48000}>\frac45.
\tag{18}
\]
For B the same bounds give
\[
 g'_B(s)\ge
 \frac{13}{12}\left(1-\frac12(19/50)^2\right)
             -\frac12(19/50)
 =\frac45+\frac{907}{60000}>\frac45.
\tag{19}
\]
Consequently
\[
 g_O(s)-g_O(s')>\frac45(s-s')
            \quad(0\le s'<s),
\qquad
 g_O(s)\ge\frac45s,
\tag{20}
\]
with the second inequality interpreted non-strictly at zero.

If TD0 is retained, or TD2 has nonpositive error, the fixed
exclusion in Section 6 of
[the signed E theorem](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md)
already covers this single-negative A case, even without core E.
For the remaining positive TD2 case, the two subcases below
supply a stronger direct join. The second subcase also works
for either other TD alternative.

### 5.1. The E total does not exceed the negative A magnitude

Suppose \(0\le e\le s\), and put
\[
                               s'=s-e.
\tag{21}
\]
For positive TD2 choose the already certified negative-flat-core
weights at the reference magnitude \(s'\) and the unchanged
\(z=d_{TD}>0\), from
[the negative-flat-core scalar theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md).
Its two A weights are \(l\sec s'\) on the selected primary
and l on the other edge. In both coefficient families \(l>1\),
so its primary multiplier obeys
\[
                              \lambda=l\sec s'\ge1.
\tag{22}
\]
The old magnitude s is not used to choose the multiplier.

Compare the actual primary inequality at \(-s\) with its algebraic
reference at \(-s'\), at the same actual A state and using this
same chosen multiplier \(\lambda\). Its unrotated G or B force
does not change. The exact increase in demand minus projection
is \(\lambda\{g_O(s)-g_O(s')\}\), which by (20) is at least
\((4/5)\lambda e\). Adding the E charge from (7) leaves a
nonnegative extra gain
\[
            \lambda\{g_O(s)-g_O(s')\}+J_C(e)
                         \ge\frac{27}{80}e.
\tag{23}
\]

Deleting the E arguments changes the signed angular sum by
\(-e\). Replacing the negative A argument \(-s\) by \(-s'\)
changes it by \(+e\), so the reference vector again has sum
zero. If the deleted E arguments have negative variation n,
their positive variation is \(e+n\); the A shortening removes
another e of negative variation. Thus both total variations
decrease by exactly \(e+n\), and remain below h.
The reference negative magnitude stays within its original
cut in (15), and the actual A remains positive flat core.

The reference force expression and its enlarged variation
domain are therefore precisely those of the certified
negative-flat-core theorem. At \(s'=0\), either algebraic
owner projection has the same aligned value, which is already
included in its closed scalar domain. That theorem makes the
reference stress strictly positive. Equation (23) transfers
the same contradiction to the weighted original inequalities.
No virtual projection is asserted to be an original witness.

### 5.2. The E total exceeds the negative A magnitude

Suppose \(e\ge s\), and put \(a'=e-s\ge0\). Choose the positive-A
scalar family at \(a'\), and use its equal A multipliers l.
The actual negative primary is compared to its zero-angle
expression with that same l. By (7), (9), (12), and (20),
\[
\begin{split}
 l g_O(s)+J_C(e)-l j(a')
 &\ge
       \left(\frac45l-\frac{37}{80}\right)s+
       \left(\frac{457}{500}l-\frac{37}{80}\right)a'\\
 &\ge\frac{499}{2000}s+\frac{4387}{12500}a'\ge0.
\end{split}
\tag{24}
\]
Thus the deleted negative A primary and E primaries together
provide at least the positive-A charge \(l j(a')\).

Their deletion leaves signed sum \(s-e=-a'\).
Their deleted positive variation is at least e, hence at
least \(a'\); their negative variation includes s.
The remaining vector consequently lies in the same enlarged
positive-A domain as in Section 4. If a nonpositive TD2
argument is also removed, its negative variation is removed
in addition to s, so the bound \(N\le h-w\) is still valid.
For positive TD2, \(a'+z\le e+z\le h\).
All three TD alternatives therefore give the corresponding
positive-A scalar contradiction.

Sections 5.1--5.2 exclude every genuine single-negative A case.

## 6. Two A primaries with negative signed sum

Finally suppose GA3 and AB2 are both retained and their
signed sum is negative. Apply
[the actual negative-sum A transport](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md).
It covers both opposite signs and two negative errors.
Its first alternative selects an already feasible actual
secondary owner, leaving a single A primary, which the
preceding sections cover.

In its transport alternative only A changes. The output
has one aligned actual secondary A witness and one negative
primary, with their old sum unchanged. A stays positive and
on its true flat core, with tangent below \(1/2\); all four
outer states H, G, B, D and the original T/E states stay fixed.
The two variations decrease equally or stay unchanged.
In particular E is still the same core state, and its
designated nonnegative primary total e is unchanged.

If the terminal negative primary supplies its actual secondary
projection, Section 4 applies. Otherwise the local entry
inequalities recover the relevant cut in (15), exactly as in
Section 6 of the all-A assembly. This uses the retained outer
neighbor, flat-core A with tangent below \(1/2\), the local
projections, and their shifted-circle inequalities. It does
not reapply a global marker theorem after transport.
Sections 5.1--5.2 now apply to the transported necessary
system, with its proved circles, neighboring inequalities
and variation bounds.

This exhausts every A-owner and TD-owner/sign alternative
in (2), under the stated core-E/nonnegative-total hypothesis.
All new estimates in this note are whole-interval comparisons
with the explicit rational reserves (10), (13), (18), (19),
(23), and (24); no new coefficient family or angular mesh
is required.
