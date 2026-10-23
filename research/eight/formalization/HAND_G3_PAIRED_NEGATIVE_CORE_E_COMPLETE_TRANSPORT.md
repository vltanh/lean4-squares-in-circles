# Two negative core-E primary errors reduce to one by strict concavity

## 1. The boundary-cycle statement

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 K=\frac{13}{12},\qquad
 W(x)=\frac{1+\cos x+|\sin x|}{2}.
\tag{1}
\]
Use the actual G0--G2 boundary-neighbor cycle in cyclic roles
\((H,G,A,B,T,D,E)\). Its canonical quarter word is
\(0101011\), its real frames have spread below h, and E is
nonpositive. H and D are sorted outer Q states with positive
and negative tangents respectively. Retain an actual high GA
witness (owner 2 or 3), and retain
\[
             DE3\text{ at }-s<0,\qquad
             EH1\text{ at }-t<0.
\tag{2}
\]
E is on its true-core boundary. No assumption on the A/TD
owners, their errors, or their tangent signs is used in the
following reduction.

**Transport theorem.** Either an actual secondary E witness is
already available, or an E-only continuous boundary-neighbor
transport gives a necessary descendant with exactly one
negative E primary and an actual secondary witness at the
other E edge. Every other state, frame and selected witness
is unchanged. The signed error sum, positive variation and
negative variation are unchanged. The real-frame spread does
not increase.

The only additional endpoint of the local calculus is E with
zero tangent. In the stated high-GA cycle that endpoint is
impossible by
[the boundary-neighbor transport and E-zero theorem](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
Thus it supplies a contradiction, not an unproved terminal
case. The proof has no small-angle or adaptive-stress premise.

## 2. The exact EH cap

If EH0 is already feasible, select it and retain the unchanged
negative DE3 witness. Otherwise the pointwise negative-EH
entry theorem in
[the mixed-negative-E reduction, Section 2.1](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
gives
\[
                  a_E=\frac7{12},\qquad 0\le b_E<\frac{39}{250}.
\tag{3}
\]
The actual EH1 inequality is
\[
                   a_H-\frac7{12}\sin t-b_E\cos t\ge W(t).
\tag{4}
\]
It implies \(a_H>1\). Write
\[
 P=a_H-\frac12,\qquad
 D(x)=\frac{P-K\sin x}{\cos x}.
\tag{5}
\]
The sorted outer circle gives
\[
                         \frac12<P<\frac{183}{200}.
\tag{6}
\]
For example, the strict primary upper bound follows from
\[
 \left(\frac{283}{200}+\frac12\right)^2+\frac14-Q
                              =\frac{13}{8000}>0.
\]
Equation (4) is exactly \(b_E+1/2\le D(t)\).

There is a unique \(t_0\in(0,9/20)\) such that
\[
 D(t_0)=\frac12,\qquad
 D(x)\ge\frac12\quad\Longleftrightarrow\quad 0\le x\le t_0
                       \quad(0\le x\le h).
\tag{7}
\]
Indeed,
\[
 D'(x)=D(x)\tan x-K
            =\frac{P\sin x-K}{\cos^2x}<0.
\tag{8}
\]
Also \(D(0)=P>1/2\), and at \(x=9/20\) the lower Taylor
bounds give
\[
 \frac12\left(1-\frac{x^2}{2}\right)
  +K\left(x-\frac{x^3}{6}\right)-\frac{183}{200}
                             =\frac{347}{64000}>0.
\tag{9}
\]
The function \((1/2)\cos x+K\sin x\) increases on \([0,h]\),
since its derivative exceeds
\(K(3/4)-(1/2)(13/20)=39/80\). These facts prove (7).

At the unchanged original frame increase the E tangent
continuously to
\[
                         b_E=D(t)-\frac12.
\tag{10}
\]
This makes EH1 an equality. It preserves DE3, because its
coefficient of \(b_E\) is the positive number \(\cos s\).
It also preserves the true core, sorting, and circle containment:
throughout this initial segment,
\[
 0\le b_E\le D(t)-\frac12<P-\frac12<\frac{83}{200}<\frac12,
\]
\[
 \left(a_E+\frac12\right)^2+\left(b_E+\frac12\right)^2
 <\left(\frac{13}{12}\right)^2+\left(\frac{183}{200}\right)^2
              =\frac{723901}{360000}<\frac52<Q.
\tag{11}
\]
Every other selected neighboring inequality is unchanged.

## 3. One strictly concave required D primary

Subtract the H frame from all real frames, so
\[
               \theta_H=0,\quad\theta_E=t,\quad
               \theta_D=v=s+t,\qquad 0<t<v<h.
\tag{12}
\]
For
\[
                     0\le x\le x_1:=\min\{v,t_0\}
\tag{13}
\]
put E at real frame x and at the flat-core state
\[
                a_E(x)=\frac7{12},\qquad
                b_E(x)=D(x)-\frac12.
\tag{14}
\]
EH1 stays at equality. Its error is \(-x\), while the DE3
error is \(-(v-x)\). The DE3 inequality is precisely
\[
 a_D\ge B(x),\qquad
 B(x)=\frac12+(1-D(x))\cos(v-x)+K\sin(v-x).
\tag{15}
\]
This follows by substituting (14) into
\(a_D-(7/12)\sin(v-x)+b_E(x)\cos(v-x)\ge W(v-x)\).

The two derivatives, using (8), are
\[
 \begin{split}
 B'(x)&=\sin(v-x)-D(x)\frac{\sin v}{\cos x},\\
 B''(x)&=-\cos(v-x)+\frac{\sin v}{\cos x}
                                    \{K-2D(x)\tan x\}.
 \end{split}
\tag{16}
\]
Because \(2D(x)\ge1\), multiplication by \(\cos x>0\) gives
\[
 \begin{split}
 \cos x\,B''(x)
 \le{}&-\cos v+K\sin v+\cos v\sin^2x\\
      &-\sin v\sin x\{\cos x+\sec x\}.
 \end{split}
\tag{17}
\]
Here \(x\le v<h\), so \(\sin v\ge\sin x\),
\(\cos v\le1\), and \(\cos x+\sec x\ge2\). The last two
terms are at most \(-\sin^2x\). The elementary whole-interval
bounds \(\cos v>3/4\), \(\sin v<13/20\) therefore yield
\[
                 \cos x\,B''(x)<-\frac34+
                      \frac{13}{12}\frac{13}{20}
                      =-\frac{11}{240}.
\tag{18}
\]
In particular \(B''(x)<-11/240\) on the full intrinsic
interval (13). This is strict concavity, with no angle
subdivision or coefficient table.

## 4. A continuous feasible motion reaches an intrinsic endpoint

If E already has zero tangent at (10), the E-zero theorem
gives a contradiction immediately. Otherwise the original
parameter t lies strictly inside (13): \(t<v\) by \(s>0\),
and \(t<t_0\) by \(b_E(t)>0\).

Choose the direction of motion as follows. If \(B'(t)>0\),
decrease x to zero. Concavity makes \(B'(x)\ge B'(t)>0\)
on that whole segment, so B never increases along the motion.
If \(B'(t)\le0\), increase x to \(x_1\). Concavity makes
\(B'(x)\le B'(t)\le0\), with strict inequality for \(x>t\),
so again B never increases. Thus (15) stays feasible all the
way to the selected endpoint, with strict DE3 slack there.
Equations (7), (11), and (14) retain a sorted true-core E
and strict shifted-circle containment throughout.

The endpoints are exhaustive:

* At \(x=0\), E and H are aligned. EH1 and EH0 have the
  identical actual projection \(a_H-b_E=1=W(0)\).
  The remaining DE3 error is \(-v<0\).
* If \(x_1=v<t_0\), E and D are aligned. DE3 and DE2
  have the identical actual projection \(a_D+b_E\).
  The remaining EH1 error is \(-v<0\).
* If \(x_1=t_0\le v\), then \(b_E=0\). This is the
  E-zero endpoint excluded by the retained high-GA witness
  and the boundary-neighbor reflection theorem. The tie
  \(t_0=v\) belongs to this last alternative as well.

Only E has moved. Every frame used lies between the unchanged
H and D frames, which already belonged to the original frame
interval. The two changing errors are nonpositive and always
sum to \(-v\); their positive variation stays zero and their
negative variation stays v. All other errors stay fixed.
Consequently all the global variation bounds are preserved.

The hypotheses needed to apply the E-zero theorem remain
valid along both the initial tangent segment and the frame
motion. Both actual neighboring SAT inequalities stay
feasible, every square remains contained and outside the
true core, and every state remains on its canonical radial
boundary. The local central-depth gap theorem prevents a
neighboring angular gap from reaching zero. Hence the
original cyclic order persists. The precise G1/BT eligibility
and reflected owner map are supplied by the cited
boundary-neighbor transport theorem; no nonneighbor
separation or original marker value at the moved E is assumed.

This proves the transport theorem in Section 1. In particular
the original simultaneous-negative E case has no separate
low-angle concentration or adaptive-quadratic scalar obligation.

## 5. Closure when the A-primary total is nonnegative

The following complete exclusion is a scope join with the
already established one-primary theorems. Assume the high-GA
boundary cycle has H,G,B,D outer with signs positive,
negative, negative, negative, retains BT2, and has either TD0
at any error or TD2 at any error. A and T have arbitrary
signs and radial kinds. At A retain GA2/GA3 and AB0/AB2,
with no primary, a single nonnegative primary, or two
primaries whose signed total is nonnegative. Then **every
DE2/3--EH0/1 selection and every E-primary error allocation
is impossible**, for either E radial kind.

If E is outer, use
[the complete outer-E high-GA theorem](HAND_G3_OUTER_E_HIGH_GA_COMPLETE_WITH_BT2.md).
If the selected E-primary total is nonnegative, use that
note's Theorem A, valid for either radial kind. For a core E
with nonpositive TD2 use
[the all-A/E nonpositive-TD2 theorem](HAND_G3_ALL_A_E_OWNERS_WITH_NONPOSITIVE_TD2_EXCLUSION.md).
It remains to take core E, a negative E-primary total, and
either TD0 or positive TD2.

For exactly one negative E primary the applicable complete
theorems are:

| Retained negative primary | TD0 | Positive TD2 |
|---|---|---|
| DE3, with actual EH0 | [secant-D exclusion for A total at most 1/6](HAND_G3_CORE_E_NEGATIVE_DE3_SECANT_D_SUPPORT.md), followed by [the remaining TD0 interval](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_A_TD0_EXCLUSION.md) | [negative-DE TD2 exclusion](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md) |
| EH1, with actual DE2 | [negative-EH TD0 exclusion](HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_TD0_EXCLUSION.md) | [small negative-EH exclusion](HAND_G3_CORE_E_NEGATIVE_EH1_SMALL_ERROR_EXCLUSION.md) and [its remaining interval](HAND_G3_CORE_E_NEGATIVE_EH1_REMAINING_ERROR_EXCLUSION.md) |

Before using a genuine-EH bound, select actual EH0 if it is
feasible; otherwise the pointwise entry theorem supplies its
flat-core and angle hypotheses at the current state.

When both E primaries have negative total and opposite signs,
Sections 3--5 of
[the mixed-negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
give one of these one-primary systems, or select an already
feasible EH0 leaving a nonnegative E-primary total. Those
motions change only E and preserve every A/TD hypothesis.
When both E errors are negative, Sections 2--4 above give
the same one-primary alternatives or the excluded E-zero
endpoint. A zero E error already supplies the corresponding
aligned secondary witness.

This exhausts the E owners and error signs. The unchanged
single-primary estimates depend only on their stated circle,
true-core, actual-neighbor and variation data, all preserved
by the transports. They do not require the old E marker
value or any nonneighbor packing constraint.

## 6. Joint negative A/E totals with arbitrary TD0

Keep BT2 and arbitrary TD0 under the same high-GA boundary
hypotheses. Then the exclusion extends to every A/E owner
and error allocation.

Outer E is already covered by
[the complete outer-E high-GA theorem](HAND_G3_OUTER_E_HIGH_GA_COMPLETE_WITH_BT2.md).
For core E, Section 5 covers every nonnegative A-primary
total. A nonnegative E-primary total with arbitrary A is
covered by
[the core-E all-A theorem](HAND_G3_CORE_E_NONNEGATIVE_PRIMARY_TOTAL_ALL_A_EXCLUSION.md).
It remains to take both designated totals negative.

First use
[the negative-sum A reduction](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md)
and its
[same-state entry alternatives](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md).
These constructions involve only G,A,B. Their local equations
do not use any T/E witness, so every E datum and the actual TD0
owner and error stay fixed. If replacing a negative A witness
by its feasible secondary leaves a nonnegative designated
A total, Section 5 applies immediately. Otherwise the
reduction leaves one actual negative A primary and an actual
secondary on its other edge. The opposite-sign motion
decreases both variations equally; the both-negative motion
preserves them.

Next apply the E reductions in Sections 2--4 and in
[the mixed-negative-E note](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
They change only E and preserve the resulting A data, TD0,
all four outer anchors, and the variation bounds. A same-state
secondary reselection that leaves a nonnegative E-primary
total is covered by the core-E all-A theorem. The E-zero
endpoint is excluded by the retained high GA. Otherwise one
negative E primary remains, with an actual secondary on the
other E edge.

The resulting E is flat core. For negative DE3 with EH0,
the unchanged actual EH0 projection gives
\[
 b_E\le\sqrt{a_H^2+b_H^2}-1\le a_0-1<.415<\frac12,
\]
so its true-core boundary has \(a_E=7/12\).
For negative EH1 with DE2, select actual EH0 if available,
which exits to the already covered zero E total. Otherwise
the genuine negative-EH entry theorem gives
\[
             a_E=\frac7{12},\qquad 0<b_E<\frac{39}{250}.
\]

Now every selected A and E primary has a nonpositive error,
and \(a_E=7/12,\ 0\le b_E\le1/2\). The exact scope of
[the negative-flat-core-E fixed stress](HAND_G3_NEGATIVE_FLAT_CORE_E_FIXED_STRESS_EXCLUSION.md),
Section 1, includes simultaneous nonpositive GA3/AB2 and
DE3/EH1 alternatives, BT2, either HG owner, and TD0 at
an arbitrary error. It has no A radial-kind requirement.
Its strict inequality therefore excludes this last system.
All its inputs are the retained actual neighboring
projections, four sorted outer circles, flat E, and variation
bounds. No new packing or marker hypothesis is required.

This finite join covers arbitrary TD0 with all A/E data.
Together with the existing all-A/E nonpositive-TD2 theorem,
the only BT2 region left outside these results is a negative
A-primary total, a negative core-E primary total, and positive
TD2. BT3 remains a separate owner input.

No Lean files are changed, and no Lean compilation, CI,
state mesh or numerical acceptance premise is used.

