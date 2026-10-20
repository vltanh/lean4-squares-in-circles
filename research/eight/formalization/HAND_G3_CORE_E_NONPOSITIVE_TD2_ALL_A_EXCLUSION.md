# Core E and nonpositive TD2: every A and E owner

## 1. Complete scope

Work on the fixed-original-witness G0--G2 necessary system at
\[
                         Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
H, G, B and D are sorted outer Q states with signed tangents
positive, negative, negative and negative. E is a nonpositive
true core state. A and T may have either sign and either
canonical radial kind. Retain
\[
 \begin{gathered}
 HG\in\{0,2\},\qquad GA\in\{2,3\},\qquad AB\in\{0,2\},\\
 BT=2,\qquad TD=2,\qquad DE\in\{2,3\},\qquad EH\in\{0,1\}.
 \end{gathered}
\tag{2}
\]
The only error-sign assumption is
\[
                              d_{TD}\le0.
\tag{3}
\]
All other original errors may have either sign. Assume the
actual adjacent inequalities and captured global variation
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{4}
\]

There is no such necessary system. This removes every
A-primary and E-primary restriction within the core-E,
nonpositive-TD2 class. It retains BT2 and the specified outer
signs and radial states. It makes no assertion about outer E,
positive TD2, or the primary BT3 alternative.

## 2. The two completed A regimes

Call GA3 and AB2 the A-primary owners.

If there is no A primary, one nonnegative A primary, or two
A primaries whose signed errors have nonnegative sum, apply
[the core-E nonnegative-A theorem](HAND_G3_CORE_E_NONNEGATIVE_A_NONPOSITIVE_TD2_EXCLUSION.md).
That theorem allows every DE2/3--EH0/1 choice and every E
error sign under exactly (3). It also allows arbitrary errors
on whichever A edge retains its secondary owner.

If each selected A-primary error is nonpositive, apply
Section 6 of
[the complete fixed A/T-regime E theorem](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
It allows every E owner and error sign, and even either radial
kind at E. In particular it excludes a single negative
A-primary error, as well as two nonpositive A-primary errors.

Thus only two opposite-sign A-primary errors with negative
sum need a new scope join. No new scalar estimate is needed.

## 3. The local A reduction does not use an E owner

Write
\[
                   u=d_{GA},\qquad v=d_{AB},\qquad u+v<0,
\tag{5}
\]
and assume u and v have opposite signs.

The required local reduction is Sections 2--6 of
[the negative-A sum transport](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md).
Its original statement retains DE2 and EH0, so we make
explicit why its local conclusion applies to (2).

At original entry retain the established signed cut
\(y_A<1/2\) from
[the high-GA target theorem](HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md).
Its original-marker return permits arbitrary E owners, so
the cut is available in the present original class. It is
also unchanged by every earlier E-only reduction. This
retained cut is one input to the negative-AB2 entry comparison;
it is not being inferred from that two-state comparison alone.

The transport's displayed input consists only of the two
actual G--A and A--B inequalities, the unchanged sorted
outer G and B circles, and A's own signed circle/core data.
Its four caps are
\[
 \begin{aligned}
 U_-(r)&=-\tfrac12+(a_G-\tfrac12)\sec r-\tfrac{13}{12}\tan r,\\
 U_+(r)&=-\tfrac12+(a_G-\tfrac12)\sec r+\tfrac1{12}\tan r,\\
 L_-(r)&=\tfrac12+(\tfrac12-b_B)\sec r+\tfrac{13}{12}\tan r,\\
 L_+(r)&=\tfrac12+(\tfrac12-b_B)\sec r-\tfrac1{12}\tan r.
 \end{aligned}
\tag{6}
\]
No E coordinate, E frame, DE projection, or EH projection
appears in these caps, their gap derivatives, or the
constructed true-core path. The initial same-state
secondary-owner alternative is likewise the local
[negative-primary entry comparison](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md);
after the retained signed cut just stated, it uses A and
the incident outer G or B state.

Consequently the proof of that transport gives the following
alternative in the present system.

If the negative A-primary edge already has its actual
secondary projection feasible, select that projection.
The remaining A primary is positive. The system is then in
the first regime of Section 2, with no state or error changed.

Otherwise only A changes, on its true flat core. The output
is either
\[
 \begin{array}{ll}
 u'=u+v<0,\quad v'=0,&\text{with actual AB0},\\
 u'=0,\quad v'=u+v<0,&\text{with actual GA2}.
 \end{array}
\tag{7}
\]
Every other state and frame is fixed. Both positive and
negative variation decrease by the removed positive A error.
The signed total is preserved, and A's circle stays below Q.
The secondary projection at the aligned endpoint is an
actual equality of the two owner formulas there.

Thus (7) has just one negative A primary. It is excluded
by the second regime of Section 2.

## 4. Termination and preserved hypotheses

The case split has at most one local A transport. It never
changes E, T, the TD error, or any of the four outer anchors.
Its only changed neighboring inequalities are precisely the
two A inequalities proved along the local path. In particular
both actual E inequalities in (2), with their original
owners and errors, remain identical.

The terminal system retains core E, (3), and (4), and A is
again a valid canonical radial state. The downstream
theorems use those retained consecutive inequalities and
variation bounds directly. The constructed A path keeps
\(0<b_A<1/2\) by its explicit flat-core interval bounds;
it does not recover that bound by another marker argument.
No original marker value at the new A or repeated G1
reduction is required.

The nonnegative-sum, individual nonpositive, and
opposite-sign negative-sum cases exhaust all A-owner choices.
This proves the complete assertion of Section 1.
