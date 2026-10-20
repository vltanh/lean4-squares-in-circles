# Every A and E owner when TD2 is nonpositive

## 1. Scope

Work on the original fixed-witness G0--G2 boundary cycle at
\[
                         Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
H,G,B,D are sorted outer Q states with signed tangents positive,
negative, negative and negative. E is nonpositive and has either
canonical radial kind. A and T have either sign and either
canonical radial kind. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},\quad
 BT=2,\quad TD=2,\quad DE\in\{2,3\},\quad EH\in\{0,1\},
\tag{2}
\]
and the actual inequalities and captured variation conditions
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]
The only error-sign input is
\[
                              d_{TD}\le0.
\tag{4}
\]

**Theorem.** There is no such original cycle. Every A-primary
and E-primary owner and every sign allocation on their errors
is included.

**Outer-E TD0 corollary.** If E is outer, the same exclusion holds
with TD0 of arbitrary error in place of (4).

Both statements retain BT2 and the displayed outer-anchor signs
and radial states. The theorem does not cover positive TD2, and
the TD0 corollary does not assert the corresponding core-E case.

## 2. Core E is already complete

If E is core, apply
[the audited core-E all-A theorem](HAND_G3_CORE_E_NONPOSITIVE_TD2_ALL_A_EXCLUSION.md).
Its scope is exactly (1)--(4), including arbitrary DE/EH owners
and error signs, arbitrary A owners, and either sign and radial
kind at T. This finishes the core-E part of the theorem.

For the rest of the proof E is outer.

## 3. Actual same-state E witnesses give a nonnegative total

Sections 2--3 of
[the outer-E witness comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md)
prove that every feasible DE3 of nonpositive error also has
its actual DE2 projection feasible, and every feasible EH1 of
nonpositive error also has its actual EH0 projection feasible.
Each conclusion uses the unchanged D,E,H states and frames.

Select these actual secondary projections at every nonpositive
E-primary edge. No center, error, frame, or positive/negative
variation changes. Every E primary that remains has positive
error. Consequently the selected E-primary total e is nonnegative,
including e=0 if none remains.

The following two statements now cover the first A regime:

* For TD2 satisfying (4), use
  [the nonnegative-A/E negative-TD2 theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_NEGATIVE_TD2_EXCLUSION.md).
* For the outer-E TD0 corollary, use
  [the nonnegative-A/E TD0 theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).

Both permit no A primary, one nonnegative A primary, or two
A primaries with nonnegative signed total. The secondary A
arguments, if any, remain arbitrary.

If instead every selected A-primary error is nonpositive,
Section 4, regime 1, of the outer-E witness comparison already
excludes the system. That fixed-stress regime permits either
TD0 of arbitrary error or TD2 of nonpositive error, and every
E owner and error sign.

Thus only two opposite-sign A-primary errors with negative
signed sum remain.

## 4. The unchanged local A transport closes the last A regime

Write
\[
                        u=d_{GA},\quad v=d_{AB},\quad u+v<0,
\tag{5}
\]
with u and v of opposite signs.
At original entry retain the signed cut \(y_A<1/2\) from
[the high-GA target theorem](HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md).
That original-marker theorem allows arbitrary E owners. The
same-state E selections above leave A untouched, so the cut
is still available.

Apply Sections 2--6 of
[the local negative-A sum reduction](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md).
Its local proof uses only the G--A and A--B inequalities, the
unchanged sorted outer G/B circles, A's own circle/core data,
and the retained signed cut at entry. The explicit scope
verification for arbitrary E owners is also recorded in Section 3 of
[the core-E all-A assembly](HAND_G3_CORE_E_NONPOSITIVE_TD2_ALL_A_EXCLUSION.md);
that verification does not use E's radial kind.

There are two possibilities.

If the negative A-primary edge already has its actual secondary
projection feasible, select it. The remaining A primary has
positive error. The nonnegative-A theorem in Section 3 applies,
with every state and E witness unchanged.

Otherwise the reduction moves only A, on its true flat core,
and ends with
\[
 \begin{array}{ll}
 u'=u+v<0,\quad v'=0,&\text{with actual AB0},\\
 \text{or}\quad u'=0,\quad v'=u+v<0,&\text{with actual GA2}.
 \end{array}
\tag{6}
\]
Both positive and negative variation decrease by the removed
positive A error. The signed sum is preserved. All four outer
anchors, E, T, every E owner/error, and the TD owner/error remain
fixed. A's constructed circle stays below Q and its explicit
flat-core interval has \(0<b_A<1/2\).

The output has one negative A primary. It is excluded by the
fixed outer-E regime in Section 3.

This last invocation is pointwise in the retained consecutive
inequalities. Its original-circle supports, secant gains, and
variation argument apply to the constructed flat-core A. It does
not require a new marker value at A or another G1 reduction.
In particular the retained \(b_A<1/2\) is supplied by the path,
not recovered by reapplying the original signed-cut theorem.

## 5. Exhaustion and termination

The nonnegative-total, individually nonpositive, and opposite-sign
negative-total cases exhaust every selection of GA2/GA3 and
AB0/AB2. At most two actual same-state E-owner selections and
one local A transport have been used. The process keeps every
hypothesis required by the terminal geometric stresses.

The core-E theorem of Section 2 and the outer-E argument of
Sections 3--4 prove (4) for both E radial kinds. The same
outer-E argument uses no sign of the TD0 error, proving the
stated TD0 corollary.

No new scalar estimate is required by this assembly. It does
not alter any marker after moving A, assume a frame order, or
use a state mesh, numerical acceptance premise, Lean compilation,
or CI.
