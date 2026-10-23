# Outer E excludes the entire high-GA branch with BT2

## 1. Two complete original-owner statements

Work on the original fixed-witness G0--G2 boundary cycle at
\[
                        Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
H,G,B,D are sorted outer states with signed tangents respectively
positive, negative, negative and negative. E is nonpositive and
has either canonical radial kind; A and T may have either sign
and either canonical radial kind. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=2,\quad TD\in\{0,2\},\quad
 DE\in\{2,3\},\quad EH\in\{0,1\},
\tag{2}
\]
and the actual inequalities and variation bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+<h,\qquad\sum_i(-d_i)_+<h.
\tag{3}
\]
No frame order is assumed.

An E-primary total is the selected DE3 or EH1 error when
exactly one primary is retained, their signed sum when both
are retained, and zero when neither is retained. A secondary
E error remains arbitrary.

**Theorem A.** There is no such cycle when the designated
E-primary total is nonnegative. Every A-primary combination,
both TD owners, and every sign of their errors are included.

**Theorem B.** If E is outer, there is no such cycle for any
original DE/EH owner or error allocation. Thus the entire
outer-E high-GA branch is excluded while BT2 is retained.

Neither statement removes the independent BT3 alternative.
Theorem A does not exclude a negative E-primary total with
core E. The proof below is a finite scope join of continuous
inequalities and local transports already established in the
linked notes.

## 2. Nonnegative A total and the already complete TD regimes

Call GA3 and AB2 the A-primary owners. If no A primary is
selected, exactly one A primary is selected and its error is
nonnegative, or both have nonnegative
signed total, the two proved nonnegative-A/E theorems apply:

* [TD0 or nonnegative TD2](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md);
* [nonpositive TD2](HAND_G3_NONNEGATIVE_A_E_TOTALS_NEGATIVE_TD2_EXCLUSION.md).

Their domains include opposite individual signs within either
primary pair and either E radial kind. Together they exclude
every TD owner/error in this A regime.

Independently, if TD2 has nonpositive error, the
[all-A/E nonpositive-TD2 assembly](HAND_G3_ALL_A_E_OWNERS_WITH_NONPOSITIVE_TD2_EXCLUSION.md)
already covers all A cases for either E radial kind. If TD0
is retained and E is outer, that same note's outer-E TD0
corollary covers every A case. If TD0 is retained and E is
core, the
[core-E nonnegative-total assembly](HAND_G3_CORE_E_NONNEGATIVE_PRIMARY_TOTAL_ALL_A_EXCLUSION.md)
covers every A case under the present hypothesis.

Therefore the only remaining part of Theorem A is TD2 with
positive error and a negative A-primary total.

## 3. One genuinely negative A primary

Suppose first that only one selected A primary has negative
error −s, and the other A edge retains its secondary owner.
At original entry retain the signed cut \(y_A<1/2\) from
[the global high-GA target theorem](HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md).
That cut permits arbitrary E owners and errors.

The actual same-state alternative in
[the negative-A entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
either supplies the corresponding feasible secondary witness,
which reduces to Section 2, or makes A positive flat core.
Its genuine GA3 branch has \(b_A<39/250,s<1/4\); its genuine
AB2 branch has \(b_A<1/2,s<19/50\). Every other state,
owner, error and variation bound is unchanged.

Let e≥0 be the retained E-primary total. If e≤s apply
[the shorter-E negative-A transfer](HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md).
If e≥s apply
[the longer-E negative-A theorem](HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md).
Both permit either E radial kind and every signed allocation
within its designated nonnegative primary total. Their union
covers all e≥0, including e=s and zero endpoints.

Thus every genuine single-negative A case is excluded.

## 4. Two A primaries with negative signed total

Write \(u=d_{GA},v=d_{AB}\), with u+v<0, and retain GA3 and
AB2. The local
[negative-sum A reduction](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md)
covers opposite signs, two negative errors, and zero endpoints.
Although that note's initial full-cycle statement retains
secondary E owners, its local construction requires only the
G--A--B triple, the two unchanged outer G/B circles, the
retained original signed A cut, and the original A circle/core
data. Its scope verification for arbitrary E owners is written
explicitly in Section 3 of
[the core-E all-A assembly](HAND_G3_CORE_E_NONPOSITIVE_TD2_ALL_A_EXCLUSION.md).
That verification uses no assumption on E's radial kind.

If a negative A-primary edge already has its actual secondary
projection feasible, select it. The remaining primary is
either nonnegative and covered by Section 2, or negative and
covered by Section 3.

Otherwise the reduction moves only A along its true flat core.
It ends with exactly one negative A primary of error u+v and
an actual aligned secondary projection on the other edge.
The new A tangent is positive and less than 1/2, and its
shifted corner is strictly contained at Q. All four outer
anchors, T, E, and every TD/DE/EH owner and error remain fixed.
Both total variations decrease equally or stay unchanged, and
the signed sum remains zero.

At the output, use the same local secondary-owner alternative
again if needed. If no secondary witness is feasible, its
pointwise shifted-circle inequalities recover the genuine
primary cuts used in Section 3. This uses the retained flat-core
A with tangent less than 1/2 and its unchanged incident outer
neighbor; it does not repeat the original-marker theorem.

The two scalar exclusions in Section 3 explicitly permit this
necessary comparison system. Their force sums and concentration
arguments use precisely its retained neighboring inequalities,
corners, and variation bounds. The original E-primary total
is unchanged. Section 3 therefore excludes the output and
completes the negative-sum case.

Sections 2--4 exhaust every A-primary owner and error allocation,
proving Theorem A.

## 5. An outer E supplies the required nonnegative total

Assume now that E is outer, with arbitrary original DE/EH
owners and errors. The actual
[outer-E negative-primary comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md)
proves that each feasible DE3 of nonpositive error has its
same-state DE2 projection feasible, and each feasible EH1 of
nonpositive error has its same-state EH0 projection feasible.

Select those secondary witnesses at every nonpositive E-primary
edge. No center, frame, error, signed sum or variation changes.
Every primary remaining at E has positive error, so its designated
total e is nonnegative, with e=0 if neither remains.
Theorem A now gives a contradiction. This proves Theorem B
for every original E-owner and error allocation.

At most two same-state E-owner selections and one A-only
transport are used. The proof preserves every hypothesis of
its terminal stress inequalities, uses no frame-order assumption,
and invokes no state mesh, sampled minimum, numerical acceptance
premise, Lean compilation, or CI.
