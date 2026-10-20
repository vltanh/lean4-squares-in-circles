# High GA: every T owner when the E-primary total is nonnegative

## 1. Complete scope

Use the actual G0--G2 boundary-neighbor cycle at
\[
 Q=9789/2500,\qquad h=7/10,
\]
with the surviving word 0101011 and cyclic roles H,G,A,B,T,D,E.
Retain the globally forced sorted outer anchors H,G,B,D of
signed tangents positive, negative, negative, negative, and
nonpositive E of either canonical radial kind. A and T have
arbitrary signs and radial kinds. The actual weak witnesses are
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
\]
\[
 BT\in\{2,3\},\quad TD\in\{0,2\},\quad
 DE\in\{2,3\},\quad EH\in\{0,1\}.
\]
The real errors have zero sum, and their positive and negative
variations are each less than h. No real frame order is imposed.

A selected primary total is zero if neither primary is selected,
the actual error if one is selected, and the signed sum if both
are selected. The primary pairs are GA3/AB2, BT3/TD2, and
DE3/EH1. Opposite individual signs are permitted in every pair.

**Theorem.** No such high-GA cycle has nonnegative selected
E-primary total. Every selected A/T total, every surviving
original zero owner and every T error allocation is included.

**Outer-E corollary.** There is no high-GA cycle with outer E,
for any E-primary owner or error allocation.

## 2. The two positive T endpoints

If BT2 is retained, the complete
[BT2/nonnegative-E theorem](HAND_G3_OUTER_E_HIGH_GA_COMPLETE_WITH_BT2.md)
already excludes every A and TD alternative. Its nonnegative-E
statement applies to both radial kinds of E.

Suppose BT3 is retained with TD0. A nonpositive BT3 error is
covered by the
[complete nonpositive-T theorem](HAND_G3_HIGH_GA_ALL_E_NONPOSITIVE_T_TOTAL_EXCLUSION.md).
For a positive BT3 error, the two possible signs of the
selected A total have complete endpoint proofs:

| Selected A total | Positive BT3, arbitrary TD0, nonnegative E total |
|---|---|
| Nonnegative | [Unequal-T stress and full signed D support](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md) |
| Negative | [Secant-A stress and both E-total transfers](HAND_G3_NEGATIVE_A_POSITIVE_BT3_WITH_NONNEGATIVE_E_TOTAL_EXCLUSION.md) |

Both use the actual T circle and retain the arbitrary TD0
argument. Neither asserts a universal T-only conversion of
sole positive BT3. A zero BT3 error supplies actual BT2 and
is already included in the first paragraph.

## 3. Every signed T-primary pair

It remains to retain BT3 and TD2. If their selected signed
total is nonpositive, the complete nonpositive-T theorem
excludes the cycle without any A/E-total hypothesis.

If their total is positive, use
[signed T cancellation](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md)
when the individual signs differ, and the
[positive paired-T endpoint reduction](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
when both are nonnegative. A zero individual error already
supplies the corresponding aligned secondary witness.

Each transport gives an actual boundary-neighbor descendant
with either BT2 and positive TD2, or positive BT3 and TD0.
It changes only T, preserves every A/E state, error and
witness, and preserves or decreases both total variations.
The unchanged high-GA owner and outer anchors remain in
the same actual cycle. The
[boundary-neighbor bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md)
supplies the needed domain at each descendant.

In particular the nonnegative E total is unchanged. Both
possible descendants are excluded by Section 2. This is a
finite exhaustive join of the actual T-owner choices and
their signed totals, proving the theorem.

## 4. Outer E needs no E-total sign premise

For outer E, every nonpositive E-primary error already has
its actual secondary witness feasible at the same state and
frame. This is the pointwise
[outer-E negative-primary comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md).
Select those actual secondary witnesses. No square, frame,
coordinate, error or other edge witness changes.

Every remaining selected E-primary error is positive, so
the resulting selected E total is nonnegative, including
zero if no E primary remains. The theorem applies to this
same actual cycle. This proves the outer-E corollary for
every original selection and weak tie.

## 5. Residual endpoints and their completed global join

Combining this theorem with the complete nonpositive-T
theorem, any remaining high-GA candidate must have core E,
a negative selected E total, and a strictly positive selected
T total. The positive paired-T transports impose no A/E-total
hypothesis, so they still reduce such a candidate to one of
the following two endpoint domains:

| Remaining actual endpoint | Additional necessary sign data |
|---|---|
| BT2 and positive TD2 | Negative A total and negative core-E total |
| Positive BT3 and arbitrary TD0 | Negative core-E total; A total arbitrary |

For the first row, a nonnegative A total is already excluded
by the complete paired-negative-E theorem and its single-E
joins. For the second row, the present positive-BT endpoint
proofs require a nonnegative E total and supply no conclusion
about the displayed negative core-E region.

The independent negative-A and negative-E transports further
reduce a negative total to one genuine primary. The endpoints
displayed above are now excluded by the later
[joint-negative BT2 theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_TD2_EXCLUSION.md),
the two single-negative positive-BT theorems, and the
[joint-negative positive-BT theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_BT3_EXCLUSION.md).
Their complete finite join is the
[global GA-owner theorem](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md).
Thus high GA is now closed. The unrestricted theorem still
requires normal-primary GA1/BT3 entry into a sharp route.

All arguments are hand geometry and exact inequalities.
No Lean compilation, CI, sampled angle premise or generated
coefficient-row inventory is used.
