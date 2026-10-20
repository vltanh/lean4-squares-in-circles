# Global GA owner rigidity from the complete high-GA exclusion

## 1. Statement for every original weak witness

Put
\[
 Q=9789/2500,\qquad h=7/10.
\]
Start with the original G0--G2 necessary cycle at a squared
radius \(q\le Q\), in the established orientation
\(y_E\le0\). The surviving quarter word is 0101011, with
cyclic roles H,G,A,B,T,D,E. Then
\[
 \boxed{\text{Every original GA witness has owner 0 or 1.}}
\tag{1}
\]
This includes every original weak tie. In the fixed-witness
boundary reduction, A is therefore positive outer. Combined
with the previous global owner conclusions, the four quarter
edges have the classes
\[
             GA\in\{0,1\},\quad BT\in\{2,3\},\quad
             DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
The corresponding boundary anchors H,A,B,D have signs
positive, positive, negative, negative. No sign of G or T,
real-frame order, or small-mismatch hypothesis is an input.

The proof below also excludes high GA on every actual
boundary-neighbor cycle in the sense of
[the boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
It thus applies to the actual descendants of the established
local transports, even when only consecutive nonoverlap has
been retained.

## 2. The complete high-GA necessary domain

Suppose that a chosen original GA witness has owner 2 or 3.
Apply the established G0 fixed-witness radial reduction at
the working ceiling Q. It preserves the chosen weak witness
and every other selected original neighboring witness.
The global owner, sign and outer-anchor theorems give
\[
 \begin{gathered}
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},\\
 BT\in\{2,3\},\quad TD\in\{0,2\},\quad
 DE\in\{2,3\},\quad EH\in\{0,1\}.
 \end{gathered}
\tag{3}
\]
H,G,B,D are sorted outer states with signs positive,
negative, negative, negative. E is nonpositive and can be
core or outer; A,T have either sign and either radial kind.
The high-GA target cut gives \(y_A<1/2\). The actual real
errors satisfy
\[
        \sum_i d_i=0,\qquad
        \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{4}
\]
Only H and D may be diagonal. The boundary-domain bridge
justifies these facts afresh at every transported canonical
endpoint; no old marker value is retained at a moved state.

The selected A primaries are GA3 and AB2; the selected T
primaries are BT3 and TD2; the selected E primaries are DE3
and EH1. For each pair its total is zero with no selected
primary, its actual error with one, and the signed sum with
two. Individual errors in a pair may have opposite signs.
Write these three totals as a, t and e. The finite proof
below exhausts all their signs and every owner in (3).

## 3. Three already complete regions

The following theorems impose no unstated total or frame-order
restriction:

| Actual domain | Complete exclusion |
|---|---|
| \(t\le0\), every a and e, either E radial kind | [All-E nonpositive T total](HAND_G3_HIGH_GA_ALL_E_NONPOSITIVE_T_TOTAL_EXCLUSION.md) |
| \(e\ge0\), every a and t, either E radial kind | [Nonnegative E total, every T owner](HAND_G3_HIGH_GA_NONNEGATIVE_E_TOTAL_ALL_T_EXCLUSION.md), Sections 2--3 |
| Outer E, every a, t and e | The same note, Section 4, by actual same-state secondary reselection |

In addition, **every high-GA cycle retaining BT2 is
excluded**, with either TD owner and arbitrary a,e. The
final missing BT2 region, negative a and negative core e
with positive TD2, is proved and joined to all earlier BT2
regions in
[the joint-negative positive-TD theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_TD2_EXCLUSION.md),
Section 8. Its proof uses the
[common-gain allocation lemma](HAND_G3_JOINT_NEGATIVE_A_CORE_E_COMMON_GAIN.md)
and [complete scalar certificates](HAND_G3_JOINT_NEGATIVE_A_CORE_E_SCALAR_CERTIFICATES.md).

Consequently any remaining necessary cycle would have
\[
        E\text{ core},\qquad e<0,\qquad t>0,
                      \qquad BT=3.
\tag{5}
\]

## 4. Reduce every positive T pair to the sole positive-BT endpoint

If TD0 is retained, (5) says that the actual BT3 error
\(z=t\) is strictly positive. Its TD0 error remains arbitrary.

If TD2 is retained, use the
[signed-cancellation transport](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md)
when the two individual T errors have opposite signs, and
the [positive-pair endpoint reduction](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
when both are nonnegative. A zero individual error already
supplies the corresponding secondary witness at that same
state. These transports impose no A/E-total assumption.

Every descendant has either BT2 with positive TD2, or
positive BT3 with TD0. The former is impossible by Section 3.
The latter is an actual boundary-neighbor cycle: only T has
changed, its true-core and circle conditions are retained,
the physical gaps remain positive, and both variations in
(4) are preserved or decreased. Every A/E state, owner and
error, all four outer anchors, and the high-GA witness are
unchanged. Thus (5) remains in force at the only surviving
endpoint. No universal conversion of sole positive BT3
into BT2 is asserted.

## 5. Every negative E total at positive BT3 and arbitrary TD0

We now have the actual endpoint
\[
       BT=3,\quad d_{BT}=z>0,\quad TD=0,
                         \quad E\text{ core},\quad e<0.
\tag{6}
\]
Both signs of a have complete proofs.

### Nonnegative A total

Use the actual negative-E reductions from
[the mixed-negative E theorem](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
and [the complete paired-negative core-E transport](HAND_G3_PAIRED_NEGATIVE_CORE_E_COMPLETE_TRANSPORT.md).
They change only E and preserve the A and T data, (3)--(4),
and the four outer anchors. If a same-state secondary
reselection makes e nonnegative, Section 3 applies. The
possible zero-E endpoint contradicts the retained high GA
by the boundary-domain bridge.

Every remaining endpoint has one genuine negative E primary
on the true flat-core side. Its other E edge has the actual
secondary witness at an arbitrary error. The two possibilities
are excluded by

| Genuine E primary | Positive BT3 with arbitrary TD0 and nonnegative a |
|---|---|
| Negative DE3, with EH0 | [Complete negative-DE theorem](HAND_G3_NEGATIVE_DE3_POSITIVE_BT3_WITH_NONNEGATIVE_A_TOTAL_EXCLUSION.md) |
| Negative EH1, with DE2 | [Complete negative-EH theorem](HAND_G3_NEGATIVE_EH1_POSITIVE_BT3_WITH_NONNEGATIVE_A_TOTAL_EXCLUSION.md) |

The negative-DE proof keeps the actual one-angle sorted D
support, the full signed TD0 argument, and the nonnegative
selected A total, including opposite signs in an A pair.
The negative-EH proof retains the actual two-angle D block.
Both allow either HG owner and all weak ties.

### Negative A total

The complete theorem
[for joint negative A/core E and positive BT3](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_BT3_EXCLUSION.md)
excludes this region. Its independent A/E transports reduce
to the four possible genuine one-A, one-E primary systems.
Section 7 of that theorem explicitly joins every same-state
secondary-reselection escape to the nonnegative-total
regions; it makes no sign-preservation assumption about a
reselected total.

Its coefficient hypotheses and two scalar inequalities are
proved by [the positive-BT scalar companion](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_BT3_SCALAR_CERTIFICATES.md).
The proof retains the variable secant at D. The
[enlarged two-angle D envelope](HAND_G3_SORTED_D_TWO_ANGLE_ENVELOPE_TO_SEVEN_FIFTHS.md)
covers \(1\le c\le1.4\), and the
[one-angle D comparison](HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md)
covers its other E alternative. The common negative-angle
allocation reduces all pure, same-block and separated cases
to two intrinsic endpoints. The separated case includes its
increasing convex secant penalty before the endpoint reduction.

Thus both signs of a in (6) are impossible. Sections 3--5
exhaust all owners and signed totals in (3), proving the
complete high-GA exclusion.

## 6. Transfer back to original witnesses and remaining global work

The contradiction is strict at Q. An original feasible high
GA witness at any \(q\le Q\), including a weak tie with a
low witness, would survive the fixed-witness boundary
reduction used in Section 2 and produce an excluded cycle.
Therefore every original witness is low, proving (1).
The global low-quarter sign and outer-anchor theorems give
the A conclusion and (2).

This exclusion uses the larger ceiling only to derive a
strict impossibility. It does not transport an equality
configuration from q to Q and back. Original-center
sharpness and the five-parameter equality family still
require entry into the completed sharp route at the
original radius.

The remaining owner-entry issue is consequently **GA1 and
BT3 within the normal quarter classes**. Neither (1) nor
the positive-T transport from the high-GA proof declares
those owners globally convertible to GA0/BT2. The completed
arbitrary-sign, arbitrary-frame hard-owner theorem remains
available once those actual hard witnesses have been
supplied. Alternatively, the complete small-mismatch terminal
is available once its global mismatch premise is proved.

Every scalar certificate used here covers its full analytic
interval by exact inequalities. No angle or state mesh,
sampled optimizer minimum, generated coefficient-row inventory,
Lean compilation or CI is a premise.
