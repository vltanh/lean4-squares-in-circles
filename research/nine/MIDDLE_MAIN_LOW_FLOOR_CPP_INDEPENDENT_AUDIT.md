# Independent audit of the complete middle-main low-floor checker

November 2, 2026. Reviewer: the separate `whole_mask` agent. **Result:
PASS; no mathematical, formula-parity, coverage, or unsafe-pruning gap
found.** This is an independent agent review, not a human or
proof-assistant verification. No Lean or CI was used.

## 1. Exact review boundary

The frozen C++ checker is
`../agent_roots/verify_middle_main_low_floor_exact.cpp`, SHA256
`96ac00e7069e20dcbf39dfb6e092349773300edc3689549f791f32c6c557bd00`.
The independently implemented Python reference is
`../agent_low_floor/verify_middle_main_side_triple.py`, SHA256
`c1e26b7c6184c2636c3eb66c1f267b076f84b852a9c7fe39e6c26e7a2029fe29`.
Both hashes were freshly recomputed during this review.

The completed certificate has SHA256
`faf9cc6967ce02412024f0fe90db6298931d0c243bce6cf345ad78dda2785a9c`.
It has 5,642,527 nodes, 2,821,264 leaves, and maximum depth 52.
The lossless archive has SHA256
`ad5275e67b28a15d86cea564cd6221149a9c7cf7e4470dfe4762c296e4f8e76e`.

The separate full C++ arithmetic replay is recorded in
`../agent_roots/middle_main_low_floor_cpp_replay.json`: every leaf passed,
with least positive reserve `360606/281474976710656`. That full arithmetic
replay was performed by the separate agent. The present review does not
claim to be a second execution of all 2.82 million arithmetic leaf tests.
It instead supplies a complete independent source/formula audit, plus a
fresh full structural replay and archive-identity check, recorded in
`middle_main_low_floor_independent_structure_audit.json`.

## 2. Integer arithmetic and exact root cells

The 48-bit interval kernel uses directed integer arithmetic. Signed floor
division subtracts one exactly when C++ truncation toward zero would be
too high; signed ceiling division adds one exactly when truncation would
be too low. Multiplication forms all four endpoint products in signed
128-bit arithmetic, and applies the appropriate directed quotient.
Division encloses the reciprocal of a strictly positive denominator and
then multiplies outward. Squaring handles an interval crossing zero.
Absolute value and negation have the correct signed endpoint order.

The integer square-root iteration starts above the root, descends by
integer Newton steps, and verifies both defining integer inequalities
before returning. The interval square root rounds its lower endpoint
down and its upper endpoint up. Clipping a negative lower radicand to
zero is used only as a relaxation of the physical subdomain on which the
actual radicand is nonnegative. A strictly negative upper radicand is
handled as an impossible physical branch.

All interval endpoint products fit signed 128-bit arithmetic because their
factors are checked signed 64-bit integers. Narrowing back to 64 bits is
checked. The root-cell numerator construction fits signed 128 bits even
at the admitted depth 60: its largest original denominator is 12,000,
and the extra interval scale is only 2^48. The actual tree reaches depth
52. The few raw scalar additions are bounded by the geometric constants
and the finite 1,000 sentinels; they do not approach signed 64-bit limits
on a surviving branch.

Root cells use exact integer level/index data, not rounded interval
midpoints. The seven exact roots are

\[
 [0,1],\ [1/27,1],\ [0,1],\ [29/60,13/12],\
 [-23/60,23/60],\ [29/60,13/12],\ [4421/12000,1/2].
\]

For a root with numerator endpoints L,R and denominator D, a cell at
level j and index i has exact endpoints
`(L*2^j+(R-L)*i)/(D*2^j)` and the same numerator plus R-L.
The C++ conversion rounds those endpoints outward only after defining
the exact cell. Left and right children therefore cover their parent
and retain every common face.

## 3. Complete parser and tree coverage

The parser requires the exact six-field certificate schema. It rejects
duplicate or unknown fields, missing fields, malformed integer tokens,
unsupported events, a wrong root family, a wrong status, and trailing
data. The only accepted terminal tag is `-6`, the complete combined
low-floor rule; the only split tags are the seven coordinate indices.

The depth-first traversal checks that every event has a pending cell,
pushes both exact children of every split, and demands an empty frontier
at completion. Recomputed node, leaf, full-binary-tree, and maximum-depth
counts must match the declared counts. The benchmark-only early return
prints a different explicit incomplete status; it cannot print the final
exact-replay success record.

In a fresh independent Python structural pass, every one of the 5,642,527
events satisfied these split/leaf and frontier conditions. The pass
recomputed 2,821,264 leaves and depth 52. It also decompressed the archived
certificate and compared the resulting bytes directly with the raw
certificate, then recomputed all stated hashes. Its saved report makes
clear that this was structural verification rather than another full
arithmetic replay.

## 4. Physical frame, corner, and pair formulas

The C++ `shape` function matches the Python endpoint envelopes: folded
a,k decrease, while b,h increase. Both retain the actual common frame
in the inset halfwidth `1/(4h)`.

`corner_upper` uses all four original signed-chirality corners, with the
correct left reflection applied by its caller. Its minimum with the
universal center ceiling only strengthens a necessary upper height bound.
An impossible corner is excluded only when the entire radical interval
is negative.

The main-clearance and endpoint-clearance formulas match the reference.
The latter retains the opposite vertical branch unless the strict
`base+opposite_reach>0` test excludes it. A box crossing a horizontal
overlap or vertical-branch boundary keeps the weaker bound. No unknown
separator sign is silently fixed.

The physical support sum is reconstructed as one half of one plus the
absolute cosine and sine of the same two original frames. Its lower bound
is capped below by one. Both owned side axes of both original squares
are retained. The four positive-horizontal normals are the same complete
cone-direction union as in the hand proof and Python reference.

The original P frame is shared between its left and right pair tests.
The fixed-sign loops maximize over both P signs, both R signs within
that P chart, and both L signs within that same P/R chart. No independent
replacement P or main frame is introduced.

## 5. Endpoint resources and the exact main support

The effective shoulder width uses the two accepted universal physical
pair tolls. Its interval upper bound is the smaller of the curved
right-endpoint upper and the linear endpoint/critical-point upper. The
critical-point inclusion test is rounded outward, so it may include an
extra case but cannot omit the genuine maximum at t=19/27.

The individual and summed main-tilt caps, the opposite adaptive loads,
the left endpoint load ceiling, the affine endpoint resource, and the
circular endpoint resource all match the frozen reference with the
correct signs. A larger shoulder effective-width upper weakens each
resource in the required direction. The lower main-tilt estimate is
computed before its positive quadratic remainder is fed back into the
main inset margins; there is no circular assumption.

The bad-floor cancellation uses 11/25, correctly corresponding to the
stronger main height -17/50. Both signed P cases and the resulting xP
lower bounds match their original owned-axis inequalities. The zero-tilt
collar is supplied separately by the hand proof, so every actual P in
the certificate root has tP>=1/27 and the required positive denominators.

The exact main support lower bound

\[
 \max\{1,\ 1/2+b_F H+a_F\sqrt{1/2-H^2}\}
\]

is evaluated at the permitted main halfwidth upper H and at the outsider
tangent lower endpoint. Its derivative in H is nonpositive, and its
derivative in the outsider folded angle is nonnegative on the root.
If the folded frame intervals overlap, the cap by one remains a safe
lower bound. Both original chirality relations are therefore covered.
The smaller horizontal-gap bounds and the same main tilt are used for
both P and L, as required.

## 6. Joint owner inequalities

Every one of the sixteen left/right owner pairs is included. The ordinary
two pair tests use the correct signed vertical-gap intervals. For equal
vertical signs, both the original and expanded versions of the weighted
yP cancellation have matching coefficients and correct endpoint choices.

The discrete shortcut `ia==ib+2 && ib<2` recognizes precisely the same
P-owned axis chosen on both links. It adds the two original inequalities
and cancels both coordinates of P; it does not infer axis identity from
approximate numerical equality.

The additional xP cancellation is exactly

\[
 ac(Z+X)+(cb-ad)y_P-cbY_L^*+adY_R^*
             -c\sigma_{LP}-a\sigma_{PR}\ge0.
\]

It is c times the LP inequality plus a times the PR inequality, with
nonnegative multipliers. The choices `YL*=Llo` for positive b and `Lhi`
otherwise, and `YR*=Rhi` for positive d and `Rlo` otherwise, give the
necessary upper relaxation. The possibly signed P coefficient is evaluated
against the full one P-height interval. Zero components remain covered.

Taking the minimum of necessary margins inside one owner choice and then
the maximum over all choices has the correct logical direction.

## 7. Every contractor preserves physical coverage

The three initial intersection sweeps use only the proved xP cut,
the coupled-floor cut, both lower inset-cone gaps, both closed weak-link
upper gaps, and the original physical pair-cap resources. Each endpoint
is rounded outward using the current necessary intervals. Sequential
intersection cannot discard an original physical point. A strict empty
interval is the only contraction-based rejection; touching endpoints
are retained.

The signed P x-contraction is performed inside its actual P/R chart and
retains the same main tilt and endpoint resources. The subsequent physical
gap contraction takes a lower bound for each of the four possible owned
normal gaps, then their minimum. Thus it covers the complete owner union,
rather than intersecting incompatible owner choices.

After all chirality charts are considered, the code takes the union hull
of the contracted xP intervals for all charts whose necessary margins
remain nonnegative. Every physical original point belongs to one such
chart and remains in this hull. Re-evaluating the full formula on that
hull is valid. The recursion permits only three repetitions after the
first evaluation; no convergence or fixed-point assertion is used.

## 8. Intentional C++ differences from Python are safe

The following differences are mathematical strengthenings or earlier
checks of necessary inequalities, not formula mismatches.

* A negative main-tilt upper bound is rejected immediately, including the
  small negative range for which Python postpones rejection and clamps
  an auxiliary evaluation to zero. The actual tilt is nonnegative.
* `allowed_g<down(15/31)` is rejected before taking its reciprocal. An
  original main inset is strictly wider than 15/31, so such a branch is
  impossible.
* A lower tilt bound strictly above either the current upper cap or
  1/60 is rejected before later resource arithmetic.
* A strictly negative upper corner-resource radical or a right symmetric
  inset lower bound strictly above 1/2 is rejected directly. Python
  carries an impossible sentinel forward to the same necessary bound.
* The high-right reach is computed only when its horizontal-overlap
  predicate holds. Outside that branch the reference computes but does
  not consume it.
* A nonpositive relaxed numerator in `physical_gap_lower` contributes
  the valid bound zero in C++, in place of a potentially negative Python
  quotient. Actual cone gaps are nonnegative. A zero-horizontal normal
  is retained whenever its vertical alternative can remain viable.

The positive quotient cap of 1,000 only rounds a lower bound downward.
All required physical gaps are bounded far below 1,000, so the absent-axis
sentinel cannot conceal a feasible owner. The negative sentinel is not
asserted to enclose an arbitrary unrestricted quotient: the only relevant
endpoint use occurs after proved horizontal overlap, where the actual
signed reach is at least -k>=-1/2. Main reach numerators are positive on
their roots. The P reciprocal denominator is bounded away from zero by
the hand collar. These physical facts justify every sentinel use.

## 9. Independent audit of the -17/50 lower-side gate

The supporting manuscript
`../agent_roots/LOWER_SIDE_MAIN_SEVENTEEN_FIFTIETHS_HAND_TABLE.md` was also
reviewed independently. Its SHA256 is
`478e97d5e5f58d901e26c6707aaa8c4c6d857e01c4ee83a4e1f7c8e48f689bc6`.

The actual four-chain and universal original center bound give the
correlated main band
`-31/60+e < x1 < -29/60-e`, with `0<=e<1/60`. After reflection, its
maximum possible horizontal gap from the original lower side unit is
the displayed maximum of the two band-end distances. No main position
or chirality is reset. The cut tM<17/500 follows from the exact positive
halfwidth comparison.

Both side chiralities contribute their actual four corner ceilings. Their
maximum is an outward relaxation. The relative-frame support lower bound
uses the closest folded angles, because cosine plus sine increases with
the unsigned difference on the relevant interval. Opposite chiralities
cannot lower it: the displayed difference is
`2(min(aM*b,bM*a)-bM*b)>=0`. Both original owners and both axes of each
owner remain in the four projection inequalities. Thus every strict leaf
excludes its complete physical subdomain, including contact limits.

A fresh run of `verify_lower_side_main_17_50.py` passed all 147 nodes and
74 strict leaves, depth 15. Its report, with exact row data, is
`lower_side_main_17_50_independent_replay.json`. A separate transcription
check matched all 74 printed boxes and proved that every printed reserve
is no larger than its freshly recomputed exact reserve; its report is
`lower_side_main_17_50_printed_table_audit.json`. Consequently the lower
side original supplies the required strict main-height improvement.

## 10. Acceptance and scope

The mathematical evaluator, its implementation differences, and its finite
coverage mechanism pass this independent review. Together with the full
separate C++ replay, the completed certificate proves the stated low-floor
exclusion on its entire root, with the separate low-right theorem and the
proved original lower-side main-height input as explicit dependencies.

The final original-nine occupancy selection and whole-mask assembly remain
the parent proof's responsibility. This review neither changes the fixed
frontier nor claims unrestricted nine-square closure on its own.
