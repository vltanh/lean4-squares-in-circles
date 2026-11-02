# Fast independent exact replay for the wide-main side-triple certificate

November 2, 2026. No Lean or CI. The implementation is a separate C++
reconstruction of the frozen exact Python evaluator; the floating producer
was not read or imported for the port.

## Complete low-right result

`verify_weak_middle_side_eight_exact.cpp` independently replayed the entire
original low-right certificate:

| Item | Exact result |
|---|---:|
| Nodes | 594,539 |
| Strict leaves | 297,270 |
| Maximum depth | 32 |
| Unresolved frontier | 0 |
| Least reserve | \(1559179356/281474976710656>0\) |
| Measured arithmetic execution | 88,528 ms |

The source certificate is
`weak_middle_side_eight_low_right_candidate.json`, SHA256
`89033c7e5fd8caaca5b4c7fcee5309be0e2791f718e8cc99ecadaddf50d78303`.
The frozen reference evaluator is `verify_weak_middle_side_eight.py`,
SHA256
`c1fad9ffb92596f67ff1b306230da124b61ad6151e419fc47832685455ea714c`.

The accepted mathematical scope is the original outer-actual main chain,
both-weak side-endpoint cone triple, and the original lower left-side
helper. It is an eight-original consequence within the retained nine-unit
packing. This arithmetic result is not by itself a complete `010/11`
mask assembly.

## Independent arithmetic and coverage

The C++ source uses the previously independently reviewed 48-bit directed
dyadic kernel, with checked signed 128-bit intermediate multiplication,
correct signed floor/ceiling division, and integer square roots whose
enclosure postcondition is checked. No floating arithmetic, tolerance,
optimizer result, or producer-supplied bound is used for acceptance.

Every scalar function, all five frame-sign choices, the sixteen original
short-triple owner combinations, common main height variables, and the
retained B--C physical pair are reconstructed directly from the exact
Python evaluator. The variable root is

\[
 [0,1]^3\times[29/60,13/12]\times[-23/60,23/60]
 \times[29/60,13/12]\times[4421/12000,1/2]\times[1/2,13/20]^2.
\]

Cell boundaries are stored as exact root-relative dyadic index/level
pairs, with the original rational root denominator in each coordinate.
Rounded arithmetic enclosures never define the covering partition.
Every split reconstructs both children, all leaf rules are independently
recomputed, and final tree/node/leaf/depth counts must agree exactly.

The strict parser rejects duplicate or unknown fields, invalid JSON
numbers, unknown split/leaf tags, wrong root families, nonempty discovery
frontiers, inconsistent counts, missing children, and trailing data.
Discovery timing and floating reserve metadata are syntax-checked and
otherwise ignored; they are never converted to floating point.

## Small implementation differences and their physical bounds

The reference uses 80-bit dyadic arithmetic. The port uses 48 bits with
the same outward directions. Its eta and piecewise main-height endpoint
values are evaluated by directed intervals at exact represented endpoints;
the accepted monotonicity gives the required lower bounds.

Quotients saturate at +/-1000 to avoid irrelevant integer overflows.
This does not strengthen any physical exclusion. For main clearance,
an excessively negative lower bound is dominated by the nonnegative
center-distance lower bound. In cone-pair range contraction, the result
is intersected with +/-d, whose magnitude is below two. For endpoint
reach, the horizontal-overlap premise gives

\[
 r_- > -k\ge-1/2\quad(b>0),\qquad r_+\ge k\ge0.
\]

The zero-b owner is omitted. Positive saturation still exceeds every
possible physical height or height difference in the Q-disk. These facts
justify both saturation signs on every call site.

## Reproducibility and independent review

The standalone source needs only a C++17 compiler and its standard
library. Build with the compiler command recorded in the replay report.
`run_weak_middle_side_eight_exact_replay.py` runs the executable, archives
the complete result and hashes, and checks four damaged controls.

All four controls were rejected: wrong root family, unknown split/leaf
rule, missing child and an invalid whole-root single leaf. The last one
reached the exact mathematical evaluator and failed with a nonnegative
root margin.

The original full replay used the source before an explanatory
endpoint-sign comment was corrected. Recompiling the comment-corrected
source produced an **identical executable byte for byte**, so the complete
arithmetic execution and controls apply to the final source. Both source
hashes and executable identity are recorded in the reports.

Final source SHA256:
`2e8164fc162336b70334195643460009c359c46922c60733cf2fbdcaf6cbd031`.
Executed and recompiled executable SHA256:
`571e3b9a132041a320c437c3578e6e1ecc3a1e5dd017d7d3b366ea05e026b8af`.

The independent `/root/whole_mask` agent reviewed the mathematical
formula parity, kernel, root-cell representation, and parser. That code
audit is separate from the full arithmetic replay reported here. Neither
is represented as a human review or a proof-assistant verification.

The same source implements the frozen reference's `low_floor` branch,
but that branch is not declared accepted until its own complete
certificate independently passes this checker.
