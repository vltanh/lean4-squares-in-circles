# Independent review of the wide-main eight-original exact C++ replay

November 2, 2026. Reviewer: the `whole_mask` agent, separately from the
Python evaluator author and the C++ port author. This is an agent code and
mathematical review, not a human review or a proof-assistant claim. No Lean
or CI was used.

## 1. Frozen inputs and outcome

The final C++ source is
`agent_roots/weak_outer_00/weak_middle_eight_replay/verify_weak_middle_side_eight_exact.cpp`,
SHA-256
`2e8164fc162336b70334195643460009c359c46922c60733cf2fbdcaf6cbd031`.

It was compared against the frozen Python mathematical evaluator
`agent_low_floor/weak_middle_11/verify_weak_middle_side_eight.py`, SHA-256
`c1fad9ffb92596f67ff1b306230da124b61ad6151e419fc47832685455ea714c`.
The independent physical derivation review is
`WEAK_MIDDLE_BRACKETED_SIDE_TRIPLE_INDEPENDENT_REVIEW.md` in this directory.

**Result: PASS.** The complete necessary-feasibility formulas, all signed
charts and original-owner alternatives, directed integer interval
operations, literal rational root, and complete certificate traversal
were independently checked. No formula or coverage discrepancy was found.

The C++ author separately replayed the low-right certificate with SHA-256
`89033c7e5fd8caaca5b4c7fcee5309be0e2791f718e8cc99ecadaddf50d78303`.
That replay passed all 297,270 strict leaves, 594,539 nodes, and depth 32;
its minimum directed reserve was

\[
                  1559179356/281474976710656>0.
\]

The final comment-only correction described in Section 4 was recompiled
to the identical executable, SHA-256
`571e3b9a132041a320c437c3578e6e1ecc3a1e5dd017d7d3b366ea05e026b8af`.
Thus the completed replay applies to the final source. These arithmetic
results and four rejected damaged controls are recorded separately in
`weak_middle_side_eight_low_right_cpp_replay.json` and
`weak_middle_side_eight_low_right_cpp_negative_controls.json` beside the
C++ source. This review does not claim a second execution of the full
297,270-leaf replay by the reviewer.

## 2. Integer arithmetic and literal root

The kernel uses signed integers scaled by \(2^{48}\), with signed
128-bit intermediates for products and division numerators. The checked
floor and ceiling divisions have the correct signs for negative
numerators. Multiplication takes all four endpoint products. Division
uses a strictly positive denominator interval and both endpoint
directions. Negation, absolute value, maxima, minima, intersection, and
square operations preserve outward inclusion. Narrowing to the stored
integer type is checked rather than silently overflowing.

The integer Newton square root starts above the root, terminates by exact
integer comparisons, and verifies its final floor inequalities. The
interval square root floors its lower endpoint and ceilings its upper
endpoint. Clipping a negative lower endpoint to zero is used only after
the upper endpoint is known nonnegative; an entirely negative necessary
radicand excludes the box.

The coordinate root is reconstructed from the literal triples

\[
\begin{aligned}
 L&=(0,0,0,29,-23,29,4421,10,10),\\
 R&=(1,1,1,65,23,65,6000,13,13),\\
 D&=(1,1,1,60,60,60,12000,20,20).
\end{aligned}
\]

Coordinate \(i\) therefore starts at \([L_i/D_i,R_i/D_i]\).
Each split is represented by its exact dyadic cell index and depth,
before a separate outward conversion to the fixed-point evaluator. The
midpoints are not reconstructed from rounded parent endpoints. The depth
bound of 60 and the literal coordinate numerators leave the conversions
inside the checked 128-bit range. Interval values in this evaluator and
its saturation constants remain inside the stored signed range.

## 3. Mathematical formula parity

The C++ expressions were checked against every corresponding Python
expression. In particular, the port preserves:

- the independent original halfwidths \(h_B,h_C\), their aligned inset
  widths, the original folded frame parameters, and the orientation
  budget \(\eta_B+\eta_C\);
- both accepted shoulder orientation tolls through the effective width
  function, all individual and summed endpoint resources, and the
  endpoint rectangle halfheights;
- the bracketed-main height function, its piecewise bump, the opposite
  endpoint inversions, and the original main position bands;
- the disk lower bound and all signed upward original-square owners in
  each main-to-outsider clearance;
- both chiralities of each endpoint-to-shoulder clearance and all four
  original corner bounds;
- all 32 choices of the original B, C, L, P, R chiralities;
- all four physical owner choices for each of L/P and P/R, with all 16
  combinations intersecting the height interval of the same original P;
- both resulting original-main height bounds and the complete original
  B/C owner union, preserving those same main chiralities and heights.

The interval implementation of \(\eta(h)\) and the bracketed-height bump
can be slightly wider than the Python point arithmetic. Each difference
weakens a necessary bound and is therefore safe; it cannot create a
false exclusion. Every chart is discarded only after one of its necessary
conditions is strictly impossible. The maximum over the surviving chart
and owner alternatives remains an upper bound for the full physical
union. A surviving physical configuration would make every margin of at
least one alternative nonnegative.

The two modes retain their separate complementary hypotheses. The
low-right mode assumes only the stated low right shoulder height; the
low-floor mode assumes only the stated low P floor. The completed
low-right arithmetic replay establishes no low-floor consequence by
itself.

## 4. Saturated quotients and the corrected endpoint comment

`div_lower` uses saturation constants \(\pm1000\). This helper is used
for necessary physical lower bounds, not as a claim that the returned
value always encloses an unrestricted real quotient.

Positive saturation is downward and hence preserves a lower bound.
Negative saturation in original-main clearance is harmless because the
result is maximized with a nonnegative original-disk clearance. In the
physical cone-pair height ranges, the range is also intersected with the
cone interval \([-d,d]\), where the admitted \(d\) is below 3/2, so a
negative saturation cannot remove a physical height difference. Zero
owner components retain the viable alternative when its numerator is
nonpositive, and discard it when it is positive, exactly as in the
Python necessary-feasibility calculation.

The endpoint term requires its own bound. Let \(a\ge b\ge0\),
\(h=(a+b)/2\), \(k=(a-b)/2\), and let \(\delta>-h\) be the strictly
overlapping horizontal inset margin. Then

\[
 \frac{1/2+\delta b}{a}>k\ge0,
 \qquad
 \frac{1/2+\delta a}{b}>-k\ge-1/2\quad(b>0).
\]

The second numerator need not be positive. Its physical lower bound
above \(-1/2\) makes the negative saturation harmless. At \(b=0\)
the zero-component branch retains or omits the axis according to its
necessary numerator test. The earlier C++ comment saying that both
endpoint numerators were positive was corrected to these inequalities.
No arithmetic expression changed, and the recompiled binary is identical.

## 5. Complete certificate traversal and rejection conditions

The parser rejects unknown and duplicate keys, malformed integers,
missing fields, and any nonempty claimed frontier. Only the two named
modes and the complete status are accepted. Producer timing and floating
reserves are syntactically read but are never used to certify a leaf.

Tags 0 through 8 split the indicated exact root coordinate; tag 9 is the
only terminal. The stack keeps every child, including both closed halves
of each split. A terminal is accepted only after the exact directed
evaluator returns a strictly negative upper bound. The traversal rejects
trailing events, unfinished trees, excessive depth, and mismatched
computed node, leaf, and depth counts. It also checks the full binary-tree
identity \(N=2L-1\). The optional benchmark limit emits the explicitly
incomplete status `BENCHMARK_ONLY_INCOMPLETE`, never a successful proof
status.

The resulting check covers the entire closed literal root, all original
frames and owners admitted by the reduction, and all split boundaries.
Together with the separately completed exact low-right replay and the
physical review, it supports the low-right eight-original theorem on its
stated complete scope. A complete low-floor replay remains a distinct
acceptance requirement.
