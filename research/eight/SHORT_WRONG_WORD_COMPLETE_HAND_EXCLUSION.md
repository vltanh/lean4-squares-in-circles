# Complete hand exclusion of the quarter word 0010111

## Theorem

There is no cyclic sequence of seven core/outer boundary square states at
`Q=9789/2500` with true separating-axis feasibility on every consecutive
pair, physical center holonomy `2pi`, center gaps greater than `.76`, a
common lifted frame interval of length less than `.7`, and quarter word

\[
 (k_0,\ldots,k_6)=(0,0,1,0,1,1,1).
\tag{1}
\]

The theorem covers all `2^7` radial words at once. It does not assume
disjointness of nonconsecutive states. Thus it applies directly to the
adjacent-pair relaxation supplied by radial boundary reduction.

This is a hand exclusion. Its continuous steps are the contact,
monotonicity, curvature and circular-support lemmas in the component
notes. Its arithmetic consists of explicit fixed rational comparisons
and nonnegative coefficients of specified one-variable polynomials.
No adaptive state-domain tree, sampled minimum, numerical optimizer,
missing-contact assumption, or external interval manifest is a premise.

## 1. The two signs forced by the zero chain

Write `alpha_i` for a state's signed center/frame angle, in
`[-pi/4,pi/4]`, and `phi_i` for its lifted frame increment including the
quarter turn. The center gap is

\[
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1}.
\tag{2}
\]

The two consecutive zero edges give

\[
 \alpha_0-\alpha_2
 =\delta_0+\delta_1-(\phi_0+\phi_1)>1.52-.7=.82.
\tag{3}
\]

Here `phi0+phi1` is the difference of two values in the common frame
interval, so it is less than `.7`. Since `pi/4<.8`, (3) forces
`alpha0>0` and `alpha2<0`. Every other state may have either sign.
Moreover a zero edge cannot have a negative source and positive target:
then (2) would give `delta<=phi<.7`, contrary to `delta>.76`.

At a zero signed tangent, either sign convention can be chosen, but it
must be chosen once per state and used on both incident edges. Both
closed sign domains are covered by the component inequalities.

## 2. The role labels and the strict cyclic reserve

For each signed core or outer state use the exact role label

\[
 \ell_i(a,\sigma b)=c_i^\sigma+p_i^\sigma a+
                  \sigma q_i^\sigma b,
\tag{4}
\]

whose integer coefficients, with denominator100000, are in
`short_hand_labels.json`. The pair cost is

\[
 C_i=\phi_i+\ell_i-\ell_{i+1}.
\tag{5}
\]

The completed components prove

\[
 C_2>\frac{359}{400}=.8975,\qquad
 C_i>\frac{17953}{20000}=.89765\quad(i\ne2).
\tag{6}
\]

The slightly weaker edge2 constant is intentional. It avoids an
unnecessary clipping argument for two outer/outer quarter contacts and
retains the exact positive reserve

\[
 \sum_i C_i>
 6\frac{17953}{20000}+\frac{359}{400}
 =\frac{31417}{5000}
 =\frac{710}{113}+\frac{121}{565000}
 >2\pi.
\tag{7}
\]

The final comparison follows from the elementary rational Machin-series
upper bound `2pi<710/113`, also checked by the assembly script.

On the other hand the role labels telescope, so

\[
 \sum_iC_i=\sum_i\phi_i=\sum_i\delta_i=2\pi.
\tag{8}
\]

Equations (7) and (8) contradict one another. It remains only to record
the exhaustive mathematical coverage of (6).

## 3. Complete component ledger

The exterior cap and forward-gap lemmas leave axes1,2,3,4. Each actual
adjacent pair has at least one of these separating axes. The components
below cover every retained axis, and include endpoints and axis ties.

| Radial kinds and quarter | Complete hand component | Scope |
|---|---|---|
| C/C, both quarters | `SHORT_WRONG_WORD_ALL_CORE_CORE_HAND_PROOF.md` | All19 allowed signed role entries, with full SAT feasibility |
| C/O or O/C, zero | `SHORT_WRONG_WORD_ALL_MIXED_ZERO_HAND_PROOF.md` and its cited mixed-zero family lemma | All56 retained-axis branches |
| C/O or O/C, one | `SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md` | All96 retained-axis branches |
| O/O, zero primary and unfavorable same-sign secondary | `SHORT_WRONG_WORD_OUTER_ZERO_PRIMARY_HAND_PROOF.md` | 18 branches |
| O/O, zero opposite secondary | `SHORT_WRONG_WORD_OUTER_ZERO_OPPOSITE_HAND_PROOF.md` | 6 branches |
| O/O, zero favorable same-sign secondary | `SHORT_WRONG_WORD_OUTER_ZERO_SAME_HAND_PROOF.md` | 4 branches |
| O/O, one, six contact neighborhoods | `SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md` | Six full neighborhoods of pi/2 |
| O/O, one, complementary angles and every other case | `SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF.md` | 140 fixed scalar regimes completing all48 branches |

The C/C theorem's19 entries comprise7 zero-quarter and12 one-quarter
signed cases; each theorem is independent of which SAT axis separates.
The mixed and outer components explicitly enumerate the retained axes.
Thus the ledger covers all76 C/C axis cases, all152 mixed axis cases,
and all76 O/O axis cases, or all304 possibilities allowed by Section1.

The component notes generally prove the stronger bound `.898`; any such
bound implies (6). The six near-aligned neighborhoods prove `.89765`.
Only the scalar table uses the relaxed edge2 bound `.8975`.

## 4. Exact angle cover on the final outer cases

There are8 original O/O quarter-one cases on edge2,16 on edge4,16 on
edge5, and8 on edge6. Each consists of its two permitted signs and one
of the four retained axes. Write `phi=pi/2+r u`, `r in{-1,1}`.

For the following six original cases, the near-aligned proof provides
the initial interval in `u`:

| Original edge, signs, axis | Normalized source axis | Negative side covered by contact proof | Positive side covered by contact proof |
|---|---|---|---|
| 2, --,3 | +f | [0,.3] | [0,.1] |
| 2, --,4 | -e | [0,.03] | [0,.06] |
| 4, --,3 | +f | [0,.3] | [0,.1] |
| 4, --,4 | -e | [0,.03] | [0,.06] |
| 6, ++,1 | +f | [0,.3] | [0,.1] |
| 6, ++,2 | -e | [0,.03] | [0,.06] |

Every table chain begins exactly at the corresponding endpoint above,
or at0 for the other42 cases. Consecutive scalar intervals share their
exact rational endpoint, and every chain ends at `.7`. Thus the scalar
table and contact neighborhoods cover the closed interval on both sides
of pi/2 for all48 cases. The arithmetic/union audit enumerates those96
signed angle chains explicitly; none is accepted merely by a plot or
sampled domain test.

## 5. Verification and dependencies

`audit_short_whole_word_hand.py` verifies the exact304-case count, the
48-case outer quarter-one domain union, the literal table/record binding,
all scalar coefficient signs, the cyclic rational reserve, and the
completed arithmetic status of every component. Its report is
`short_whole_word_hand_assembly_audit.json`; it also records SHA256
bindings for the sources, rational table, labels, and arithmetic records.

This assembly depends on the hand central-core, radial-boundary,
common-point/axis and frame-concentration theorems only for their stated
geometric interfaces. It does not depend on the older computational
three-core, short-two-core,123-case capture, or endpoint-owner manifests.
Its conclusion is the full exclusion of (1), rather than a restriction
to a newly isolated continuous remainder.
