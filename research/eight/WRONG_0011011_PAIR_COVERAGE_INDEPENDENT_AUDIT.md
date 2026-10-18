# Independent finite coverage audit for the word 0011011

**Result: the exact case count, reflection, role-label identities, and
manuscript cover pass.** There are 76 directed pair cases and 39
reflection representatives: 10 core/core, 19 mixed, and 10 outer/outer.
The 39 representatives below have a manuscript assigned to every case.

This audit checks the finite assembly. It does not replace the continuous
proof or the independent mathematical review of a component manuscript.
In particular, its `PASS_FINITE_COVERAGE` output must not be read as an
automatic proof of any pair inequality. The companion
`audit_wrong_0011011_pair_coverage.py` binds all cited principal manuscripts,
the three explicit geometric imports, and the exact role-label data by
SHA-256. Its complete output is
`wrong_0011011_pair_coverage_audit.json`.

All indices are taken modulo seven. All decimals below are exact rationals.

## 1. Geometric premises and signs

Use the already proved exterior-boundary reduction, the center-ray gap
bound `delta_i > .76`, and a common lifted square-frame interval of length
less than `.7`. The quarter word is

\[
 (k_0,\ldots,k_6)=(0,0,1,1,0,1,1).
\]

Write its frame lifts as `beta_i`, and put

\[
 \phi_i=k_i\pi/2+\beta_{i+1}-\beta_i,
 \qquad
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1},
 \qquad -\pi/4\le\alpha_i\le\pi/4.
 \tag{1}
\]

The signs of the local angles are denoted by `sigma_i`. At a zero local
angle, choose either signed representation once for that vertex and use
it consistently in both incident costs. Every cited proof covers the
closed endpoint `b=0`. The argument does not require the two signed
polynomials to agree there.

The two consecutive zero edges give

\[
 \alpha_0-\alpha_2
 =\delta_0+\delta_1-(\beta_2-\beta_0)
 >1.52-.7=.82>\pi/4.
 \tag{2}
\]

Consequently `alpha_0>0` and `alpha_2<0`: if either failed, their
difference would be at most `pi/4`. A zero edge cannot have sign pair
`(-,+)`, since then (1) would give `delta_i <= phi_i < .7`, contradicting
`delta_i>.76`. These restrictions leave exactly the following local
edge/sign classes:

| Edge | Quarter increment | Sign pairs |
|---:|---:|---|
| 0 | 0 | `++`, `+-` |
| 1 | 0 | `+-`, `--` |
| 2 | 1 | `--`, `-+` |
| 3 | 1 | `++`, `+-`, `-+`, `--` |
| 4 | 0 | `++`, `+-`, `--` |
| 5 | 1 | `++`, `+-`, `-+`, `--` |
| 6 | 1 | `++`, `-+` |

Their number is `2+2+2+4+3+4+2=19`. There are 24 full assignments of
seven signs satisfying these necessary restrictions, and each class in
the table occurs in at least one such assignment. This last observation
only checks the local list; physical realization of every assignment is
unnecessary. An over-cover by these 19 classes is sufficient.

Each edge/sign class has the four ordered radial kinds `CC`, `CO`, `OC`,
and `OO`. Thus there are `19*4=76` directed pair cases. A core state includes
both its straight side and its corner arc. It is not counted as two
different radial kinds.

## 2. Exact reflection and its fixed cases

The coefficient file `proof_integration/wrong_0011011_labels.json` gives
the unsigned polynomials `L_i^sigma(a,b)` and the identity

\[
 L_{2-i}^{\sigma}=L_i^{-\sigma}.
 \tag{3}
\]

The companion expands all seven roles from the four independent roles
and verifies (3), coefficient by coefficient, for both kinds and signs.
It also verifies that `k_i=k_(1-i)`.

Reflecting the plane and reversing the cyclic order sends a pair to

\[
 (i,\sigma,\tau,K_s,K_t)
 \longmapsto
 (1-i,-\tau,-\sigma,K_t,K_s).
 \tag{4}
\]

Its frame angle is still `phi_i`. Its corrected cost is unchanged:

\[
 \begin{aligned}
 \phi_i+(-\tau)L_{1-i}^{-\tau}
              -(-\sigma)L_{2-i}^{-\sigma}
 &=\phi_i-\tau L_{i+1}^{\tau}+\sigma L_i^{\sigma}.
 \end{aligned}
 \tag{5}
\]

This verifies the reflection for the actual role polynomials; no
interchangeability of arbitrary source and target labels is assumed.

The only fixed directed pair cases of (4) are

\[
 (4,+,-,C,C),\qquad(4,+,-,O,O).
\]

Indeed a fixed edge must satisfy `i=1-i`, so `i=4`; a fixed sign pair must
be opposite, and the only allowed one there is `(+,-)`; finally the kinds
must coincide. Hence the number of pair orbits is

\[
 \frac{76+2}{2}=39.
\]

There are 10 `CC` orbits, 10 `OO` orbits, and 19 mixed orbits. In the
mixed class the 38 directed cases have no fixed point.

For clarity, the four retained signed axes, in order, are source `+f`,
target `+e`, target `+f`, and source `-e`. Under (4) they are permuted by
`(1 3)(2 4)`, as follows directly from the four projection formulas.
Thus the 304 directed kind/sign/axis cases have 152 reflection orbits.
Giving all four axes for each of 39 pair representatives supplies four
harmless duplicate axis claims in the two fixed pair cases. The pair
count 39 must not be confused with a count of axis orbits.

## 3. Complete principal-manuscript map

The following table lists all ten canonical edge/sign choices.
`CC` always refers to
`proof_integration/WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md`.
The mixed and outer names are expanded immediately below. The second
radial order in edge `4,+-` is the reflection of the first and is counted
only once.

| Edge | Signs | `CC` | `CO` | `OC` | `OO` |
|---:|:---:|---|---|---|---|
| 0 | `++` | all-core | mixed-zero-same | mixed-zero-same | outer-zero-same |
| 0 | `+-` | all-core | mixed-zero-opposite | mixed-zero-opposite | outer-zero-asymmetric |
| 2 | `--` | all-core | e2-negative-core | e2-negative-core-side + corner | outer-e2-negative |
| 2 | `-+` | all-core | e2-core-positive-outer | e2-outer-positive-core | outer-e2-opposite |
| 3 | `++` | all-core | e3-positive-core-positive-outer | e3-four-mixed | outer-e3-positive |
| 3 | `+-` | all-core | e3-four-mixed | e3-four-mixed | outer-e3-positive-negative |
| 3 | `-+` | all-core | e3-negative-core-positive-outer | e3-outer-positive-core | outer-e3-opposite-axes12 + axes34 |
| 3 | `--` | all-core | e3-four-mixed | e3-outer-negative-core | outer-e3-negative |
| 4 | `++` | all-core | mixed-zero-same | mixed-zero-same | outer-zero-same |
| 4 | `+-` | all-core | mixed-zero-opposite | reflection of `CO` | outer-zero-symmetric |

The following files are under `proof_integration/`; all names have the
prefix `WRONG_0011011_` and suffix `_HAND_PROOF.md`:

| Table name | Manuscript stem |
|---|---|
| mixed-zero-same | `SAME_SIGN_MIXED_ZERO` |
| mixed-zero-opposite | `OPPOSITE_MIXED_ZERO` |
| outer-zero-same | `SAME_OUTER_ZERO` |
| outer-zero-asymmetric | `ASYMMETRIC_OPPOSITE_OUTER_ZERO` |
| outer-zero-symmetric | `SYMMETRIC_OUTER_WHOLE_ANGLE` |
| outer-e2-negative | `NEGATIVE_OUTER_QUARTER` |
| outer-e2-opposite | `OPPOSITE_OUTER_EDGE2_QUARTER` |
| outer-e3-positive-negative | `POSITIVE_NEGATIVE_OUTER_QUARTER` |
| outer-e3-opposite-axes12 | `EDGE3_OPPOSITE_AXES12` |
| outer-e3-opposite-axes34 | `EDGE3_OPPOSITE_AXES34` |
| outer-e3-negative | `EDGE3_NEGATIVE_OUTER_QUARTER` |

The remaining files are under `m5_agent/hand_conversion/`, with the same
prefix and suffix:

| Table name | Manuscript stem |
|---|---|
| e2-negative-core | `EDGE2_NEGATIVE_CORE_TO_OUTER` |
| e2-negative-core-side | `EDGE2_NEGATIVE_CORE_SIDE` |
| e2-negative-core-corner | `EDGE2_NEGATIVE_CORE_CORNER` |
| e2-core-positive-outer | `EDGE2_CORE_TO_POSITIVE_OUTER` |
| e2-outer-positive-core | `EDGE2_OUTER_TO_POSITIVE_CORE` |
| e3-four-mixed | `EDGE3_FOUR_WHOLE_MIXED_FAMILIES` |
| e3-positive-core-positive-outer | `EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER` |
| e3-negative-core-positive-outer | `EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER` |
| e3-outer-positive-core | `EDGE3_OUTER_TO_POSITIVE_CORE` |
| e3-outer-negative-core | `EDGE3_OUTER_TO_NEGATIVE_CORE` |
| outer-e3-positive | `EDGE3_POSITIVE_OUTER_PAIR` |

There are two principal split covers. For `e2-negative-core-side + corner`,
the closed intervals `0<=B<=1/2` and `1/2<=B<=d_c` cover the entire core
curve, including their common endpoint. For the two opposite outer edge-3
notes, the axis sets `{1,2}` and `{3,4}` cover the complete retained-axis
list over the whole frame interval.

The aligned mixed-quarter lemma and the edge-2 contact-strip lemma are
imports for some principal mixed proofs, not replacements for the rest
of the quarter interval. The symmetric aligned outer lemma is likewise
an import of the whole-angle symmetric note. The companion binds these
three additional manuscripts explicitly. Their coverage is never
mistaken for a whole pair theorem.

## 4. Conditional cyclic conclusion

Suppose every principal entry above has its asserted bound

\[
 C_i=\phi_i+\sigma_iL_i^{\sigma_i}
                    -\sigma_{i+1}L_{i+1}^{\sigma_{i+1}}
 >\gamma=\frac{17953}{20000}.
\]

Choose the kind and signed representative of each vertex once. The
labels then telescope exactly, independently of their discontinuities
between signed or radial pieces. Formula (1) and the four quarter-one
increments give

\[
 \sum_{i=0}^{6} C_i=\sum_{i=0}^{6}\phi_i=2\pi.
\]

But the exact rational comparison is

\[
 7\gamma=\frac{125671}{20000},\qquad
 7\gamma-\frac{710}{113}=\frac{823}{2260000}>0,
 \qquad 2\pi<\frac{710}{113}.
\]

Thus all listed pair theorems together exclude the word `0011011` at
`Q=9789/2500` under the stated analytic boundary, gap, and frame premises.
The role coefficient file's historical candidate-status string is kept
unchanged for provenance; its exact coefficients are what this audit
binds. This conclusion does not assert the separate candidate-word
capture or the complete packing/equality theorem.
