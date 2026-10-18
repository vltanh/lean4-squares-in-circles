# A complete hand exclusion of the word 0011011

## Theorem

At squared containing radius
\[
 Q=\frac{9789}{2500},
\]
the exterior seven-square boundary ring cannot have quarter-increment
word
\[
 (0,0,1,1,0,1,1).
\]
This statement includes every one of the \(2^7\) core/outer radial
assignments, every allowed local sign choice, every retained true
separating axis, and all boundary endpoints.

The hypotheses are the already proved geometric reduction: neighboring
open square interiors are disjoint; every exterior state is on the
radius-\(1/12\) core boundary or on the containing-disk boundary; the
ordered center-ray gaps satisfy \(\delta_i>19/25\); and the seven physical
frames have lifts in an interval of length less than \(7/10\).
The complete hand frame-concentration theorem supplies the last
hypothesis for every original eight-square packing at \(q\leq Q\).
The fixed-axis radial-boundary reduction supplies the boundary ring
without changing those physical frames.

The proof below assembles the complete continuous pair inequalities.
Their hand proofs use explicit calculus, circular support bounds,
fixed rational reference comparisons, and displayed polynomial
positivity identities. No sampled minimum, adaptive interval tree,
or retained numerical role-box exclusion is a premise.

Every principal pair proof and its independent review is complete.
The source bindings and the exact finite case map are recorded in
**wrong_0011011_hand_word_closure_manifest.json** and
**wrong_0011011_pair_coverage_audit.json**. The latter's accompanying
note is **WRONG_0011011_PAIR_COVERAGE_INDEPENDENT_AUDIT.md**.

## 1. States, angles and the proposed labels

Set
\[
 a_c=\frac7{12},\qquad
 d_c=\frac12+\frac{\sqrt2}{24},\qquad
 d=\sqrt{Q/2}-\frac12.
\]
The unsigned coordinates of a core state lie on the two closed pieces
\[
 a=a_c,\quad 0\leq b\leq\frac12,
\]
or
\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},
 \quad \frac12\leq b\leq d_c,\quad a\geq b.
\]
An outer state lies on
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\frac12,
 \qquad 0\leq b\leq d.
\]
For a chosen sign \(\sigma\in\{-1,1\}\), the actual center in its
nearest-axis frame is \((a,-\sigma b)\), and its signed local angle is
\[
 \alpha=\sigma\arctan(b/a)\in[-\pi/4,\pi/4].
\]

Write the physical frame lifts as \(\beta_i\), with
\(\beta_{i+7}=\beta_i\), and let \(k_i\) be the quarter increments.
The nearest-axis frame change on edge \(i\) is
\[
 \phi_i=k_i\frac\pi2+\beta_{i+1}-\beta_i.
\]
The center-ray and frame changes satisfy
\[
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1}.                 \tag{1}
\]
For a zero-quarter edge, \(-.7<\phi_i<.7\). For a quarter-one
edge, \(\pi/2-.7<\phi_i<\pi/2+.7\).
All component statements use the corresponding closed angle intervals.

The exact label table is **wrong_0011011_labels.json**. A label has
the five features
\[
 L_i^\sigma(a,b)=
 c_i^\sigma+p_i^\sigma a+q_i^\sigma b
 +r_i^\sigma b^2+s_i^\sigma ab.
\]
The integers in the following table are its five coefficients, all
divided by \(100000\).

| Role | Radial kind and sign | \(100000(c,p,q,r,s)\) |
|---:|:---:|---|
| 0 | \(C+\) | \((125,0,103981,0,0)\) |
| 0 | \(C-\) | \((19911,0,63607,0,0)\) |
| 0 | \(O+\) | \((2478,0,93015,2363,-11055)\) |
| 0 | \(O-\) | \((394,0,33945,0,39635)\) |
| 1 | \(C+\), \(C-\) | \((19555,0,63132,0,0)\) |
| 1 | \(O+\), \(O-\) | \((0,-26,83194,-11864,17627)\) |
| 3 | \(C+\) | \((-1449,0,104240,0,0)\) |
| 3 | \(C-\) | \((22042,-34492,98439,-5334,0)\) |
| 3 | \(O+\) | \((0,-1025,16031,0,63457)\) |
| 3 | \(O-\) | \((1670,0,242322,-91744,-95769)\) |
| 4 | \(C+\) | \((4970,0,94831,0,0)\) |
| 4 | \(C-\) | \((16823,0,62312,0,0)\) |
| 4 | \(O+\) | \((3965,0,385510,-149748,-189442)\) |
| 4 | \(O-\) | \((0,-2112,29090,0,44642)\) |

The remaining roles are defined by the exact identity
\[
 L_{2-i}^{\sigma}=L_i^{-\sigma},                       \tag{2}
\]
with indices modulo seven and with the radial kind unchanged.
The table for role 1 satisfies its required self-reflection identity.

At a zero local angle or a nearest-axis tie, choose a representation
once for that vertex and use it in both incident edge costs.
The two signed formulas need not agree at zero. Their values will
cancel because the same choice is used on both edges.
The core side/corner join uses the same polynomial on both pieces.

Define the corrected edge cost
\[
 C_i=\phi_i+\sigma_i L_i^{\sigma_i}(a_i,b_i)
             -\sigma_{i+1}L_{i+1}^{\sigma_{i+1}}(a_{i+1},b_{i+1}).
                                                               \tag{3}
\]
We will use the common strict threshold
\[
 \gamma=\frac{17953}{20000}=.89765.                    \tag{4}
\]

## 2. Necessary signs and the exact finite cover

The first two quarter increments are zero, so (1) gives
\[
 \alpha_0-\alpha_2
 =\delta_0+\delta_1-(\beta_2-\beta_0)
 >\frac{38}{25}-\frac7{10}
 =\frac{41}{50}>\frac\pi4.                            \tag{5}
\]
It follows that \(\alpha_0>0\) and \(\alpha_2<0\).
For example, if \(\alpha_0\leq0\), then
\(\alpha_0-\alpha_2\leq\pi/4\), a contradiction; the other conclusion
is identical.

A zero-quarter edge cannot have signs \((-,+)\). Such signs make
\(\alpha_i-\alpha_{i+1}\leq0\), and then (1) would imply
\(\delta_i\leq\phi_i<.7<19/25\).
These necessary restrictions leave exactly the following local
over-cover:

| Edge | Quarter increment | Allowed signs |
|---:|---:|---|
| 0 | 0 | \(++,+-\) |
| 1 | 0 | \(+-,--\) |
| 2 | 1 | \(-+,--\) |
| 3 | 1 | \(++,+-,-+,--\) |
| 4 | 0 | \(++,+-,--\) |
| 5 | 1 | \(++,+-,-+,--\) |
| 6 | 1 | \(++,-+\) |

There are \(19\) edge/sign classes and four ordered radial-kind
choices \(CC,CO,OC,OO\) for each, hence \(76\) directed pair cases.
All four signed separators are covered for every pair case, giving
\(304\) directed axis cases.
Additional geometric restrictions could only reduce this list.

Reflection of the plane followed by reversal of the center order
sends a pair to
\[
 (i,\sigma,\tau,K_s,K_t)
 \longmapsto(1-i,-\tau,-\sigma,K_t,K_s).                \tag{6}
\]
The word is invariant under this operation. Identity (2) shows that
the cost (3) is also invariant. The four retained axes are permuted
by \((1\ 3)(2\ 4)\).
This uses the actual coefficient table; no arbitrary role labels
are being interchanged.

The only fixed pair cases in (6) are edge \(4\), signs \((+,-)\),
with radial kinds \(CC\) or \(OO\). Consequently the \(76\) pair
cases form
\[
 (76+2)/2=39
\]
reflection classes: ten \(CC\), nineteen mixed, and ten \(OO\).
The independent finite cover reconstructs both the sign restrictions
and every reflection identity coefficient by coefficient.

## 3. The complete pair theorem

**Pair theorem.** For every case in Section 2, every point on the
stated side or arc, and every physically retained separating axis,
\[
 C_i>\gamma.                                         \tag{7}
\]

Here is its full hand-proof map. All names in the map have prefix
**WRONG_0011011_** and suffix **_HAND_PROOF.md**.
The abbreviations are expanded immediately below. In every row the
\(CC\) proof is **ALL_CORE_CORE**, which gives the stronger bound
\(C_i>.91\).

| Edge | Signs | \(CO\) proof | \(OC\) proof | \(OO\) proof |
|---:|:---:|---|---|---|
| 0 | \(++\) | mixed-zero-same | mixed-zero-same | outer-zero-same |
| 0 | \(+-\) | mixed-zero-opposite | mixed-zero-opposite | outer-zero-asymmetric |
| 2 | \(--\) | e2-negative-core | e2-core-side + corner | outer-e2-negative |
| 2 | \(-+\) | e2-core-positive-outer | e2-outer-positive-core | outer-e2-opposite |
| 3 | \(++\) | e3-positive-core-positive-outer | e3-four-mixed | outer-e3-positive |
| 3 | \(+-\) | e3-four-mixed | e3-four-mixed | outer-e3-positive-negative |
| 3 | \(-+\) | e3-negative-core-positive-outer | e3-outer-positive-core | outer-e3-opposite-axes12 + axes34 |
| 3 | \(--\) | e3-four-mixed | e3-outer-negative-core | outer-e3-negative |
| 4 | \(++\) | mixed-zero-same | mixed-zero-same | outer-zero-same |
| 4 | \(+-\) | mixed-zero-opposite | reflection of \(CO\) | outer-zero-symmetric |

### Zero-quarter components

| Abbreviation | Full manuscript stem |
|---|---|
| mixed-zero-same | SAME_SIGN_MIXED_ZERO |
| mixed-zero-opposite | OPPOSITE_MIXED_ZERO |
| outer-zero-same | SAME_OUTER_ZERO |
| outer-zero-asymmetric | ASYMMETRIC_OPPOSITE_OUTER_ZERO |
| outer-zero-symmetric | SYMMETRIC_OUTER_WHOLE_ANGLE |

The same-sign zero-quarter proofs explicitly use the physical
center-gap bound to exclude their possible small negative frame
angles. The opposite-sign proofs cover their complete negative and
positive angle ranges. Thus this table does not silently replace
\([-.7,.7]\) by its positive half.
The symmetric whole-angle proof imports
**SYMMETRIC_ALIGNED_OUTER** only for its final aligned scalar
inequality; it proves the whole angle reduction separately.

### Mixed quarter-one components

| Abbreviation | Full manuscript stem |
|---|---|
| e2-negative-core | EDGE2_NEGATIVE_CORE_TO_OUTER |
| e2-core-side | EDGE2_NEGATIVE_CORE_SIDE |
| e2-core-corner | EDGE2_NEGATIVE_CORE_CORNER |
| e2-core-positive-outer | EDGE2_CORE_TO_POSITIVE_OUTER |
| e2-outer-positive-core | EDGE2_OUTER_TO_POSITIVE_CORE |
| e3-four-mixed | EDGE3_FOUR_WHOLE_MIXED_FAMILIES |
| e3-positive-core-positive-outer | EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER |
| e3-negative-core-positive-outer | EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER |
| e3-outer-positive-core | EDGE3_OUTER_TO_POSITIVE_CORE |
| e3-outer-negative-core | EDGE3_OUTER_TO_NEGATIVE_CORE |

The side and corner intervals of the split edge-2 family are
\([0,1/2]\) and \([1/2,d_c]\), so their union is the whole core and
their join is covered twice.
The imported **ALIGNED_MIXED_QUARTER** and
**EDGE2_MIXED_QUARTER_STRIP** prove only their explicitly stated
angle domains. Their parent manuscripts prove all remaining angles.

The six older whole-family notes and those two imports have a fresh
joint independent review in
**WRONG_0011011_EARLIER_MIXED_INDEPENDENT_AUDIT.md**.
That review reconstructs all ten polynomial rows and all 84 printed
Bernstein coefficient bounds, together with the decisive scalar and
contact comparisons. The remaining mixed-family reviews are bound
in the closure manifest.

### Outer quarter-one components

| Abbreviation | Full manuscript stem |
|---|---|
| outer-e2-negative | NEGATIVE_OUTER_QUARTER |
| outer-e2-opposite | OPPOSITE_OUTER_EDGE2_QUARTER |
| outer-e3-positive | EDGE3_POSITIVE_OUTER_PAIR |
| outer-e3-positive-negative | POSITIVE_NEGATIVE_OUTER_QUARTER |
| outer-e3-opposite-axes12 | EDGE3_OPPOSITE_AXES12 |
| outer-e3-opposite-axes34 | EDGE3_OPPOSITE_AXES34 |
| outer-e3-negative | EDGE3_NEGATIVE_OUTER_QUARTER |

The opposite-sign edge-3 notes divide the retained axes into
\(\{1,2\}\) and \(\{3,4\}\), on the same full angle interval.
Their union therefore covers the whole pair, not just an aligned
neighborhood. The negative/negative edge-3 manuscript is its corrected,
independently reviewed **134-comparison** version; the obsolete
126-comparison sign-swapped version is not an input.
The final positive/positive edge-3 theorem has its complete
**147-comparison** hand arithmetic and independent **47-comparison**
review, including all contact and endpoint cases.

These component theorems prove every entry in the pair map.
Their strict inequalities give (7), including all boundary choices.
No unproved numerical table entry remains in this pair theorem.

## 4. The contradiction is exact

Choose the radial kind and signed representation of each vertex
once, as in Section 1. Sum the seven costs in (3). Every label
appears once with each sign, so they cancel exactly.
The physical frame lifts are periodic, and the quarter word has
four increments equal to one. Therefore
\[
 \sum_{i=0}^{6}C_i
 =\sum_{i=0}^{6}\phi_i
 =\frac\pi2\sum_{i=0}^{6}k_i
 =2\pi.                                               \tag{8}
\]
This identity is unaffected by jumps between alternative signed
label formulas or by the choice of a nearest-axis tie.

On the other hand, (7) gives
\[
 2\pi=\sum_i C_i>7\gamma=\frac{125671}{20000}.
                                                               \tag{9}
\]
The elementary rational comparison is
\[
 \frac{125671}{20000}-\frac{710}{113}
 =\frac{823}{2260000}>0,
 \qquad 2\pi<\frac{710}{113}.                          \tag{10}
\]
Equations (9) and (10) contradict each other.
This proves the whole-word theorem.

For a short hand verification of the upper bound in (10), let
\[
 T_n(x)=\sum_{j=0}^{n-1}\frac{(-1)^j x^{2j+1}}{2j+1}.
\]
The alternating arctangent inequalities and Machin's identity give
\[
 \pi
 =16\arctan(1/5)-4\arctan(1/239)
 <16T_5(1/5)-4T_2(1/239)
 <\frac{355}{113}.
\]
The last comparison is a fixed positive rational inequality,
reconstructed in the companion finite-arithmetic audit.

## 5. Consequence for the original packing and equality

The hand central-core, common-point, boundary-reduction and
frame-concentration results associate the relevant exterior
boundary ring to any original eight-square packing at \(q\leq Q\).
The seven-word classification applies to that ring. This theorem
eliminates its entire \(0011011\) branch, including every radial
assignment; no separate all-outer or one-core numerical capture
remains for this branch.

All pair inequalities used here are strict with a positive rational
cyclic reserve. Hence this wrong word contributes **no equality
configuration** to the sharp theorem.
Together with the separate complete hand exclusion of \(0010111\)
and the four double-increment words, it leaves only \(0101011\).
The candidate-word capture and the classification of its equality
family remain their own theorems; they are not asserted by this
word exclusion.
