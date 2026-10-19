# Complete table-free exclusion of the quarter word 0010111

## Theorem and dependency boundary

Put \(Q=9789/2500\). After the central-core, fixed-axis radial-boundary,
and frame-concentration reductions, the exterior boundary seven-cycle
cannot have quarter-increment word
\[
                 (k_0,\ldots,k_6)=(0,0,1,0,1,1,1).       \tag{1}
\]
This includes every core/outer assignment, every original feasible
separating axis, both signs of every frame error, and all weak contacts.
There is no candidate-word tangent-cut, mismatch, owner-selection, or
tilt hypothesis in this theorem.

This is the table-free successor of
[SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION](../SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md).
The latter's contact-neighborhood/table angle cover and its arithmetic
manifest are not dependencies. The complete continuous component
successors are bound explicitly below. The eight successors already
present at source commit `bbe15f74b3406647b89eb26710629c0bb3a54f11`
finish the previously unassembled components; this note supplies the
whole-word mathematical assembly, not another numerical certificate.

## 1. The actual boundary-cycle interface

Use the boundary reduction and the complete theorem in
[HAND_EXTERIOR_FRAME_CONCENTRATION](../HAND_EXTERIOR_FRAME_CONCENTRATION.md).
Every unsigned state is on either the core side/corner
\[
 a=7/12,\quad 0\le b\le1/2,
\]
\[
 (a-1/2)^2+(b-1/2)^2=1/144,\quad
 1/2\le b\le a,\quad a\ge d_c:=1/2+\sqrt2/24,
                                                               \tag{2}
\]
or the outer arc
\[
 a=\sqrt{Q-(b+1/2)^2}-1/2,\quad
                  0\le b\le d:=\sqrt{Q/2}-1/2.            \tag{3}
\]
A signed representation has own-frame center \((a,-\sigma b)\),
\(\sigma\in\{-1,1\}\), and signed local angle
\(\alpha=\sigma\arctan(b/a)\in[-\pi/4,\pi/4]\).
The physical frame lifts \(\beta_i\) are periodic and have spread
strictly less than \(7/10\). Their increments and the ordered center
gaps satisfy
\[
 \phi_i=k_i\pi/2+\beta_{i+1}-\beta_i,\qquad
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1}>19/25,
 \qquad \sum_i\delta_i=2\pi.                              \tag{4}
\]
Thus every zero edge lies in \(|\phi|<.7\), and every one edge lies
in \(|\phi-\pi/2|<.7\). All component statements cover the corresponding
closed angle domains. Only consecutive-square disjointness is used.

For reference, with source \((a,-\sigma b)\), target \((A,-\tau B)\),
and \(W=(1+|\sin\phi|+|\cos\phi|)/2\), the four original one-based
forward separating inequalities are
\[
\begin{array}{ll}
1:&\sigma b+A\sin\phi-\tau B\cos\phi\ge W,\\
2:&-a\cos\phi+\sigma b\sin\phi+A\ge W,\\
3:&a\sin\phi+\sigma b\cos\phi-\tau B\ge W,\\
4:&a-A\cos\phi-\tau B\sin\phi\ge W.
\end{array}                                                \tag{5}
\]
The existing forward-axis theorem supplies at least one such inequality
on each actual edge. We never replace this union by a preferred owner.

Apply [HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
to this same cycle, before any word exclusion. Its hypotheses are the
boundary geometry, G1 pair inequalities, physical gaps, and the closed
frame tour. It excludes every feasible zero-edge primary axis, namely
one-based axes 2 and 4, including primary axes tied with secondary ones.
This is an actual-cycle input. No omitted isolated primary pair is
claimed to satisfy a replacement label inequality.

## 2. Exact labels and the intrinsic signed case cover

The two initial zero edges in (1) imply
\[
 \alpha_0-\alpha_2
 =\delta_0+\delta_1-(\beta_2-\beta_0)
 >38/25-7/10=41/50>\pi/4.                                 \tag{6}
\]
Since both local angles lie in \([-\pi/4,\pi/4]\), this forces
\(\alpha_0>0\) and \(\alpha_2<0\). Also a zero edge cannot have
signs \((-,+)\): then (4) would imply \(\delta_i\le\phi_i<.7\).
These deductions give precisely the following local over-cover:

| Edge | Quarter | Allowed signs |
|---:|---:|---|
| 0 | 0 | ++, +- |
| 1 | 0 | +-, -- |
| 2 | 1 | -+, -- |
| 3 | 0 | ++, +-, -- |
| 4 | 1 | ++, +-, -+, -- |
| 5 | 1 | ++, +-, -+, -- |
| 6 | 1 | ++, -+ |

There are nineteen directed edge/sign cases: seven zero and twelve one.
Each allows the four radial orders \(CC,CO,OC,OO\). Each radial/sign
case has four original axes in (5). This is a 304-axis over-cover,
not a partition of a continuous state or angle domain.

Define one signed role label per vertex by
\[
 \ell_i(a,\sigma b)=c_i^\sigma+p_i^\sigma a+\sigma q_i^\sigma b.
                                                               \tag{7}
\]
The following integer triples, divided by \(100000\), are the exact
coefficients \((c,p,q)\). They reproduce `short_hand_labels.json` as
mathematical definitions, so the JSON or a transcription checker is
not an input to the theorem.

| Role | Sign | Core triple | Outer triple |
|---:|:---:|---|---|
| 0 | + | (3177, 0, 108816) | (0, 0, 94766) |
| 1 | + | (25648, 0, 62095) | (6130, 0, 99940) |
| 1 | - | (-14041, 0, 62095) | (24463, -13422, 103828) |
| 2 | - | (11680, 0, 113855) | (-2623, 9133, 88074) |
| 3 | + | (4149, 0, 104729) | (-68803, 51554, 119909) |
| 3 | - | (-15540, 0, 62750) | (50866, -33147, 113360) |
| 4 | + | (25812, 0, 58829) | (6294, 0, 71553) |
| 4 | - | (3897, 0, 104073) | (-23483, 19335, 76744) |
| 5 | + | (2448, 0, 99195) | (2448, 0, 86884) |
| 5 | - | (1027, 0, 95269) | (29579, -20967, 83048) |
| 6 | + | (9072, 0, 95324) | (-20704, 21826, 83472) |
| 6 | - | (7651, 0, 99173) | (-18660, 18602, 80996) |

Choose the radial/sign representation once for each vertex and use it
on both incident edges. Alternative label formulas need not agree at
a zero coordinate or nearest-axis tie. The core side/corner join uses
the same formula. Define
\[
 C_i=\phi_i+\ell_i-\ell_{i+1},\qquad
 \gamma_2=359/400,\quad \gamma_i=17953/20000\quad(i\ne2).
                                                               \tag{8}
\]

Reflection and reversal used inside a pair proof do not assert a
symmetry of the short word or interchange unrelated role labels.
They interchange the two states, change the signs to \((-\tau,-\sigma)\),
and negate the reversed labels. In the standard tuple notation
\(C=\phi+c+pa+\sigma qb-PA-\tau tB\), this gives
\[
 (p,q,P,t)\longmapsto(-P,t,-p,q),
\]
with \(c\), \(\phi\), and the original corrected cost unchanged.
It swaps original axes \(1\leftrightarrow3\) and
\(2\leftrightarrow4\). All successor proofs use this exact rule.

## 3. Core/core and mixed-radial components

[SHORT_WRONG_WORD_ALL_CORE_CORE_HAND_PROOF](../SHORT_WRONG_WORD_ALL_CORE_CORE_HAND_PROOF.md)
proves \(C_i>.898\) for all nineteen core/core sign cases, independently
of which original axis separates. Its continuous ingredients are the
statewise core bound
\[
 0\le\arctan(b/a)-gb\le\pi/4-gd_c\quad(0\le g\le8/7),
\]
and the strict core/core center gap \(\delta>27/20\), obtained from
center distance at least one and center norms less than \(4/5\).
Its two exceptional signed rows are handled by their displayed direct
coordinate inequalities. The finite role substitutions are arithmetic
in (7), not variable-domain certificate rows. This covers all 76
core/core original-axis cases.

[HAND_SHORT_WORD_MIXED_ZERO_COMPLETE_WITHOUT_TABLES](HAND_SHORT_WORD_MIXED_ZERO_COMPLETE_WITHOUT_TABLES.md)
proves the complete mixed-zero component for this actual cycle. It
covers all 28 transverse branches, proving them impossible or giving
\(C_i>.898\); the other 28 primary branches are excluded by Section 1.
Its complete zero-source arc curvature and intrinsic support-transition
arguments replace the old angle tables. Section 4 of that successor
identifies exactly the retained full-domain parent sections. No
candidate capture or mismatch premise enters those imports.

[HAND_SHORT_WORD_MIXED_QUARTER_NEGATIVE_CORE_WITHOUT_TABLES](HAND_SHORT_WORD_MIXED_QUARTER_NEGATIVE_CORE_WITHOUT_TABLES.md),
Section 7, is the complete mixed-quarter assembly. It uses
[the circle/positive-core contact successor](HAND_SHORT_WORD_MIXED_QUARTER_CIRCLE_AND_SIDE_CONTACTS_WITHOUT_TABLES.md)
and the stated full-domain sections of
[SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF](../SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md).
It proves \(C_i>.898\) for all 96 mixed-quarter original owners on
both full angle halves. The two core pieces, their join, and every
contact continuation and inactive-source boundary are included.
The parent source-sign reductions are pointwise lower bounds for the
original cost; they do not change a chosen vertex label in (8).
Neither parent polynomial appendix nor a moving multiplier table is used.

Together these theorems cover all 152 mixed original-axis cases.

## 4. All outer zero-quarter owners

There are 28 original outer-zero branches. Fourteen are primary and
are excluded by the independent cycle theorem in Section 1. The
fourteen transverse branches have the following complete cover:

| Original families | Complete successor | Bound |
|---|---|---:|
| (0,++,1), (1,--,3), (3,++,1), (3,--,3) | [Favorable same signs](HAND_SHORT_WORD_OUTER_ZERO_SAME_WITHOUT_TABLES.md) | > .898 |
| (0,++,3), (1,--,1), (3,++,3), (3,--,1) | [Unfavorable same signs](HAND_SHORT_WORD_UNFAVORABLE_ZERO_SECONDARY_WITHOUT_TABLES.md) | > 1.03 |
| (i,+-,j), i in {0,1,3}, j in {1,3} | [Opposite signs](HAND_SHORT_WORD_OUTER_ZERO_OPPOSITE_WITHOUT_TABLES.md) | > .898 |

Each successor uses the exact labels in (7) and the stipulated weak
axis in (5). The same-sign proofs establish when nonpositive angles
are impossible, rather than omit that half. The opposite-sign proof
covers both angle signs and every axial/diagonal contact exit.
Its zero-source curvature import is the geometric lemma in Section 2.1
of the mixed-zero successor; that lemma is independent of core labels.
Thus no old mixed angle table re-enters through the outer proof.

## 5. All outer quarter-one owners, without near-aligned patches

The following proof abbreviations refer to entire original angle
domains, not to an interval chain:

- **U**: [same-sign unit supports](HAND_SHORT_WORD_SAME_SIGN_UNIT_SUPPORTS_WITHOUT_TABLES.md).
- **S** and **P**: [same-sign secondary](HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md)
  and [same-sign primary](HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md).
- **O**: [opposite secondary](HAND_SHORT_WORD_OPPOSITE_SECONDARY_FAMILIES_WITHOUT_TABLES.md).
- **V**: [opposite primary lower halves](HAND_SHORT_WORD_NEGATIVE_PRIMARY_FAMILIES_WITHOUT_TABLES.md)
  together with [opposite primary upper halves](HAND_SHORT_WORD_OPPOSITE_UPPER_PRIMARY_COMPLETE_WITHOUT_TABLES.md).
  The latter explicitly imports the three other upper owners from
  [upper-primary contacts](HAND_SHORT_WORD_UPPER_PRIMARY_CONTACTS_WITHOUT_TABLES.md).
- **R**: [positive role 4](HAND_SHORT_WORD_ROLE_FOUR_POSITIVE_QUARTER_WITHOUT_TABLES.md).
- **E**: [complete role 5](HAND_SHORT_WORD_EDGE_FIVE_COMPLETE_WITHOUT_TABLES.md)
  together with [its opposite-sign component](HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md).
  Its Section 7 also proves every role-4 (+,-) owner.

Here is the entire 48-owner cover, in original one-based axis numbering.
Every entry covers both full halves \(0\le|\phi-\pi/2|\le.7\).

| Edge | Signs | Axis 1 | Axis 2 | Axis 3 | Axis 4 |
|---:|:---:|:---:|:---:|:---:|:---:|
| 2 | -- | U | U | S | P |
| 2 | -+ | O | V | O | V |
| 4 | -- | U | U | S | P |
| 4 | -+ | O | V | O | V |
| 4 | +- | E | E | E | E |
| 4 | ++ | R | R | U | U |
| 5 | -- | E | E | E | E |
| 5 | -+ | E | E | E | E |
| 5 | +- | E | E | E | E |
| 5 | ++ | E | E | E | E |
| 6 | -+ | O | V | O | V |
| 6 | ++ | S | P | U | U |

These are precisely the twelve quarter-one signed cases of Section 2,
with four axes each: 48 owners and 96 angle halves. Every stated bound
implies \(C_i>\gamma_i\). In particular **O** and **V** on edge 2 may
use \(.8975\); that is exactly the edge-2 threshold in (8).

The **S/P** pair uses the primary successor's Section 2 for its aligned
scalar. It does not import the historical near-aligned manuscript.
The **V** pair covers every lower half and each of the six upper owners
by the explicitly listed complement. Consequently none of the 140
scalar rows, their 4,475 coefficient comparisons, or the six old
near-aligned patches is needed, directly or indirectly.

## 6. Exact cancellation and contradiction

Sections 3--5 give \(C_i>\gamma_i\) on every possible edge of the same
cycle, with the representation choices fixed in Section 2. This is an
actual-cycle conclusion; excluded primary-zero branches are not
independent-pair inequalities.

Each original vertex label in (8) appears once positively and once
negatively. The frame differences in (4) also telescope. Since (1)
contains four unit quarter increments,
\[
 \sum_{i=0}^6 C_i=\sum_{i=0}^6\phi_i
      =\frac\pi2\sum_{i=0}^6k_i=2\pi.                    \tag{9}
\]
However, the seven strict inequalities give
\[
 \sum_i C_i>
 \frac{359}{400}+6\frac{17953}{20000}
 =\frac{31417}{5000}
 =\frac{710}{113}+\frac{121}{565000}
 >2\pi.                                                   \tag{10}
\]
The rational reserve is exact. To prove the only transcendental
comparison, put
\(T_n(x)=\sum_{j=0}^{n-1}(-1)^jx^{2j+1}/(2j+1)\).
Machin's identity and the adjacent alternating arctangent bounds give
\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
   <16T_5(1/5)-4T_2(1/239)<355/113.
\]
The last inequality is one explicit rational comparison. Thus
\(2\pi<710/113\), and (9)--(10) contradict each other.
This proves the complete theorem.

## 7. What has and has not been concluded

This excludes the whole 0010111 branch, including every radial word,
all signed representations allowed by (6), and all weak original
separators. It has no equality configuration because (10) has strict
positive reserve. Together with
[the complete 0011011 exclusion](HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md),
both residual binary wrong-word exclusions now have table-free hand
assemblies.

No old closure manifest, program output, state mesh, angle mesh,
Bernstein coefficient row, or table of moving contacts is a premise
of this assembly. The finite coefficient definitions and intrinsic
role/axis maps specify functions and actual geometric alternatives;
the cited successors prove their inequalities on whole continuous
domains by contact geometry, calculus, and explicit polynomial identities.

The candidate-word tangent cuts and mismatch contractions remain separate
mathematical obligations. They are not consequences of cancelling labels
in a wrong word, and no unrestricted sharp lower bound is claimed here
before those capture hypotheses are discharged.
