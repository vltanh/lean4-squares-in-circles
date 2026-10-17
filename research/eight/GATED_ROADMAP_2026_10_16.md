# Gated roadmap to the unrestricted eight-square theorem

Started: 2026-10-16 (America/Chicago); continued 2026-10-17 UTC.
Starting head: 77ac445d3c8b5299d02aa58d14aa444646234959.
Scope: PR #9, research/eight/**, pen-and-paper research with exact computer
assistance. This active queue supersedes GATED_ROADMAP_2026_10_13.md.

**The unrestricted sharp radius theorem and complete equality classification
are proved with exact computer assistance. The requested all-hand proof
remains active.** All three remaining
radial words have complete global covers, all four retained terminal cases
satisfy the hypotheses of the final sharp dual, and the radius pullback
closes the unrestricted argument. The full assembly is
[UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md](UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md).
The central core, exact sharp-ceiling bracket, and terminal coefficient
arithmetic now have complete hand replacements. Analytic replacement of
the global pair/capture premises is the active gate. The user has explicitly included global equality classification in the
active hand-proof target. The fixed-axis equality pullback and the complete five-parameter domain
have independent hand audits. Their only remaining non-hand input is the
same global capture being converted for optimality.

The [complete common quarter table](COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md)
now gives whole-domain hand proofs for all three increments. Its cyclic sum
excludes all four words containing a double increment. The upstream frame
bound now has its complete hand proof in
[HAND_EXTERIOR_FRAME_CONCENTRATION.md](HAND_EXTERIOR_FRAME_CONCENTRATION.md). The [independent audit](COMMON_QUARTER_TABLE_INDEPENDENT_AUDIT.md)
passes. The [exact square-completion terminal](HAND_EXACT_CENTER_SQUARE_COMPLETION.md)
is valid for \(S\le1/500\). The whole word 0010111 now has a complete hand assembly; its final
scalar-kernel independent review is pending. The remaining 0011011
quarter-one cases and candidate capture are the active hand work.

## 1. Exact target and closure standards

Let \(q_*=R_*^2\) be the unique least admissible five-corner family radius
selected by [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md), with the
radical and stationary equations in
[HUMAN_FIVE_CORNER.md](HUMAN_FIVE_CORNER.md). The decimal
\(R_*\approx1.97877086534\) is descriptive only. The
[exact construction](ANALYTIC_EXACT_CONSTRUCTION.md) proves attainment by
an actual eight-square packing.

The unrestricted lower-bound target is:

> Every eight-tuple of unit squares with pairwise disjoint open interiors
> contained in a disk of squared radius q satisfies q >= q_*.

Three exits are distinguished throughout this roadmap:

1. **Optimality:** the unrestricted lower bound and actual construction.
   This exit has passed with exact computer assistance.
2. **Equality:** every attaining pose, including genuine slider freedoms
   and the eighth central square. This is explicitly requested and now proved using the completed global
   capture plus independently reviewed hand equality arguments. The exact
   five-parameter domain includes a box of noncongruent packings, so
   isolated-pose uniqueness is false.
3. **Hand-proof closure:** analytic replacement of every retained
   computer-assisted premise. This is the user's active requirement.

An exact computer-assisted theorem is a valid research result. It does not
by itself satisfy the requested hand proof. Decreasing a rounded search
radius or repeating completed subclass exclusions does not discharge an
open gate. No Lean writing or compilation, CI invocation, production-source
change, or merge is included in this work.

## 2. Gate table with exact exits

| Gate | Required exit | Current status |
|---|---|---|
| G0: target, exact model, attainment | Define q_* exactly; cover every actual packing by the genuine square/SAT model; construct attainment. | **Passed, hand proofs.** Foundational interfaces re-audited. |
| G1: fiber and owner alternatives | Preserve original common-center fibers, sparse alternatives, owner ties and exhaustive orientation cover. | **Passed, hand proofs.** |
| G2: central core | Every packing below the research ceiling has one square containing the closed radius-1/12 disk in its open interior. | **Passed, hand proof at 9789/2500.** A universal transverse segment and two forbidden-angle estimates exclude every shallow central square. |
| G3: radial-boundary cover | Deform every exterior seven-cycle, at fixed actual frames and angle sum 2π, onto two explicit boundary curves, retaining adjacent true SAT. | **Passed, hand proof.** Nonneighbor constraints are explicitly relaxed. |
| G4: global frame concentration | Put all seven exterior frames in one open 45-degree interval, excluding every former M5 and M6 branch. | **Passed, computer-assisted.** All 40 four-type branches, then hand odd-cycle and frame-lifting arguments. |
| G5a: no adjacent core states | Reduce the boundary cycle to the five words with no adjacent C. | **Passed.** Hand core-pair estimate using G4. |
| G5b: three-core exclusion | Exclude the entire COCOCOO continuous family. | **Passed, computer-assisted.** Eight complete branches, then a hand cyclic sum. |
| G5c: short two-core exclusion | Exclude the entire COCOOOO continuous family. | **Passed, computer-assisted.** 28 complete directed role/sign branches, then a hand cyclic sum. |
| G6: global survivor capture | Cover every remaining physical boundary cycle by explicit families on which all sharp-proof hypotheses hold. | **Passed, computer-assisted.** All 123 exclusions complete: 45 all-O, 46 one-C, 32 long two-C; every closed domain union independently audited. |
| G7a: broad sharp terminal inequality | Prove a uniform sharp bound for every surviving owner assignment and both projected sliders, without a center-proximity assumption. | **Passed, hand proof.** Nine position brackets, four rectangles, nine scalar reserves, and an explicit nonlinear dual bound. |
| G7b: terminal completeness | Prove every G6 survivor satisfies the actual frame, owner, tilt and slider hypotheses of G7a. | **Passed.** Four full-SAT budget compositions, four angle lifts, complete slider interfaces; S<1/10000. |
| G8: unrestricted assembly | Apply the terminal bound before radius expansion, then combine with exact attainment. | **Passed, computer-assisted theorem.** Hand monotone-radius transfer preserves every originally feasible signed separator. |
| G9: global equality | Recover all original eight-square attaining poses and give the exact feasible parameter family, with converse. | **Passed, with the same computer-assisted global capture input.** The independently reviewed equality pullback fixes five original anchors and both outer frame groups. The complete explicit five-parameter domain is necessary and sufficient and contains a full box of noncongruent poses. Its classification argument and 84 fixed comparisons are hand proofs. |
| H: hand conversion and final audit | Replace every retained computational premise by analytic inequalities and audit all boundaries, ties and dependencies. | **ACTIVE.** The frame inequalities and 0010111 exclusion now have hand replacements; the final 0010111 independent scalar review, remaining 0011011 cases and candidate capture are active. |

The old M5-DIFFUSE queue, low 3+5/4+4 reference certificates, and narrow
center-proximity terminal are no longer dependencies of the completed
route. Their historical results remain separately available.

## 3. The completed global cover

The parent domain is an ordered seven-cycle of actual square frames with
center-angle gaps \(3/5<\delta_i<\pi\), sum exactly \(2\pi\), and all
seven adjacent true SAT disjunctions. Every center lies on either the outer
curve O or the radius-1/12 core-avoidance curve C. In its canonical chart the
center is \((a,-au)\), so its frame differs from its center ray by
\(\arctan u\). Nonneighbor overlaps and overlaps with the central square
beyond its radius-1/12 core are relaxed.

The earlier gates leave precisely:

| Word | Complete global exclusions | Retained terminal case |
|---|---:|---|
| OOOOOOO | 45 | Both T and G outer |
| COOOOOO | 46 | T core or G core |
| COOCOOO | 32 | Both T and G core |

All 123 exclusions are full continuous pair-potential theorems. The closed
domain audits verify every complementary cut, sequential hypothesis,
reflection, canonical maximum choice and inclusion in the frozen certificate
domain. No sampled contact graph is used as an exhaustive classification.

For each of the four retained cases, selected and complementary signed-axis
certificates form a complete partition of all eight SAT axes. Their union
first proves a baseline pair inequality for every actual separator. Only
then does the cyclic sum exclude complementary owners and force the
five aligned-edge mismatch sum below 1/10000. This order avoids assuming
the desired owners in order to prove them.

The captured common tilt satisfies \(1/10<t<4/25\). Comparison sliders
are chosen from actual transverse projections, with
\(T_y\in[29/50,7/5]\) and \(\eta\in[-1/2,37/100]\).
This choice removes the former requirement that all centers first be
captured inside a tiny neighborhood of the candidate.

## 4. The exact sharp contradiction

Let \(q_c=3.91553413751747532652\), as an exact rational, and put
\(Q_\sharp=q_c+10^{-16}\). For a hypothetical packing at \(q<q_*\),
work first at \(\widetilde q=\max(q,q_c-2\cdot10^{-16})<q_*\).
The [hand sharp-ceiling bracket](HUMAN_SHARP_CEILING_BRACKET.md), using
eight explicit radical brackets and two-stage strong convexity, proves
\(q_c-2\cdot10^{-16}<q_*<Q_\sharp\).
Perform the radial reduction there, then expand only the O radii to
\(Q_\sharp\). The hand monotonicity theorem preserves every originally
valid signed separator, all center rays and all actual frames.

The global capture is proved at \(Q_\sharp\), but the terminal dual is
applied **before expansion**, at \(\widetilde q\). A forbidden axis at
the smaller radius would remain forbidden and feasible after expansion,
contradicting the completed owner theorem. The slider interfaces hold
directly throughout the lower-radius interval.

Normalize A's frame to zero and G's frame to t. Let \(S<10^{-4}\) be
the sum of the five aligned-edge mismatches. The stationary comparison
family and positive balanced weights give

\[
\widetilde q\ge q_*+
\frac{3\mu_H}{8}(t-t_*)^2+
\frac12\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2+
\frac1{200}S\ge q_*.
\]

The positive quadratic center terms absorb arbitrary anchored-center
displacements. The two free-slider displacements are parallel to their
reference contact normals, so their angular coupling is quadratic by
\((R(a)n-n)\cdot(\xi n)=\xi(\cos a-1)\).
This proves the sharp contradiction without a center-proximity assumption.

## 5. Evidence and reproduction

The main proof links every dependency. The new
[capture package](certificates/sharp_capture/README.md) preserves 28,039
completed numerical evidence files and 170 additional interface files,
with SHA256 bindings. Its portable extraction/replay script authenticates
all 28,211 members and replays thirteen mathematical interfaces in a fresh
directory. That fresh-directory replay passed in this continuation.

The 123 ordinary exclusions comprise 1,402 signed branches, 1,225,792
initial affine-piece rectangles, and 230,820,848 exact subdivision nodes.
Four selected terminal budgets and four complementary owner certificates
complete the full-SAT terminal union. The
[certificate index](SHARP_CAPTURE_CERTIFICATE_INDEX.md) records their
separate manifests and counts; rejected or interrupted discovery probes
are excluded.

Earlier completed evidence includes all four central-core branches, all
40 four-type branches, all eight three-core branches, and all 28 short
two-core branches. Their original sources, logs, exact rational data and
independent range/domain audits remain in their existing locations.

## 6. Active hand-conversion queue

| Hand gate | Required analytic replacement | Current concrete work |
|---|---|---|
| H1: central core | Prove the strict radius-1/12 core for every packing at 9789/2500. | **Passed.** [Transverse-segment proof](HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md), with 19 explicit polynomial rows and two elementary forbidden-width estimates; independently reviewed. |
| H2a: frame concentration | Replace the full four-type continuous pair theorem. | **Passed, hand proof.** All ten entries and all 128 ordered source-axis branches have complete independent reviews. The final [C/M audit](CORE_MID_WHOLE_PAIR_INDEPENDENT_AUDIT.md) verifies the complete geometry and independently reconstructs its polynomial and curvature bounds. The [hand assembly](HAND_EXTERIOR_FRAME_CONCENTRATION.md) proves D < .7 by the exact seven-walk budget and orientation-circle lifting. |
| H2b: global word and owner capture | Derive every sharp-terminal hypothesis throughout the full remaining domain. | **Active.** H2a now supplies the hand frame premise; the common hand table excludes all four double-increment words. For 0010111, the [complete hand exclusion](SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md) covers all 304 radial/sign/axis possibilities. The final 48 O/O quarter-one branches are closed by six contact neighborhoods and 140 fixed scalar regimes with 4,475 nonnegative coefficients. The aligned component has independent review; final scalar-kernel review is pending. For 0011011, all C/C and all zero-quarter mixed/O/O cases are proved, and every mixed edge2/6 quarter-one family is complete. The O/O quarter-one and mixed edge3/5 quarter-one cases remain active. Candidate 0101011 capture remains open. |
| H3: terminal constants and radius bracket | Give hand-verifiable broad stationary, slider, weight, owner and exact-ceiling inequalities. | **Passed.** [Compact terminal proof](HUMAN_BROAD_TERMINAL_ARITHMETIC.md), [sharp bracket](HUMAN_SHARP_CEILING_BRACKET.md), and [independent audit](HAND_TERMINAL_AND_CEILING_INDEPENDENT_AUDIT.md). The [exact square completion](HAND_EXACT_CENTER_SQUARE_COMPLETION.md) now extends the sufficient mismatch bound twenty-fold to \(S\le1/500\), for arbitrary anchored centers and all 32 owners. All bounds are displayed finite rational arithmetic with no adaptive search. |
| H4: assembly audit | Substitute the completed hand lemmas into the unrestricted argument and check all ties, boundaries, signs and radius transfers. | H1 and H3 are substituted into the main assembly. Full hand closure waits for the remaining H2b work and its assembly audit. |
| H5: equality classification | Classify every optimal original packing, modulo isometry and relabeling, including the full freedoms of the remaining squares. | **Passed as a hand component conditional on global capture.** The independently reviewed [equality pullback](EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md) fixes the original five anchors and both outer orientation groups once boundary capture is supplied. It leaves exactly two exterior slider coordinates and one remaining square. The independently reviewed [complete five-parameter domain](COMPLETE_EQUALITY_PARAMETER_DOMAIN.md) gives the hand necessity and sufficiency argument, 84 fixed comparisons, and an explicit box of five independently variable noncongruent poses. Its sole remaining non-hand input is global capture. |

**Next required exit:** a complete analytic replacement for the retained
wrong-word and candidate-capture premises. The hand-proof gate stays open until
that replacement is written and checked; the computer-assisted result is
not relabeled as a hand proof.
