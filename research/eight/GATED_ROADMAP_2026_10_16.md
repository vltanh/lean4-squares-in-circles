# Gated roadmap to the unrestricted eight-square theorem

Started: 2026-10-16 (America/Chicago); continued 2026-10-17 UTC.
Starting head: 77ac445d3c8b5299d02aa58d14aa444646234959.
Scope: PR #9, research/eight/**, pen-and-paper research with exact computer
assistance. This active queue supersedes GATED_ROADMAP_2026_10_13.md.

**The unrestricted sharp radius theorem is complete with exact computer
assistance. The requested hand proof remains active.** All three remaining
radial words have complete global covers, all four retained terminal cases
satisfy the hypotheses of the final sharp dual, and the radius pullback
closes the unrestricted argument. The full assembly is
[UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md](UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md).
Analytic replacement of its retained computational premises is the active
gate. Global equality classification remains a separate open gate.

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
   and the eighth central square. This exit remains open.
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
| G2: central core | Every packing below the research ceiling has one square containing the closed radius-1/12 disk in its open interior. | **Passed, computer-assisted.** All four exact branches replayed. Hand replacement active. |
| G3: radial-boundary cover | Deform every exterior seven-cycle, at fixed actual frames and angle sum 2π, onto two explicit boundary curves, retaining adjacent true SAT. | **Passed, hand proof.** Nonneighbor constraints are explicitly relaxed. |
| G4: global frame concentration | Put all seven exterior frames in one open 45-degree interval, excluding every former M5 and M6 branch. | **Passed, computer-assisted.** All 40 four-type branches, then hand odd-cycle and frame-lifting arguments. |
| G5a: no adjacent core states | Reduce the boundary cycle to the five words with no adjacent C. | **Passed.** Hand core-pair estimate using G4. |
| G5b: three-core exclusion | Exclude the entire COCOCOO continuous family. | **Passed, computer-assisted.** Eight complete branches, then a hand cyclic sum. |
| G5c: short two-core exclusion | Exclude the entire COCOOOO continuous family. | **Passed, computer-assisted.** 28 complete directed role/sign branches, then a hand cyclic sum. |
| G6: global survivor capture | Cover every remaining physical boundary cycle by explicit families on which all sharp-proof hypotheses hold. | **Passed, computer-assisted.** All 123 exclusions complete: 45 all-O, 46 one-C, 32 long two-C; every closed domain union independently audited. |
| G7a: broad sharp terminal inequality | Prove a uniform sharp bound for every surviving owner assignment and both projected sliders, without a center-proximity assumption. | **Passed.** Hand nonlinear dual expansion, with exact finite coefficient/stationary premises. |
| G7b: terminal completeness | Prove every G6 survivor satisfies the actual frame, owner, tilt and slider hypotheses of G7a. | **Passed.** Four full-SAT budget compositions, four angle lifts, complete slider interfaces; S<1/10000. |
| G8: unrestricted assembly | Apply the terminal bound before radius expansion, then combine with exact attainment. | **Passed, computer-assisted theorem.** Hand monotone-radius transfer preserves every originally feasible signed separator. |
| G9: global equality | Trace equality through the cover and recover all original eight-square attaining poses, with converse feasibility. | **Open.** The final dual determines captured exterior equality; radial pullback and the central square need a separate argument. |
| H: hand conversion and final audit | Replace every retained computational premise by analytic inequalities and audit all boundaries, ties and dependencies. | **ACTIVE.** Central core, global pair/capture inequalities, and finite terminal arithmetic remain to be replaced. |

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
\frac{\mu_H}{2}(t-t_*)^2+
\frac12\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2+
\frac{13}{2500}S\ge q_*.
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
| H1: central core | Prove the strict marker separation for every sorted square state with primary coordinate at least 5/12, including shallow central squares. | The [circular-cap lemma](HUMAN_CIRCULAR_CAP_AND_AXIS_ELIMINATION.md) eliminates outward-primary separators by hand. Remaining angular marker cases are active. |
| H2: global geometry | Replace the four-type, excluded-word and 123 capture pair inequalities by tractable contact-envelope inequalities and an exhaustive geometric argument. | The cap lemma also removes exterior outward axes. Low-degree potentials and a shared finite transition argument are being investigated; discovery fits are not counted as proofs. |
| H3: terminal constants | Give a hand-verifiable proof of the broad stationary, slider, weight and owner inequalities. | Exact force identities reduce 32 owner assignments to nine scalar inequalities. Monotonicity reduces the stationary graph to rational endpoint comparisons. Analytic presentation is in progress. |
| H4: assembly audit | Substitute the completed hand lemmas into the unrestricted argument and check all ties, boundaries, signs and radius transfers. | Waits for H1–H3; the existing computer-assisted assembly is preserved as a completed reference. |

**Next required exit:** a complete analytic replacement for the retained
global and local arithmetic premises. The hand-proof gate stays open until
that replacement is written and checked; the computer-assisted result is
not relabeled as a hand proof.

