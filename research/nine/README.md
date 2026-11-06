# Nine squares: pen-and-paper proof in progress

The target is to prove that nine independently oriented unit squares with
disjoint interiors require a containing radius of at least
\(\sqrt{1105}/16\). An exact packing attains this radius. **The unrestricted
lower bound and the classification of all equality packings remain open.**

The present task is a pen-and-paper proof, with explicit finite tables where
useful. Lean work is deferred. Numerical searches, certificate replay and
archived success reports are not steps in the proposed paper proof.

**Actual-and-cone four-chain with a disjoint cone three-chain: CLOSED
at the manuscript level.** The [complete (1,3,1) chapter](ACTUAL_FOUR_131.md)
finishes the last occupancy type and assembles all six counts, up to
horizontal reflection, in its Section 9. Thus every selected witness
`000/**` is excluded: the three main links are actual, while either
short link may still be weak. This includes the previously completed
[(2,2,1) directive](ACTIVE_221_DIRECTIVE.md).

The [independent coverage review](ACTUAL_CONE_COVERAGE_REVIEW.md) checks
the assembly, normalization, caller hypotheses and boundaries. It is not
a new independent verification of every supporting scalar argument.
The unrestricted extraction gives only cone links; a weak main link
therefore remains a genuine unresolved case, and the unrestricted theorem
remains open.

Read these documents in order:

1. [Proof draft](PROOF.md): the physical model, attaining construction,
   weighted endpoint inequality, and the exact missing implication.
2. [Proof plan](PROOF_PLAN.md): complete mathematical milestones and the
   standard for a usable table.
3. [Physical-and-cap foundation](FOUNDATION.md): the complete physical
   preliminaries, weighted two-square cap, endpoint criterion, directional
   center capture and sharp three-square half-plane cap, including their
   scalar tables and terminal equality arguments.
4. [Five-square cap](FIVE_SQUARE_CAP.md) and its
   [outer-envelope proof](FIVE_SQUARE_CAP_OUTER.md): a complete hand
   terminal coupling two far endpoints to three upper originals,
   with every separating direction, strictness and its own equality
   family. The outer and central interval tables have been replaced
   by explicit analytic arguments.
5. [Exhaustive extraction](EXTRACTION.md): the complete cone-chain height
   bound, precise Greene input, rotating-rank proof and all-nine diagonal
   event cover, including persistent height four and simultaneous ties.
6. [Actual-four-chain analysis](ACTUAL_FOUR_CHAIN.md): the fixed all-nine
   domain, a stronger endpoint budget, the common central band, and the
   precise surviving geometric implication. Its Section 4.3 links the
   complete [full-side theorem](ACTUAL_FOUR_FULL_SIDES.md),
   [one-sided occupancy theorem](ACTUAL_FOUR_230.md),
   [four-central occupancy theorem](ACTUAL_FOUR_140.md),
   [complete (2,2,1) occupancy theorem](ACTUAL_FOUR_221.md),
   [complete (1,3,1) theorem and six-count assembly](ACTUAL_FOUR_131.md),
   [two-upper-central caller and reusable floor lemmas](ACTUAL_FOUR_CONE_TRIPLES.md),
   and [central-height exclusions](ACTUAL_FOUR_CENTRAL_BOUNDS.md).
7. [Review of the earlier work](AUDIT.md): what to reuse, what failed, and
   what the old completion counts mean.
8. [Mathematical sources](sources/README.md): the retained arguments and
   exact examples. Dated status remarks in these sources describe their
   original checkpoints; this page and the proof plan describe current work.
9. [Archive and recovery](ARCHIVE.md): the immutable snapshot containing
   the old graph campaign, computational certificates, scripts and handoffs.

The most useful existing argument is the
[physical two-square cap](sources/PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md).
Applying it at two ends bounds a weighted span of four original squares.
Actual projection chains of lengths four and three reach that bound, but
they are only one possible way to do so. The new draft makes the more general
endpoint criterion explicit.

The main difficulty is to connect **all nine original squares** to a sharp
criterion. The existing rotating-frame argument supplies center-cone chains,
whose consecutive links need not be projection-separated. The two omitted
squares cannot both be discarded: an
[explicit rational table](sources/SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md)
realizes every remaining historical mask with seven squares strictly below
the proposed radius.

For the current `001/00` frontier, a new
[hand bound on the inner frame and downward cone](00100_INNER_FRAME_AND_DOWNWARD_CONE.md)
gives h_B<259/480 and canonical |t_B|<1/12. It also excludes the entire
Cb882 halfspace y_B<=-67/120. The needed nonpositive-D C-slant input
is now proved by the three hand/table chapters below.
The complementary Cb882 domain and every whole-original closure remain
open; this adds no completed cell or mask. The new argument prints its
rational arithmetic; its [second-agent review](CB882_HAND_REVIEW.md)
checks the physical implications and exact constants.

The [C-slant primary-axis chapter](00100_C_SLANT_PRIMARY_AXES.md) now
replaces the primary-axis part for nonpositive D with direct hand
inequalities and a complete 67-rectangle rational table. It uses the
foundation's physical pair cap, without importing C-slant or G-order.
The [upper-G secondary-axis chapter](00100_C_SLANT_SECONDARY_AXES.md)
prints every rational coefficient rule and all 4,204 terminal combinations.
The [lower-G complement](00100_C_SLANT_LOWER_COMPLEMENT.md) supplies
all 1,039 remaining terminal combinations and the complete acyclic
assembly. Together these prove C-slant for nonpositive D without the
archived C-slant or G-order forests. Their full covers and rational
arithmetic have received an [independent second-agent reconstruction](CB882_HAND_REVIEW.md),
including all 5,243 printed leaves.
Positive-D C-slant, whole-original exclusions, and the unrestricted
theorem remain open.

The new [endpoint-inset lemma](00100_ENDPOINT_INSETS_ARE_VERTICAL.md)
proves that both A/E and D/G must separate vertically through their
actual contained insets throughout `001/00`. The A/E argument excludes
the complete forward horizontal case by one physical pair cap and two
short rational polynomial estimates. It uses only seven originals and
requires neither C-slant nor a tilt-sign or height-order hypothesis.

For the complete Cb882 caller, the
[G-order theorem](CB882_G_ABOVE_D.md) now rules out G below D by
two rational estimates. A universal actual-square clearance bound,
|c_P-c_T|>=1+|h_P-h_T|, supplies the key comparison. The
[downward-cone localization](CB882_GEOMETRIC_REDUCTION.md) gives
x_H<-1/40, and the [A/E routing theorem](CB882_E_DOWN_ROUTING.md)
proves y_A-g_A<-1/4 and reduces the E-below-A physical separator
to three owned axes. E below A and the whole original remain open.

For the whole Cb882 attempt, a new
[sharp local terminal](CB882_LOCAL_SHARP_TERMINAL.md) uses the actual
AB and EFG links and four original boundary corners. Its continuous
weighted argument covers the closed-Q boundary, including the freedom
to lower B, and contradicts the original strict weak CD bit. It needs
no endpoint tilt-toll theorem or archived certificate. The complete
complement of its stated local guard remains a whole-cell obligation;
the terminal alone closes no original or mask.

The foundation and extraction gates G1–G2 are complete at the manuscript
level and have received independent reading. Greene's finite-poset theorem
is stated exactly and remains an explicit classical dependency. These
chapters settle the proof inputs and coverage; the unrestricted geometric
closure is still open. The complete five-square cap strengthens the
available terminals and the surviving actual-four-chain predicate.
All outsider occupancy domains are now excluded when the same main chain
is actual and cone, with a disjoint outsider cone triple. The weak-main
domains and the unrestricted actual-four domain without those cone
hypotheses remain explicit.
Earlier computational results remain available in
Git history; they are not silently promoted to self-contained paper proofs.
