# Gated roadmap for a pen-and-paper proof

The target is the unrestricted sharp bound \(R^2\ge1105/256\), with the
explicit attaining packing in [the proof draft](PROOF.md). The current work
is mathematical exposition and proof. Lean, numerical searches and replay
infrastructure are deferred. The eventual proof, including every finite
table, must be checkable from the manuscript and its stated mathematical
inputs, without external scripts or archived certificate data. State each
cited mathematical input precisely and track it as a dependency for later
Lean formalization.

## Complete actual-and-cone four-plus-three domain

**CLOSED at the manuscript level:** nine original squares below the
target radius cannot contain a horizontal four-chain whose links are
both actual and center-cone, together with a disjoint horizontal
center-cone three-chain. The [complete (1,3,1) chapter](ACTUAL_FOUR_131.md)
finishes the outsider occupancy proof and assembles its six exhaustive
counts, up to reflection, in Section 9. Neither short-chain link needs
actual projection separation. Thus all four strict witness domains
`000/00`, `000/01`, `000/10`, and `000/11` are excluded.

The [independent coverage review](ACTUAL_CONE_COVERAGE_REVIEW.md) checks
the six-count assembly, normalization and local caller guards. It does not
claim an independent recheck of every inherited scalar proof. The remaining
global task is to route witnesses with a weak main link; the extraction
does not itself supply actual links. G3--G5 remain open for the unrestricted
domains specified below.

## Earlier fixed target resolution

**CLOSED:** the complete (2,2,1) domain in
[ACTIVE_221_DIRECTIVE.md](ACTIVE_221_DIRECTIVE.md) is excluded by
[ACTUAL_FOUR_221.md](ACTUAL_FOUR_221.md). That single manuscript includes
the complete bottom/middle/top cover, both central vertical counts and
their reflections, the low-right caller, both positive-central physical
directions, and the negative-central scalar contradiction. A sufficiently
small center expansion preserves the original occupancy. Every supporting
lemma has a stated use in that fixed target.

The geometric reductions, final scalar bounds, and complete caller cover
received independent hand reviews. No Lean compilation, CI, numerical
search, mathematical program, or certificate replay was used. This resolves
the fixed directive and its reflected (1,2,2) counterpart. G3--G5 and the
unrestricted theorem retain the open status stated below.

## Gates and acceptance criteria

These are fixed deliverables, not a percentage-complete estimate. A new
subcase, restored archive or conditional inequality does not close a gate.

| Gate | Current status | Pass condition | If it does not pass |
|---|---|---|---|
| G0. Scope and cleanup | Complete in the preceding cleanup | One target, one roadmap, reviewed archive boundary, working source links | Repair the documentation before more research |
| G1. Hand-proof foundation | Complete at the manuscript level: [foundation](FOUNDATION.md), independently read | One complete physical-and-cap chapter, with all scalar tables and an independent review | State the exact failing lemma; repair it without weakening its caller |
| G2. Exhaustive extraction | Complete at the manuscript level: [extraction](EXTRACTION.md), with Greene's theorem explicitly imported | Exact poset input, rotating-frame proof and event cover, including persistent height four and all boundary faces | Keep the missing implication named; do not assume actual chain separation |
| G3. Choose the all-nine route | Open; [actual-four-chain attempt and surviving predicate](ACTUAL_FOUR_CHAIN.md) recorded | One whole-domain attempt, with the stopping rule in Section 3, yields a complete useful hand theorem or an exact obstruction to the proposed stronger route | Record the full surviving predicate; revise the route before growing another case tree |
| G4. Unrestricted geometric closure | Open | Every hypothetical strict counterexample reaches a proved sharp criterion, with every original square and every alternative accounted for | Keep the global bound open; local exclusions do not pass this gate |
| G5. Paper assembly and audit | Open | Attainer plus unconditional lower bound in one acyclic manuscript, with independent checks of geometry, tables and endpoints | Repair the identified dependency or coverage gap |
| G6. Global equality | Follow-up after G5 | Necessary and sufficient equality families, with converse constructions and allowed symmetries | Retain only the equality statements actually proved |

G1 and G2 have been supplied and independently read. Their mathematical
contracts are recorded in the two chapters; G2 retains one explicitly stated
classical finite-poset input. These are paper-proof milestones, not Lean
verification or new unrestricted geometric exclusions. G3 now has their
precise theorem contracts; G4 depends on the selected route actually working.
An obstruction passes a **research decision** in G3, never the proof gate G4.
No gate promises a fixed running time or a guaranteed route to the theorem.
G5 completes the sharp-radius theorem; G6 is a separate classification task.

## 1. Completed foundation

[FOUNDATION.md](FOUNDATION.md) supplies this deliverable in one acyclic
chapter. It proves the physical preliminaries, the full weighted two-square
cap, the endpoint and weak-middle consequences, the directional center
capture, and the sharp three-square whole-half-plane cap. All five owner
alternatives, both signs of the normal, the four-interval rational table,
and the center-cap polynomial and rational anchors are printed. The
strict-radius and equality arguments are separate. Independent reading
checked the geometric reductions, scalar coverage and equality steps; the
center-cap polynomial and both anchor evaluations were also expanded by
hand. No Lean or computational proof check is asserted.

The chapter assembles the physical model, support formula, separating-axis
criterion, aligned inset, and center-radius bound. It retains independent
orientations and weak contacts throughout. Every replacement estimate must
be an inequality about the same originals, not a new packing whose extra
properties are transferred back without proof.

The two-square cap is proved in full, including its triangle
bounding-rectangle lemma, five owner cases, four-interval convexity table,
strictness and equality. Its weighted endpoint consequence is (2) of the
draft. The actual \(4+3\) chain theorem and the weak-middle case are short
applications. The three-square half-plane cap and its directional
center-cap input are proved in the same chapter.

**Delivered:** a complete, independently read terminal chapter. Its tables
contain every rational comparison. This reuses the strongest existing hand
work without importing a computational closure report.

The [five-square cap](FIVE_SQUARE_CAP.md) now extends these terminals.
It couples two far horizontal endpoints to three original upper squares:
the shoulders have center height at least \(3/5\), and the central
original has whole floor at least \(1/10\). The endpoint inward span
is at most two, strictly less below the target radius. The
[outer envelopes](FIVE_SQUARE_CAP_OUTER.md) cover all real separating
slopes and all original owners by hand. The central transfer likewise
has a complete analytic proof, including its degree-six positive-slope
polynomial and its negative reciprocal boundary. Both parts replace
their archived interval-certificate dependencies. The five-square
equality family is proved within this terminal's own domain.

## 2. Completed extraction and its named dependency

[EXTRACTION.md](EXTRACTION.md) supplies the geometric estimates, height
bound, rotating-rank argument and diagonal-event reduction. It states
Greene's finite-poset conjugate-partition theorem exactly, cites its original
paper, and proves the required nine-element specialization. The original
publisher's abstract and the author's bibliographic record were checked.
Independent reading checked the shortened five-chain contradiction, the
closed-comparison argument and every symmetry map. The imported Greene
theorem remains a dependency for eventual formalization; it is not silently
treated as a direct finite proof.

The center-cone extraction is the best existing unrestricted starting point.
Its poset argument invokes Greene's theorem: for the relevant nine-element
poset of height four and width at most four, there are disjoint chains of
sizes four and three, or disjoint antichains of those sizes. The short
partition calculation in the source is conditional on that theorem.

The exact cited theorem and its specialization now appear in Section 4 of
the extraction chapter. A self-contained replacement of that imported
combinatorial theorem would require a direct finite proof; none is claimed
here. The stated paper-proof acceptance criterion permits this precise
classical input. A future formalization must prove it or supply the direct
nine-element lemma.

The chapter retains the unconditional diagonal-event reduction. Mark one tied edge;
whole-chain reversal and a common reflection reduce its position and sign
to the following cover:

| Event type | Representative tied edge | Other data retained |
|---|---|---|
| Long-chain outer edge | AB | All five cone comparisons and all nine originals |
| Long-chain middle edge | BC | All five cone comparisons and all nine originals |
| Short-chain edge | EF | All five cone comparisons and all nine originals |

Section 7 of the extraction chapter writes the symmetry maps explicitly,
including both chains, both extras and every original frame. This table
covers event *types*, not finitely many positions. Multiple simultaneous
ties may belong to several rows.

**Delivered:** a complete extraction chapter with its finite-poset proof
or exact cited input, and its boundary conventions. Do not apply a
first-birth grid to the persistent height-four case. Do not apply
actual-four-chain estimates to a cone chain whose links are still weak.

## 3. Target one all-nine geometric implication

The first attempt is recorded in [ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md).
It keeps the original nine-square domain fixed. For an actual four-chain,
write \(U=h_0+h_3-1\) for the endpoint halfwidth excess, \(E\) for
the full inward endpoint span minus two, and \(S\) for the sum of the
absolute endpoint heights. The new necessary budget is
\(S+(37/50)U+(32/9)E\le1/8\), strictly below the proposed radius.
The pair caps force every other original to meet a common central band
of width \(1-(92/27)E\). These deductions have been independently read.
They do not close the domain: physical sections on the two boundary lines
can be short. Section 5 of that note records every surviving physical
constraint and the precise missing endpoint/cap implication. Accordingly
G3 remains open under the stopping rule below.

Section 4.2 of the same actual-four analysis now installs the complete
five-square cap as an additional proved terminal. The surviving
all-nine predicate must fail at least one of that caller's guards for
every eligible triple, on both vertical sides. This is a stronger
necessary condition; extracting such a triple throughout the domain
remains unproved and does not change the status of G3 or G4.

The completed [six-count assembly](ACTUAL_FOUR_131.md#9-complete-fixed-coverage-and-the-actual-cone-four-plus-three-corollary)
now excludes this entire domain when the same actual main chain also
satisfies its three cone comparisons and a disjoint outsider cone
three-chain is retained. Side capacity leaves, up to reflection, exactly
\((2,1,2),(2,2,1),(2,3,0),(1,3,1),(1,4,0),(0,5,0)\).
The first five have complete hand contradictions; the last contradicts
the selected cone triple's horizontal span. The
[coverage review](ACTUAL_CONE_COVERAGE_REVIEW.md) records the exact callers
and closed boundaries. The proof uses all nine originals and covers both
statuses of each selected short link. It leaves open the unrestricted
actual-four domain without the additional cone hypotheses and the
unrestricted extracted domain with a weak main link; it does not close G3.

Use the weighted endpoint quantity \(W\), rather than requiring every weak
edge to become an actual projection separation. Equation (3) of the draft
retains both the projection losses and the positive surpluses. The latter
may supply the compensation the earlier edge-by-edge approach loses.

The proposed global target is the explicit routing statement in Section 5
of the draft: obtain \(W\ge211/2\) for some endpoint choice and direction,
force three whole originals beyond the \(7/16\) cap line, or extract all
five-square cap hypotheses with endpoint inward span at least two. This
coverage remains unproved. Keep both omitted squares in the domain. Excluding the remaining
fixed masks requires some information involving an omitted original: an
exact seven-square realization exists for every such mask. This does not
prove that both extras are individually indispensable.

A strengthened no-actual-four shortcut has now been ruled out by an
[exact nine-square family](NO_ACTUAL_FOUR_NEAR_OPTIMAL_FAMILY.md): no
actual four-chain exists in any direction, but the squared radii approach
Q from above. Thus an exclusion based on that absence must be sharp;
a fixed gap above Q, including the proposed 9/2 threshold, is false.
The same family has actual outer main links and an actual short triple,
so the existing weak-middle terminal applies. An extraction of that
broader terminal remains a possible direction, with its coverage unproved.

Start with one complete geometric domain. The actual-four-chain domain is
a useful first candidate: its outsider strip, inner clearances and
two-per-side marker bounds are already hand arguments. Analyze all five
outsiders jointly, seeking an endpoint exchange or a three-square cap.
A proof that **every nine-square packing containing an actual four-chain**
meets a sharp terminal would compress several old computational assemblies.
That claim is new and open; the existing local lemmas do not establish it.

In a marked event domain without an actual four-chain, retain all-nine
physical inequalities, including the available relative-support and
point-to-incircle bounds. An endpoint exchange may use a different
direction. Specify the entire domain before trying a scalar inequality;
retain every failed guard's complement.

**Stopping rule:** first write one domain contract specifying all nine
originals, the radius assumption and the intended terminal conclusion.
Attempt the complete implication for that unchanged domain. Before opening
another case tree, write a reviewable result: a full hand proof, an exact
obstruction to a stated stronger routing claim, or the full surviving
predicate and precise missing inequality. The third outcome keeps G3 open.
Do not turn every failed attempt into a new mandatory subtree, or equate
another conditional lemma with a completed case.

The event reduction fixes the auxiliary witness angle from one center pair;
it does not discretize the physical poses or prove that this program will
finish. The archived mask method remains available if its inequalities
suggest a shorter proof. Its next numerical
leaf is not the default research objective.

## 4. Specify what a table proves

Each row needs the following information:

| Item | Required content |
|---|---|
| Domain | Exact interval endpoints, signs, owners and strict or weak boundaries |
| Physical input | The original-square inequalities and their derivations |
| Arithmetic | Explicit rational weights, coefficients or polynomial identity |
| Conclusion | The contradiction or a proved terminal with all hypotheses checked |
| Coverage | Why the rows cover the parent, including complements and shared faces |

A nonnegative combination of inequalities, a sum of explicit squares, or
a polynomial written with nonnegative coefficients on a stated interval is
a good row. Number reused lemmas so the dependency order is visible.
An archive path, a hash, a leaf count or a successful checker report cannot
stand in for the arithmetic.

Near equality, identify the zero set and prove a sharp inequality or a
separate equality argument there. Some full-nine closed-\(Q\) masks have
explicit feasible examples. Therefore a positive-reserve subdivision of
their closed relaxation need not finish, however fine the subdivision.

## 5. Assemble the lower bound, then classify equality

The completed paper should run from the physical model through the cap
lemmas and exhaustive extraction to the all-nine argument and conclusion.
Keep one list of genuinely open mathematical statements. Report complete
domain proofs, not numerical-worker counts, new folders or finer leaves.

Once the unrestricted lower bound is complete, trace equality through its
actual proof and verify the converse for every surviving family. The known
terminal equality cases and attaining examples do not yet give that global
classification.

The remaining order is therefore: one full all-nine geometric domain;
unrestricted assembly and paper audit; equality. The
[audit](AUDIT.md) explains why restarting the old graph census or finishing
seven cells of a single mask would not by itself accomplish this plan.
