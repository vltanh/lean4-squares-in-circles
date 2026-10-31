# Fresh recovery review: original Packing compact minimum and G4.2.a

Date: October 29, 2026 UTC. Reviewer: shared_terminal, not an author of the
recovered proof or its prior review. Current comparison head:
`13ab63c00f6385151f882f10bc506dfd3920ddca`.

**Verdict: PASS for the entire original G4.2.a.** The proof starts from the
unchanged original finite Packing predicate, attains its global minimum
radius, and permits a finite continuous canonical refinement. The original
nine-square assertion is a direct specialization. No stress, contact-normal,
orientation, graph, angular chart, or load assumption is imported.

This is a new source-level review of recovered bytes, not a claim that a
historical unpublished ledger was already authoritative. No status file,
original identifier, Lean definition, CI action, or remote branch was changed
by this review.

## 1. Frozen payloads and actual current definitions

The following four files were recovered byte for byte from the prior local
`publication_structural_315` snapshot. Their historical dates, authors and
comparison head remain unchanged.

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | 15756 | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` |
| `REVIEW_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_COMPLETE_INDEPENDENT_BBC_2026_10_28.md` | 22755 | `65024715d38edd24c303c280ddbb5a4496044be04c5ab4a324d1de85e01f912c` |
| `INDEPENDENT_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_EXACT_RECORD_BBC_2026_10_28.json` | 21839 | `db06a50d9782dfe572783daa9699cc2923c6a4b62efbab72f6bdbdfd403639d4` |
| `ADOPTION_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_ROOT_BBC_2026_10_28.md` | 10757 | `27944a827a5ceaffd17e4cf4bfbe733be16963e5ff811adc72b9cf18c2d4cf85` |

I read the complete proof, complete independent review, complete historical
adoption, the current original roadmap statement, and all current Geometry
definitions consumed by the proof. The record is preserved as historical
support; I do not claim to have rerun its 27 finite algebra checks.

The actual current `SquaresInCircles/Geometry.lean` is 20319 bytes, SHA256
`64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94`,
exactly the definition blob pinned by the proof. Its UnitSquare uses a center
and an independent frame `(C,S),(-S,C)` with `C^2+S^2=1`. Its Packing retains
nonnegative radius, whole closed-square disk containment, and pairwise
absence of a common open-interior point. The definitions of openSquare,
closedSquare and Congruent are unchanged.

`SPARSE_MINIMIZER_STRESS.md` is 16597 bytes, SHA256
`b182276dace03bf64d9903145e8861022712b05f7ff7317ad62f30f97850e9ac`,
also matching the source pin. Its earlier compactness discussion is
provenance only. The present proof supplies its own full argument and does
not consume the later translational sparsity bound or a torque-stationary
certificate. No recursive stress audit is asserted here.

## 2. Closed original feasibility and globality

One common translation subtracts the actual containing-circle center from
every square center and every tested point. The two original local
coordinates and the disk displacement are unchanged. Translation back
supplies the converse. This is an exact equivalence on all original labels
and all independently rotated units, including every touching endpoint.

Given any feasible witness of radius R0, all translated feasible packings
with radius at most R0 belong to

    [0,R0] x product_i (closed disk D_R0 x S^1).

Every square center belongs to its own closed square, which justifies the
center bound. The full frame circle is compact without an angle cut. The
finite product is compact; for zero units the square-coordinate product is
the one-point empty product.

Whole closed-square containment is equivalent to the four continuous vertex
inequalities. The displayed four weights are nonnegative, sum to one, and
reconstruct every point with own coordinates in the closed half-side box.
Convexity of the closed disk proves sufficiency, with boundary weights zero
allowed.

Nonoverlap is closed directly in the original predicate. A fixed point in
two limit open interiors has a positive common margin in its four strict
local-coordinate inequalities. Continuity retains that same point in both
open interiors of every sufficiently late tuple, a contradiction. New side
or vertex contacts can appear at a limit; common open interior cannot. This
does not choose separating axes or assume a stable contact stratum.

The feasible subset is nonempty and closed in the compact product, so the
radius attains a minimum R*. This minimum is global: every original packing
with R<=R0 translates into the set; every one with R>R0 already has R>=R*.
All original radii are nonnegative, so squared-radius minimization is
equivalent. The artificial ceiling R0 is used only for the compactness
argument and adds no physical constraint to subsequent minimizer work.

## 3. Canonical refinement, endpoints and exact transfer scope

The full minimum-radius fiber is nonempty and compact. Successive minima of
any prescribed finite list of continuous real functionals exist on nested
compact fibers. In particular total center energy
`Phi=sum_i |c_i|^2` has a global minimum among all origin-translated original
radius minimizers. This choice occurs before any stress selection. No
infinite selector, discontinuous minimization, uniqueness, or common-frame
restriction is inferred.

A later Phi-motion argument must produce an actual Packing competitor for
all original units at the same radius and reduce the total Phi. Checking
only a stressed component is insufficient. A chosen stress need not be
preserved in this specific comparison, since every original feasible
packing belongs to the minimization domain.

The proof includes zero units and zero radius. For a nonempty family the
average of a square's four squared vertex norms is `|c|^2+1/2`, giving
`R^2>=1/2`. For two or more units equality forces every center to zero,
contradicting disjoint open interiors. All frame and physical touching
endpoints remain included.

An original subcritical packing of the actual nine units supplies its own
compactness ceiling and yields a canonical radius/Phi minimizer of nine
units at no larger radius. Thus excluding all such subcritical canonical
minima transfers a sharp lower bound to every original packing, with the
original circle center and independent frames allowed. The transfer is
conditional on that exclusion. Compactness does not supply the missing
sharp lower bound, a simultaneous stress selector, or a verified upper
witness.

Once a universal sharp lower bound has been established, each particular
equality packing is itself a radius minimizer. It need not be a Phi
minimizer. Replacing it by a canonical packing cannot classify the original
equality configuration. The source states this limitation correctly and
does not discard any unstressed body or change the original congruence
predicate.

## 4. Original-gate consequence

The unchanged original G4.2.a reads: start from the original nine-square
Packing predicate and obtain a compact minimizer with no extra orientation
or contact hypothesis. Sections 1--3 of the recovered proof establish this
entire assertion. Its n=9 specialization retains all nine physical units,
all labels, arbitrary circle center through exact translation, the full
independent frame circles, and every original open/closed condition.

I recommend adoption of precisely the existing original G4.2.a, one fine
update and no coarse-parent update. The conditional radius-transfer
corollaries do not by themselves close G4.2.f, whose sharp-bound premise is
still separate. G4.2.b, G4.2.c, G4.2.d, G4.2.e, the G4.2 parent, all equality
classification gates and the final global audit receive no credit here.

No repair was needed. This review uses continuous elementary compactness,
continuity and convexity, not a numerical pose sample, packing certificate,
Lean compilation, or CI run.
