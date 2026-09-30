# Analytic n=6 finishing ledger

Baseline: `7a77bedec1772a2d9d78d49b47dc6d9f88a83cb3`, PR #7.
This continuation starts from `e2333407a1712620ccac93a81296b6c976abf2f6`.
Compilation remains deferred. Checked items mean written analytic source, not
compiler or kernel acceptance. No certificate, new axiom or changed Packing
predicate may discharge a geometric hypothesis.

## Source-index convention and corrected scope

Indices refer to `Stress.pairNormal` on the ordered pairs W/D and D/S:

| W/D index | D/S index | Geometric sources | Current status |
|---|---|---|---|
| 2 | 6 | W-secondary / S-secondary | Candidate graph |
| 6 | 2 | D-secondary / D-secondary | Analytically excluded |
| 6 | 6 | D-secondary / S-secondary | Mixed case still open |
| 2 | 2 | W-secondary / D-secondary | Mixed case still open |

**Correction:** the historical 53-cell hard table in
`Stress/FixedData/Hard.lean` has indices `(6,6)`, not `(6,2)`. The previous
ledger incorrectly said the OWN/OWN double-D-secondary proof replaced that
table. It does not. That proof is useful, but the 53-cell mixed-source
replacement remains a substantive open obligation. No theorem is changed by
this correction to the completion claim.

## Completed source foundations

- [x] Analytic normalization through `normalize_of_candidate`.
- [x] `FixedPair.lower_bound` on its explicit bit-dependent Domain, including the |n|/1000 reserve.
- [x] Actual N/W and E/S work, with the central-force correction and cancellation.
- [x] W/D primary and reverse-secondary exclusions; selected W/D source is 2 or 6.
- [x] Full-range existence of a forward secondary D/S separator — `SouthSecondaryComplete.lean`.

D/S existence uses a dominating secondary projection in some cases. It does
not assert that every possible primary separator is impossible when sources
can tie. This is sufficient for the intended source selection.

## Fixed-pair/diagonal connection

- [x] Correct negative-side line slope 18/25, rather than 73/100.
- [x] Cap branch keeps the required positive reserve after the slope change.
- [x] Vertex branch: analytic minorant and two geometrically forced quartic chords.
- [x] Corrected diagonal remainder: nonnegativity and unique zero on the explicit domain.
- [x] Actual candidate D-edge work matches the pair transverse residual.
- [x] Strict D support gives strict total work at a smaller radius.
- [x] `FixedCandidateClosure` proves angle/source/radius rigidity from ReductionHypotheses.
- [ ] Establish ReductionHypotheses for every normalized packing; the conditional closure does not do this.

## Analytic source and domain reductions

- [x] Canonical OWN W has negative deviation.
- [x] Low-diagonal OWN-W exclusion by frozen-center concavity and original corners.
- [x] Low-diagonal cardinal-W exclusion by rotating-length concavity and geometric vertices.
- [x] `normalized_diagonal_gt_half`: d>1/2 for both W bits.
- [x] Actual high-D radial and transverse bounds, including |bD|<229/1000.
- [x] Both D-sourced phase gaps exceed pi/4, sharpening the earlier 1/2 estimate — `SecondaryPhaseRestrictions.lean`, commit `31e853c`.
- [x] Consequently a noncandidate W/D edge requires w<d-pi/4; a noncandidate D/S edge requires s>d-pi/4.
- [x] The candidate W edge is automatic for w>=d-pi/4, and the candidate S edge for s<=d-pi/4, including the closed boundaries.

## Double-D-secondary exclusion — distinct from the hard mixed table

- [x] Whole-semicircle secondary-cost bound, including the genuine cap branch.
- [x] Exact cancellation of D with equal weights on its two secondary edges.
- [x] OWN/OWN case by affine costs and whole-domain wing bounds.
- [x] Cardinal/cardinal case by exact resultant lengths and the cos(pi/8) bound.
- [x] Both mixed central-bit cases by analytic depth reserves.
- [x] All four bit cases connected to the actual four separator inequalities.
- [x] Together with full D/S selection, at least one actual candidate wing separator exists.
- [ ] Exclude the `(6,6)` mixed D/S-sourced case, including the historical 53-cell region.
- [ ] Exclude the `(2,2)` mixed W/D-sourced case.

## Remaining unrestricted connections

- [ ] Derive both actual candidate D-edge inequalities over the full normalized domain.
- [ ] Derive the OWN W/S bounds required by FixedPair.Domain, or replace that envelope by one on the domain proved.
- [ ] Assemble those conclusions and d>1/2 into ReductionHypotheses.
- [ ] Switch the final closure away from old pair/fixed-row dependencies.
- [ ] Reconnect support equality, exact reconstruction and the recorded reflection.
- [ ] Review transitive dependencies of LowerBound, Uniqueness and public Optimum 6.
- [ ] Compile and execute the final kernel/axiom audit — deferred, not passed.

The new quarter-gap argument uses the existing analytic core-constrained
support lemma with the correct signed coordinates on each side of D. It
neither changes the phase ranges nor assumes the candidate edges. The two
mixed regions and their hard-table replacement are deliberately still open.
