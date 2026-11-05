# Complete physical trees for a registered B original

This document explains the proof rule used by a complete registered-B packet. A particular original is excluded only when its frozen `ORIGINAL_PROOF.json`, exact terminal table, and fresh portable replay all report a complete tree with no OPEN leaves. An OPEN prototype or a conditional branch proves no complete original.

## Physical caller and initial domain

The original labels remain A through I throughout. Each is a physical unit square, with center `(x_i,y_i)`, unit frame `(alpha_i,beta_i)`, and four original corners

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},\quad
y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

All 36 corners lie in the closed disk of squared radius `Q=1105/256`; all 36 original pairs have disjoint interiors. The marked actual pairs AB, BC, EF and FG, the five original center-cone conditions, and the strict weak CD condition remain part of the unchanged `001/00` caller. No square is replaced by a proxy or deleted.

An `angle_cut` in the records cuts the frame-slope coordinate `beta_i/alpha_i` used by the frozen original definitions. Its rational endpoints are not angles measured in radians.

The initial original is reconstructed from the frozen 231-original **definition source**, whose SHA256 is `ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604`. This historical source defines the original IDs and paths; it is not the current status ledger, which changes when other originals are accepted. The packet identifies the exact original ID and path, and final acceptance also compares that definition with the unchanged ID and path in the current register. The independent whole-domain checker accepts only this registered root followed by unconditional bound proofs and complete union-to-bound steps. It does not infer whole-domain coverage from a producer's scope label or from an arbitrary restricted branch.

## Exact bound induction

Every maintained position, frame-component, slope, or pair-difference interval is a necessary closed interval for the same physical caller. At each round the independent checker reconstructs all printed rows from that already certified state, then checks every rational multiplier and every claimed improvement. A numerical solver is used only to suggest multipliers and cuts.

For inequalities `c_k·z <= b_k` and rational nonnegative multipliers `w_k`, write `C=sum_k w_k c_k` and `B=sum_k w_k b_k`. If `|z_j|<=M_j`, then an objective `a·z` satisfies

\[
a\cdot z\le B+\sum_j M_j\,|C_j-a_j|.
\]

This pays every coefficient residual. In particular a terminal with

\[
-B-\sum_j M_j|C_j|>0
\]

is contradictory. Empty position, scalar, slope, or pair-difference intervals give a direct exact contradiction. The terminal table records either a positive rational lower bound on the residual reserve or the independently reconstructed non-affine terminal kind. A displayed floating LP infeasibility is never a terminal.

Analytic propagation uses the same physical unit-frame identity and the already proved intervals. Rows derived from position or frame rectangles are always reconstructed with those current certified intervals. A cached numerical cut contains parameters only; its coefficients are rebuilt for the caller, and the independent checker does not import the numerical runtime.

The accepted source packets retain the complete derivations for energy, area, support, coupled-three energy, physical Gram squares, adaptive original-corner disk rows, and unit-frame corner rows. The two Gram families expand nonnegative squares using existing physical products. A unit-frame corner row combines the exact expanded original-corner identity with a center squared-norm tangent and lower rectangle planes. In the four-product extension, each of four signed center/frame products independently chooses either its lower/lower or upper/upper matching endpoint plane. Every one of the 16 choices is valid on the same caller rectangle; these choices create no additional subdomains.

## Complete finite covers

Every internal node has an independently checked complete cover of its certified domain. The permitted branch rules are:

1. **Four inset alternatives.** Each physical square contains its certified axis-aligned centered inset. Their interiors are disjoint because the original squares have disjoint interiors. Thus for one Cartesian axis and one sign the signed center gap is at least the sum of the inset half-sizes. All four axis/sign alternatives are retained. The insets provide necessary inequalities while all original physical square predicates remain active.

2. **Eight physical separating alternatives.** For disjoint interiors of two convex squares, one of the two edge-normal axes of one of the two squares separates them, with one of two signs. The required projected gap is the sum of the exact half-supports of the two original squares. The owner, axis and sign yield eight alternatives, all of which are retained. Auxiliary products denote products of the original center and frame quantities; their interval and Gram inequalities are necessary consequences, not replacements for those physical meanings.

3. **Two closed angle intervals.** A rational cut `c` satisfies `lo<c<hi`, and the children retain `[lo,c]` and `[c,hi]`. Every other certified bound is inherited. The original cut face belongs to both children. A floating physical-corner diagnostic may choose `c`, but it supplies no inequality and no exclusion.

The checker requires the exact complete alternative set, correct parent attachment, identical original labels, and the appropriate inherited state for every child. Sibling exclusions are not assumptions of later siblings. Touching faces remain in the covers.

## Complete union-to-bound steps

A complete eight-alternative SAT union may strengthen the unsplit parent. The checker first replays all eight alternatives and their exclusions or deductions. For each shared original quantity, it takes the interval hull over every surviving child and intersects it with the prior parent interval. A quantity is joined only when every surviving child supplies the corresponding interval.

Only common original position, frame, slope, and pair-difference bounds cross this union. No child-specific SAT predicate or auxiliary product is carried to the unsplit parent. The original ID, path, and selected predicates remain those of the parent. If all eight alternatives are excluded, the complete union itself is excluded.

## Accepted sharp row terminals

A row terminal is permitted only when its exact physical guard is independently reconstructed from the current certified state and the accepted theorem sources are bound to the caller. The retained shared sharp theorem and full-angle row theorems use unchanged original labels, physical square supports, and the original marked conditions. Their closed-`Q` conclusion includes the strict-CD equality blocker. Any new literal label substitution requires its own accepted attachment; an unregistered row order cannot be introduced by editing the guard view in a proof.

The portable checker freshly replays the required scalar theorem and cap data on first use of a corresponding full-angle terminal. Merely finding a small floating height variation or a nearly axis-aligned LP frame does not satisfy a guard.

## Original exclusion and reproducibility

Induction on the finite tree proves every excluded node has no physical caller in its certified domain. At an internal node this follows from exclusion of every member of its complete cover. At the root, the independent whole-domain provenance proof establishes that this is the entire registered original. Hence a fully closed root excludes that original, including all shared and closed-disk boundary faces.

The portable replay verifies every packet input and every frozen prior input, uses explicit archive-relative path aliases, and forbids reads from the old workspace. It reconstructs the whole bound and cover graph using standard-library exact rational arithmetic, imports no numerical optimizer, and rehashes all inputs at completion. The final packet also retains the full literal terminal table and all bound records. No Lean, Lake, or CI execution is used by this replay.
