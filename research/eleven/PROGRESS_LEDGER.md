# Eleven-square progress ledger

The [roadmap](DEEP_GATED_ROADMAP.md) is the current status authority. This
history records checkpoints without overwriting their original scope.
Commit timestamps and hashes are recorded after the commit exists.

## Initial roadmap checkpoint

- Base: main `4bea747b3efa13c869b956cb28435efaf21526fa`.
- G0.1 H: read repository physical semantics, PR #9 n=8 hand proof and
  roadmap, PR #10 source/verification distinction, and PR #11 n=9 residual
  coverage discipline through the GitHub connector.
- Added the full G0–G9 roadmap with separate exact-construction, raw-cover,
  reduced-classification, sharp-inequality, equality, audit, and Lean gates.
- No n=11 optimality claim. No Lean changes or Lean execution.
- Commit: `0a4a86e87c11a346a895c8d3c9a3c00a9c84041e`,
  2026-10-23 12:35:51 UTC. Draft PR #13 opened from this checkpoint.

## Exact feasible upper-bound checkpoint

- G1.1 H: elementary q=5 witness; tighter rational witness at
  U=49013/10000. All frames are exactly unit, all 44 vertices are contained,
  and all 55 pairs have an explicit separating own axis.
- G1.2.a H: pinned Friedman source credits Milan Kovacic, May 2006,
  with printed radius 2.21386+; its exact target and sharpness stay open.
- Validation: `python3 research/eleven/check_rational_witness.py` passed.
  An independent reviewer recomputed projection interval endpoints directly,
  checked all 11 printed coordinate rows against JSON, and found no gap.
- Independent minimum squared disk slack:
  229555019504308385673653663/2655897936042190250000000000000,
  greater than 1/20000. Minimum pair gap (7,8):
  64682720004556517/65138723819620100000000, greater than 1/2000000.
- Evidence: `EXACT_UPPER_BOUND.md`, `RATIONAL_WITNESS.json`, and
  `check_rational_witness.py`. This certifies one packing, not an optimality
  theorem, exact published contact system, or equality classification.
- Commit: `6ed9b0b2dac83413c3f54bb201fa1e59acf78105`,
  2026-10-23 12:38:04 UTC.

## Exact physical cover and compactness checkpoint

- G0.2–G0.4 H: four-corner containment equivalence, own-axis nonoverlap
  equivalence, orientation-sorted normalization, center bound, and compact
  minimizer existence.
- G2.1–G2.3 H: all 55 pair choices, eight signed owner axes per pair,
  and the exact 8^55 closed quadratic cell cover. Closed charts and overlap
  retain perpendicular/parallel frames, touching boundaries and owner ties.
- G4.1 H (generic): a completed-square stress identity conditional on
  supplied nonnegative weights; zero-loaded squares and equality residues
  are explicit. No sharp n=11 stress has been found.
- Review: separate mathematical audit checked the normalized support
  threshold, Minkowski-sum converse, compactness and dual signs; no
  substantive error found. No assumption of a common separating frame,
  a central square, or a boundary cycle enters the cover.
- Evidence: `FINITE_SEPARATOR_COVER.md`. The useful reduced cover G2.4,
  sharp terminal inequalities, and global equality remain open.
- Commit: `c61d57e1bad62bb1ec19f6d0aadbb9e17beae469`,
  2026-10-23 12:39:00 UTC.

## Coordinate rank and double-four-chain checkpoint

- G3.C1–C2 H: for the explicitly conditional common-coordinate-separable
  branch, projection ranks inject into (3,4), (4,3), or (4,4), with no empty
  rank. There are 4296 necessary labeled masks before geometric exclusions.
- G3.C3 partial closure: rank (4,4) is impossible in q<=5; two disjoint
  four-square projection chains in one direction force q>=5. The latter
  is an all-angle support theorem, sharp for an aligned 2 by 4 rectangle.
- At q<=U<5, all rectangular grids and double-full row/column profiles
  disappear. Exactly 1155 necessary square-grid masks remain explicitly
  listed. Their physical realizability and sharp inequalities are open.
- Independent review confirmed the support penalty including all signs,
  the independent left-to-right orders of endpoint pairs, and exact stage
  counts 4296 -> 1359 -> 1155.
- Evidence: `COORDINATE_RANK_CASES.md`, `classify_rank_masks.py`, and
  `RANK_MASKS.json`. The unrestricted oblique branch remains untouched.
- Commit: `26dcc73ce85721197f5ac38e075f72b2f86b4b53`,
  2026-10-23 12:46:10 UTC.

## Shared chain-start corner checkpoint

- G3.C3 further partial closure: the first row and first column cannot both
  be full. Their common square would start perpendicular four-chains and
  violate the unconditional center bound.
- This excludes 50 additional masks, leaving 1105, with row-profile counts
  225, 460, 420 for (4,3,3,1), (4,3,2,2), (3,3,3,2), respectively.
- Independent mathematical review and a separate finite enumeration agree
  on all stage counts and all nine row/column profile-pair counts.
- All 1105 residual geometric domains remain open, as does unrestricted
  oblique classification. No rank-grid reflection quotient is assumed.
- Commit: `55eac929af444b7dc8d73dfbae9f02beb67392d9`,
  2026-10-23 12:48:18 UTC.

## Exact contact-family existence checkpoint

- G1.2.b C: derive two exact radical equations for q and first half-angle t,
  with explicit centers, orientations, ten boundary vertices, fourteen pair
  contacts and one horizontal slider h in [H,a].
- G1.3 A: rational interval arithmetic and a written Banach argument isolate
  exactly one root in q=4.901206412408144±10^-9,
  t=0.2054740374066444±10^-9. All derivatives and divisions are valid on the
  whole box; no floating-point comparison is an acceptance input.
- Exact identities plus 34 remaining vertex inequalities, 39 remaining pair
  inequalities and both slider endpoint inequalities prove feasibility of
  the complete closed slider interval at that exact q_c.
- Independent review rechecked interval arithmetic, differentiation,
  contraction, all omitted algebraic identities, and residual pair intervals
  by a distinct vertex-projection calculation. Review hashes are recorded.
- G1.4 partial: q_c is the candidate sharp target. Neither local optimality
  under arbitrary perturbations nor unrestricted sharpness has been proved.
- Evidence: `CANDIDATE_CONTACT_SYSTEM.md`, `contact_family.py`,
  `isolate_contact_root.py`, and `CONTACT_ROOT_REVIEW.md`.
- Commit: `91ded8d69bdeb68b31358100e8c1c6d0da3c4660`,
  2026-10-23 12:50:41 UTC.

## Oblique obstruction and residual case ledger checkpoint

- G1.4.N1 H/A: the exact construction has two positive shared-edge contacts
  with mandatory separator normals ex and u=(c,s), c,s>0. No common
  orthogonal frame separates every pair, for any slider parameter.
- Exact interval bounds give the shared edge lengths >1/10 and >19/20;
  the shared-segment lemma supplies the geometric obstruction. Independent
  review found no missing weak-contact or slider-endpoint case.
- Added `TERMINAL_CASES.md`: four closed exclusion families, explicit
  domains for all 1105 residual masks, nine open profile families with
  independently reproduced counts, and the separate oblique frontier.
- Enhanced the mask inventory with exact row/column profile-pair counts.
  No additional masks were removed and none was declared realizable.
- Current-roadmap review found and clarified overlapping method/scope tags;
  no sharpness claim, stale current count, broken local link, or mismatched
  contact-review artifact hash was found.
- Commit: `1b182e43677068f76c7900ad0ca74a7640215856`,
  2026-10-23 12:54:20 UTC.

## Research verification checkpoint

- Reconciled the roadmap, exact candidate, case ledger and proof scopes.
  Final scope tags distinguish hand arguments, conditional results and exact
  arithmetic certificates; none implies kernel verification.
- Added `VERIFICATION.md` with the four successful exact replay commands
  and remaining proof boundary, plus `MANIFEST.json` binding 14 critical
  artifacts. All independent contact-review hashes and local links match.
- All 1105 residual coordinate masks and the oblique sharp-bound branch
  remain open. This is a partial research checkpoint, not G7 full closure.
- The commit carrying this entry is the verification checkpoint; its
  authoritative SHA and UTC timestamp are Git metadata, avoiding a circular
  self-hash entry. Future work should append them with its next checkpoint.


## Whole common-coordinate branch closure

- Previous verification checkpoint: `1b960b2b9cec92ce25cfd97cc0122b37558de92e`,
  2026-10-23 12:56:02 UTC. Continued under the instruction to seek a full
  proof without Lean.
- G3.C closed: independently oriented squares with common-coordinate
  separation shrink to axis-aligned squares in the same disk, preserving
  all selected coordinate separators.
- Thirteen fixed unit cells reduce axis-aligned eleven-square packings at
  q<=U to 28 hole pairs and six symmetry representatives. Half-open cells
  establish injection; closed cells and transported forced separators
  preserve every boundary case after reflection.
- Exact outward integer interval propagation excludes all six cases in
  32 nodes and 19 leaves. A separate Fraction replay uses simultaneous
  updates and rounding scale 10^6 instead of 10^8; it recomputes every
  contradiction and independently verifies the hole orbit cover.
- All 1105 earlier rank masks are closed by this stronger theorem. Any
  packing in the candidate radius window, including every minimizer,
  belongs to the unrestricted oblique branch. Global sharpness stays open.
- The stronger guess q>=5 for every axis-aligned packing is false; a
  separate exact feasible witness has q<4.91. It does not conflict with
  exclusion at U=4.9013. No such false global claim enters this proof.

## Candidate sharp stress and unrestricted local equality

- Previous common-coordinate closure commit: `fa4f0abbf0bdc9deb373ea45179f7ec33c93c76e`.
- G4.F H/A/C: exact interval Gaussian elimination proves the 24 by 24
  active-gradient matrix invertible and all 24 dual weights greater than
  1/100. A completed-square identity proves q>=q_c for arbitrary centers
  with the fixed candidate frames and fourteen specified separators.
- Equality recovers the eight loaded centers, the other two rigid centers,
  and the exact slider interval using physical nonoverlap.
- G4.L H/A: all nine parallel-contact angular flow margins exceed 1/100;
  fifteen alternative oblique axes fail strictly. The physical directional
  cone permits only sliding and common rotation at nonpositive radius cost.
  Removing these exact freedoms and taking a compactness limit proves an
  actual neighborhood theorem, including slider endpoints and local equality.
- Independent review checked every derivative, exact linear algebra, owner
  tie, flow sign, and the compactness argument; both checkers passed.
- The local neighborhood is existential. Global capture and all distant
  classes remain open; no stationarity-to-global inference is made.

## Unrestricted five-case radial extraction

- Previous local sharpness commit: `1c24400711421ca053331360b56c02b57cf18fae`.
- G2.4.a H: every square whose center norm is at least
  (sqrt(7)+1-sqrt(2))/2 occupies one connected auxiliary-circle arc of
  angular length at least 2 asin(1/(2sqrt(2))). Nine such arcs cannot fit.
- An elementary point-packing bound puts at most seven centers in the core
  disk. Exactly one of the five count rows (3,8) through (7,4) applies.
- The center ray lies inside each ring arc, proving a genuine cyclic order.
  Exact near/far side formulas retain all boundary cases. Area proves every
  core square strictly misses the containing circle.
- Two independent reviews checked arc derivatives, all endpoint branches,
  count bounds, cyclic ordering, and the closed-cover convention.
- All five sharp radial terminal problems remain open. No core-to-ring pair,
  ring nonneighbor, or unstressed square is removed.

## Refined rational core threshold and four exhaustive count rows

- Previous radial extraction commit: `c7ca971bed640dee1e5a172a032e62c2445592ae`.
- At the smaller threshold 41/40, every ring square contributes more than
  7/10 radians on the radius-27/20 auxiliary circle. All four exact
  side-branch differences have analytic lower bounds; rational Taylor
  estimates handle the near/far diagonal endpoints. There remain at most
  eight ring squares and at least three core squares.
- Independently, at most six nonoverlapping squares have centers within
  41/40. Six origin-avoiding squares would tile the unit circle in equal
  pi/3 arcs; their forced neighboring radial squares actually overlap.
  Thus a six-core case has exactly one origin-containing square.
- The current exhaustive rows are (3,8), (4,7), (5,6), (6,5). This changes
  the radial threshold; it does not assert that seven centers at the older,
  larger threshold were impossible. All four sharp terminal bounds remain
  open. Both independent analytic audit records are included.

## Actual minimizer stresses and exclusion of small contact components

- Previous rational core checkpoint: `96b7311332e3ab0d7321d9ff67bd88ba46803ef2`.
- G3.O2 H: a common strict direction for active constraints proves
  normalized nonnegative multipliers at an actual global minimizer.
  Strict owner selection for noncontacts makes every positive pair physical.
- Fixed frames admit at most 23 positive terms. A separate all-angle
  certificate uses at most 33 smooth support-vertex atoms, retaining
  parallel ties and torque equations. These counts are not conflated.
- The stress value is attained; a connected component can be retained and
  normalized, with bounded multipliers and the original disk as its unique
  minimum enclosing disk in its actual position. Every removed weight leaves
  the corresponding physical square present as a completion.
- An elementary center-shell theorem proves q>1469/400. Together with exact
  path and triangle comparisons, it excludes all stress components on at
  most three bodies. Components have 4 through 11 bodies, no unloaded leaf,
  and at most two internal unloaded degree-two transmitters per straight path.
- Independent audit passes all extraction, compactness, and exclusion
  arguments. No preexisting n=8 theorem is needed for this auxiliary bound.
- The remaining contact supports and their completions still need sharp
  bounds; bounded finite chart data alone does not close the global proof.

## The six-core geometric case is excluded

- Previous stress extraction commit: `55ea7a9e2475836ffbe1efde6fef4505a921b2c2`.
- A hypothetical six-square family with centers in the radius-41/40 disk
  has a unique origin-containing square. Its five neighbor rays are more
  than one radian apart. Center separation then pins the central center
  within 3/40 of the origin: otherwise all five rays lie in an arc shorter
  than four radians.
- The five centers lie within 11/10 of the central center and avoid its
  radius-1/2 offset. They must occupy four disjoint narrow coordinate
  regions. Two in the same region have distance squared below 17/20,
  contradicting disjoint inscribed radius-1/2 disks.
- This is a full all-orientation exclusion of six centers, including the
  closed threshold. Independent reviews agree; rational constants and
  Taylor residues were recomputed.
- The current global radial cases are exactly (3,8), (4,7), and (5,6).
  These three sharp terminal problems remain open.
