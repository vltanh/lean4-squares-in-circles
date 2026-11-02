# Hand review of the nine-square continuation

Updated November 2, 2026. This records independent agent and integrating-agent hand
reviews of the stated mathematical arguments. It is not a kernel check or
an independent human review. No mathematical program is used as proof evidence.

## Accepted proof scopes

| Source | Reviewed conclusion | Remaining scope |
|---|---|---|
| `ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md` | Far-endpoint obstruction; exact outer-square orientation and common-point lemma; closed-Q exclusion of the hard distinct original rank grid | Does not cover every weak-four-chain configuration |
| `PATTERN_I_NINE_SQUARE_CONTINUATION.md` | All displayed rank reductions, duplicated-top exclusions, three/four/two normalization, aggregate support bound, far-endpoint uniqueness, and extra actual comparisons | Rank normalization assumes both original actual heights at most three |
| `PATTERN_I_COMMON_LOWER_CAP_HAND_PROOF.md` | Strict transfer cap and actual caller for right/down separator slope at most 27/46 | Steeper downward separators are outside this cap |
| `PATTERN_I_UPWARD_CAP_HAND_PROOF.md` | Strict transfer cap and actual caller for right/up separator slope at most 7/10 | Steeper upward separators are outside this cap |
| `PATTERN_II_NINE_SQUARE_CONTINUATION.md` | Exact four-chain endpoint budget, outsider strip and side capacities, complete one-middle closure | Used together with the complete complement analysis below |
| `BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md` | Complete Pattern II lower bound, including all five middle-occupancy counts and both two-middle exception placements | Requires an actual four-chain disjoint from both exceptional squares in a fat direction of that pair |
| `DOWNWARD_THREE_SQUARE_CAP_HAND_PROOF.md` | Complete E, N, D scalar bounds and strict downward transfer cap | Its lower-edge hypothesis must be derived by the caller |
| `UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md` | Uniform orientation reserve and strict upward transfer cap | Its matched vertical separation and lower-edge hypothesis remain explicit |
| `PATTERN_I_STEEP_UPWARD_HAND_PROOF.md` | All upward owned separators; both owners; signed-endpoint aggregate and explicit broader actual-comparison caller | Does not assume a global one-exception cover |
| `PATTERN_I_DOWNWARD_OWNER_EXTENSION_HAND_PROOF.md` | Both downward owners through slope 18/25, using the actual common lower square | Used with the middle-range and large-slope arguments |
| `PATTERN_I_STEEP_DOWNWARD_HAND_PROOF.md` | A-owned downward slopes from 21/10 and B-owned slopes from 13/4 | Vertical-span range lemma covers the intervening slopes |
| `PATTERN_I_ACTUAL_HEIGHT_FOUR_BRIDGE.md` | Every Pattern I with an actual four-chain in its fat direction reaches the sharp physical terminal | The chain need not initially be disjoint from the exceptional pair |
| `PATTERN_I_PERPENDICULAR_HEIGHT_FOUR_BRIDGE.md` | Every Pattern I with an actual perpendicular four-chain is settled, without perpendicular fatness | Uses the explicitly generalized signed upward caller |
| `PATTERN_I_HEIGHT_THREE_COMPLETE_HAND_PROOF.md` | All three original-height-three rank diagrams are settled | The height-four bridges supply the complementary scopes |
| `ONE_EXCEPTION_NINE_HAND_PROOF_2026_11_02.md` | Complete sharp lower bound for every orthogonal cover with at most one exceptional pair; all original height scopes joined | Unrestricted cover/extraction and wider equality classification remain open |

## Checks reconstructed independently

The transverse-grid review reconstructed the far-endpoint concavity,
both endpoint comparisons, the two chirality cases, the exact interval for
the outer halfwidth, and the inclusion of the fixed point
`(-59/60,1/3)` in the physical square's open interior. The final rank routing
uses actual comparisons; its last quadrant contradiction is `q>=41/9>Q`.

The Pattern I reviews reconstructed each permitted rank-column profile,
the treatment of a two-member column missing its former middle rank, and
the recomputation of longest-chain ranks after reflection. They checked
the negative-offset quadrant argument separately from the positive-offset
quadrant lemma. The far-endpoint uniqueness bound is the explicit support
inequality `q>157/36>Q`; it forces actual lower and upper neighbors of the
inner exceptional square in the normalized diagrams.

For the common-lower cap, the reviewers reconstructed the two support-vector
cancellations, the three minimum rectangle costs, convexity of the remaining
scalar function, and the endpoint reserve `241/25600`. For the upward cap,
they reconstructed the three edge-projection cases, the initial-interval
norm decrease, all second-derivative signs, and the exact endpoint margins
`7/400` and `3/400`.

For Pattern II, the reviews checked the endpoint-budget derivative and its
equality implications, the outsider-strip concavity, the side-column edge
bound, and every actual chain used in the occupancy cases. In the two-middle
case, the singleton-side exception needs the separate two-bottom-square
floor argument; that argument and its reflected caller were both checked.
The physical normal has positive x-component by the fat-direction inequality
and genuine vertical overlap, so neither separator sign is omitted.

The downward cap review reconstructed the finite integer identities in the
N branch, including `J=2PT_1`, all five coefficients of K, and the shifted
polynomial for `zJ-K`. It also reconstructed the D-branch quartic and its
positive endpoint comparison. The upward cap review checked both physical
orientation signs, both ranges in the orientation reserve proof, every
support-slope interval, and the final strict addition to the matched cap.

The integrating review also reopened the earlier physical two-square cap
theorem: its pair hypothesis is physical interior nonoverlap, without an
extra vertical-separation premise. The new narrower callers explicitly
derive the vertical comparisons they need for their own transfer inequalities.

The later reviews reconstructed the entire upward-sign completion, including
the two exact far-edge reserves, the B-owner quartic, the A-owner derivative,
and the actual supporting vertex used in the restricted-circle argument.
The independently signed endpoint-depth version was checked for both R/D
y-orders before its use in the perpendicular bridge. The downward owner
extension retains the exact side-normal support bound and B penalty; its
reserves are `1907/4800` and `1643/32000`. The steep downward review checked
both orientation cases of the outer-square directional bound and both owner
thresholds.

The original-height-three synthesis received three independent hand checks
in addition to its author's derivation. These reconstructed the universal
outer upper-edge bound `11/8`, its three corner cases, the shifted-inscribed-
corner rule, the lower-edge bound `-11/15`, and both branches of the split
at halfwidth `77/120`. The resulting V<2 condition is derived for the last
missing-top-left diagram, not assumed. The separator table covers all signs,
owners, slopes and shared interval endpoints.

Both original-height-four bridges received separate hand reviews. The
perpendicular proof's new endpoint extent `|x|+h<17/27`, coordinate-only
common-point use with a weak y-bound, rank-two routing, restored long span,
and final four-member-column exhaustion were all checked. The fat-direction
proof's reuse of the outsider strip was verified for an ordinary outsider
even when one exceptional square belongs to the actual chain.

Finally, an independent compositional review traced the initial fat-direction
choice through augmentation and Greene extraction. It checked the exact
Pattern II disjointness premise and the three exhaustive Pattern I height
possibilities. No remaining weak-endpoint or original-height scope is omitted
from the one-exception theorem. This compositional closure does not supply an
unrestricted frame-selection theorem.

## Method and accounting

One exploratory numerical optimization, with 48 starting points, tested a
possible three-square horizontal-cap direction during discovery. No output
from it is an accepted inequality, certificate, exhaustive case check, or
proof dependency. The results in the table above follow from the displayed
hand arguments alone. No proof program, Lean, Lake, or CI was run.

No claim below transfers a whole original positional root. The published
ledger therefore remains **7,915 roots: 5,838 excluded and 2,077 open**, with
the earlier archive-only 312 exclusions recorded separately. The same 15
roadmap IDs remain in use. Global A.2, unrestricted equality, and the complete
hand/table manuscript remain open.
