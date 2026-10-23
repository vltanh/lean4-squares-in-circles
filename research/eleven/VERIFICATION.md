# Eleven-square research verification

This checkpoint contains hand arguments and exact arithmetic certificates.
It is not a Lean proof. No Lean source was written, no Lean or Lake command
was run, and the public n=1 through n=8 theorem files were not edited.
All PR changes are confined to `research/eleven/`.

## Reproducible certificate commands

Run in this directory with ordinary Python 3 and its standard library:

```sh
python3 check_rational_witness.py
python3 isolate_contact_root.py
python3 check_oblique_witness.py
python3 classify_rank_masks.py --check RANK_MASKS.json
python3 axis_exclusion.py --check AXIS_EXCLUSION.json
python3 replay_axis_exclusion.py AXIS_EXCLUSION.json
python3 check_fixed_orientation_stress.py
python3 check_local_angular_stress.py
python3 check_axis_terminal_graphs.py
python3 check_axis_counterexample.py
python3 arc_budget/check_weighted_arc_cover.py
python3 arc_budget/replay_weighted_arcs.py
python3 arc_budget/check_universal_bound.py
python3 arc_budget/replay_universal_bound.py
```

All fourteen commands passed on 23 October 2026. They have different scopes:

| Command | Exact checked output | Scope limit |
| --- | --- | --- |
| Rational witness | 11 unit frames, 44 corner bounds, 55 pair separators at U=49013/10000 | One feasible packing |
| Contact root | Strict interval self-map and contraction; local root uniqueness; 34 inactive corners and 39 inactive pairs | Ten corner and fourteen pair identities are proved algebraically in the note; two more pairs follow from the slider domain |
| Oblique witness | Positive shared-edge lengths and an oblique forced normal | Refutes common-frame coverage of this family; no global sharpness |
| Rank inventory | 4296 -> 1359 -> 1155 -> 1105 masks; all nine profile-pair counts | Intermediate necessary masks, now all excluded by the stronger axis theorem |

The interval checker uses exact rational endpoint arithmetic and integer
square roots; floating-point conversions only print diagnostics. It refuses
optimized Python execution that would disable assertions. The contraction
argument and the meaning of all omitted exact identities are written in
`CANDIDATE_CONTACT_SYSTEM.md`.

The two axis commands prove exclusion at U through six covering cases and
19 contradiction leaves. The replay imports no generator, uses Fraction
intervals at a different scale, and recomputes every leaf contradiction.
The terminal-graph replay additionally verifies all 19 leaves against three
written hand inequalities (10 stresses, 7 double chains, 2 forks). A separate
exact counterexample at q<4.91 prevents strengthening the exclusion to the
false whole-class bound q>=5.
The geometric cover and arithmetic soundness are proved in
`AXIS_ALIGNED_EXCLUSION.md`; shrinking handles independently rotated squares
under the common-frame hypothesis.

The two stress commands certify invertibility of the 24 by 24 active
Jacobian, positivity of all 24 weights, all nine strict angular flow margins,
and all fifteen alternative-axis failures for the oblique contacts. Their
written square-completion and compactness arguments prove conditional global
sharpness and unrestricted local sharpness, respectively.

## Independent review and artifact binding

`CONTACT_ROOT_REVIEW.md` records the independent contact-family audit and
hashes of its four inputs. The reviewer checked the interval operations,
derivative domains, Banach hypotheses, all exact contacts and the 39 inactive
pair constraints with a distinct vertex-projection calculation.

`CANDIDATE_STRESS_REVIEW.md` audits the partial derivatives, interval Gaussian
elimination, equality reconstruction, physical owner-switch derivative, exact
flow identities, and the transverse compactness proof of local optimality.

The simpler rational witness was independently checked by reconstructing all
vertices and projecting them, with all printed coordinates compared to JSON.
The rank arguments and counts received separate mathematical and enumeration
reviews. The all-angle double-four-chain inequality was checked for both
endpoint order signs. The obstruction proof was reviewed with weak contact
and slider endpoints retained.

`MANIFEST.json` binds the listed critical proof, data and checker artifacts by
SHA-256. The contact-review hashes and every local Markdown target were
checked against the final local files. Research method/scope labels were
reconciled in the current roadmap; historical intermediate counts remain only
as history or named reduction stages.

The radial extraction is an analytic hand proof, separately reviewed: own-frame
circle intersections cover every near/far side branch; derivative
factorizations bound their arc lengths; exact angular counts give at least
three and at most seven core centers. The refined rational threshold 41/40
gives at most six core centers, with a unique origin-containing square
when there are six. A further analytic argument excludes six altogether:
`FIVE_CORE_REVIEW.md` verifies the center pinning and four-region contradiction.
`CORE_RING_REVIEW.md` and `RATIONAL_CORE_REVIEW.md`
bind the independent reviews. Area makes all core squares strictly
circle-unloaded. No sampled angle table is a premise.

`SPARSE_STRESS_REVIEW.md` audits extraction from a global minimizer, the
strict direction, fixed-frame versus angular counts, bounded multipliers,
component normalization, physical-contact witnesses, small-component
exclusions, and retained completions. These are analytic results.

The two weighted-arc replays check complete continuous pose covers, with
4,790 nodes and 2,037 accepted arc leaves. The second imports neither the
generator nor its arithmetic library, uses a different square-root scale and
arcsine reduction, and recomputes every domain test and leaf bound.
`arc_budget/WEIGHTED_ARC_INDEPENDENT_REVIEW.md` binds the mathematical and
source audit; `arc_budget/SECOND_REPLAY.md` records the separate execution.
Together the bounds exclude five or more core centers.

The five-circle universal lower bound q>9/2 has its own 2,385-node
continuous pose cover. Both arithmetic implementations pass all 980
accepted leaves; `arc_budget/UNIVERSAL_BOUND_REVIEW.md` records the
independent proof and source review. This bound is global but not sharp.

## Remaining verification boundary

This is a partial research handoff. G2.4.b–c, the sharp refinement of the two unrestricted radial classes, the remaining sharp
terminal inequalities and complete equality are still open. The candidate family is now proved locally optimal under unrestricted
perturbations, with complete local equality. No certificate here proves the
global n=11 lower bound.

G7's **full** hand-proof audit remains blocked by those mathematical gaps.
The reviews above close only their stated artifact scopes. Future Lean
translation, compilation, axiom/import audits and public integration remain
G8–G9 and are outside the current no-Lean phase.

## Full grouped-angle terminal

Run `python3 check_angle_neighborhood.py`, `python3 check_angle_tiles.py`,
and `python3 check_reverse_angle_tiles.py` from this directory. The first
checks four exact positive dual stresses and their uniform Hessian bounds.
The last two replay all 507 closed rectangles over both angle orders,
including zero cosines and equal-angle boundaries. The three reviews
`ANGLE_NEIGHBORHOOD_REVIEW.md`, `ORDERED_ANGLE_COVER_REVIEW.md`, and
`FULL_ANGLE_COVER_REVIEW.md` bind the mathematical, source and execution
audits. These certify the specified fourteen-separator contact class;
unrestricted capture remains open.
