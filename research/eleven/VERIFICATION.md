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
```

All four commands passed on 23 October 2026. They have different scopes:

| Command | Exact checked output | Scope limit |
| --- | --- | --- |
| Rational witness | 11 unit frames, 44 corner bounds, 55 pair separators at U=49013/10000 | One feasible packing |
| Contact root | Strict interval self-map and contraction; local root uniqueness; 34 inactive corners and 39 inactive pairs | Ten corner and fourteen pair identities are proved algebraically in the note; two more pairs follow from the slider domain |
| Oblique witness | Positive shared-edge lengths and an oblique forced normal | Refutes common-frame coverage of this family; no global sharpness |
| Rank inventory | 4296 -> 1359 -> 1155 -> 1105 masks; all nine profile-pair counts | Necessary masks under the common-coordinate hypothesis; no realizability or sharp-bound conclusion |

The interval checker uses exact rational endpoint arithmetic and integer
square roots; floating-point conversions only print diagnostics. It refuses
optimized Python execution that would disable assertions. The contraction
argument and the meaning of all omitted exact identities are written in
`CANDIDATE_CONTACT_SYSTEM.md`.

## Independent review and artifact binding

`CONTACT_ROOT_REVIEW.md` records the independent contact-family audit and
hashes of its four inputs. The reviewer checked the interval operations,
derivative domains, Banach hypotheses, all exact contacts and the 39 inactive
pair constraints with a distinct vertex-projection calculation.

The simpler rational witness was independently checked by reconstructing all
vertices and projecting them, with all printed coordinates compared to JSON.
The rank arguments and counts received separate mathematical and enumeration
reviews. The all-angle double-four-chain inequality was checked for both
endpoint order signs. The obstruction proof was reviewed with weak contact
and slider endpoints retained.

`MANIFEST.json` binds the 14 critical proof, data and checker artifacts by
SHA-256. The contact-review hashes and every local Markdown target were
checked against the final local files. Research method/scope labels were
reconciled in the current roadmap; historical intermediate counts remain only
as history or named reduction stages.

## Remaining verification boundary

This is a partial research handoff. G2.4, the 1105 residual coordinate
geometric domains, unrestricted oblique extraction, all required sharp
terminal inequalities and complete equality are still open. The local root
construction does not establish even local optimality among unrestricted
perturbations. No certificate here proves the global n=11 lower bound.

G7's **full** hand-proof audit remains blocked by those mathematical gaps.
The reviews above close only their stated artifact scopes. Future Lean
translation, compilation, axiom/import audits and public integration remain
G8–G9 and are outside the current no-Lean phase.
