# n=9: current status and the fixed closure queue

## Latest continuation — free-inner-height terminal; full domain still open

The [new hand theorem](computer_assisted/ACTUAL_FOUR_FREE_INNER_HEIGHT_TERMINAL.md) removes all height and tilt guards on the two inner squares of an actual four-chain. It proves a sharp terminal from explicit bounds on five other tilts and one central-square height, with all physical separator owners retained. Its pen-and-paper proof reduces to three positive rational inequalities. The [separate exact checker](computer_assisted/verify_free_inner_terminal.py) passed both polynomial identities, all scalar bounds, three parameter rows, 90 supplementary signed layers, and two corruption controls.

**This is not full-domain coverage.** The remaining five tilt guards and central height floor have not been derived for every `000/01` packing. There are zero new full-mask closures and zero new canonical-root exclusions. The same fixed target and ledger remain.

Solver availability was resolved: the installed Z3 4.13.3 shared library runs through `computer_assisted/z3_ctypes.py`. Five pinned rational SAT/UNSAT controls passed. The unrestricted nine-square query and a strengthened query both returned UNKNOWN due to their recorded time limits. An unfinished floating-point joint-center/frame search is preserved as discovery work, not a proof certificate. See the [complete continuation record](computer_assisted/CONTINUATION_FREE_INNER_HEIGHT_AND_SOLVER.md).

**Unrestricted lower bound: OPEN. Full equality: OPEN. Final manuscript: OPEN.**

Current method: computer-assisted discovery and exact arithmetic checking, followed by a complete pen-and-paper/table argument. No Lean, Lake, or CI. Floating-point optimizer failures and unsupported solver answers are not exclusions.

[Closure contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md) · [Fixed mask table](gates/A2_MASK_FRONTIER.json) · [Roadmap](DEEP_GATED_ROADMAP.md) · [Registry](gates/ACTIVE_ROADMAP.json) · [Current handoff](HANDOFF_A2_FIXED_CLOSURE.md)

## Previous computer-first continuation — fixed-pose pilot, not global closure

The [58-leaf exact no-eighth table](computer_assisted/NO_EIGHTH_FIXED_SEVEN_HAND_TABLE.md), independently regenerated and checked by `computer_assisted/make_no_eighth_certificate.py` and `computer_assisted/verify_no_eighth_certificate.py`, proves that the one fixed seven-square rational negative control cannot accept an eighth square at or below Q. Its 58 rational center boxes have maximum depth 13, and its final oblique-square cap has squared-distance margin `518311/70560000`. This is a fixed-pose theorem, not a closure for a moving nine-square mask or canonical positional root.

`computer_assisted/emit_fixed_mask.py` emits the exact degree-two QF_NRA predicate for all nine moving physical squares and the entire `000/01` domain (45 real variables; 36 pair predicates; 36 corner tests; no square-0 horizontal gauge). Its original exact assertion controls passed. The old statement that no nonlinear solver could run is superseded by the shared-library execution above. No global UNSAT certificate exists.

The pilot and emitter added zero complete mask closures and zero root exclusions. A certificate must close the complete moving domain; the pilot is not a global caller.

## Whole-domain hand attempt: 000/01 remains OPEN / BLOCKED

[Attempt record](A2_000_01_ATTEMPT.md). The selected short chain has been routed to one common side of the two inner mains by a uniform physical argument. The weighted endpoint caps then leave an exact outer-square orientation deficit; no proof yet shows that the two additional units eliminate it on the full domain.

An exact rational seven-unit packing with the same selected `000/01` links fits in squared radius 273/64<Q, with margin 13/256. All 21 physical pairs and all farthest-corner bounds are printed. The weak-link inset gap is attained exactly, and the selected seven already have two coordinate-exceptional pairs. This rules out the seven-square shortcut and an automatic one-exception invocation. It is not a nine-square counterexample and does not prove an eight-square shortcut.

No full mask or root was closed by that attempt. Its construction and identities have hand derivations. No independent human or kernel review is claimed for this continuation.

## The fixed-domain reset remains in force

The expanding conditional-lemma queue is frozen. Existing proofs remain available, but separator owners, slopes, marker positions, and successively stronger thresholds are not new progress gates. The active task must close a complete fixed domain, not merely add a sufficient condition.

The existing exhaustive cover was not missing. The missing result is a complete proof over its remaining continuous domains. The contract gives the exact all-nine-square mask predicates, every boundary convention, their coverage/assembly argument, and the rule for accepting a whole-domain proof. It does not claim that these proofs are easy or that research termination is guaranteed.

The reset closed zero geometric cases. It reconciled a stale registry that still recorded 31 untreated masks and described some subsequently published proofs as missing leads; no conditional result was promoted by that accounting correction.

## The two ledgers

| Ledger | Established baseline | Still open | Meaning |
|---|---:|---:|---|
| Original positional roots | 5,838 closed-Q exclusions | 2,077 | Historical published summary over 7,915 stable IDs; not rerun here |
| Fixed hand-proof masks | 2 complete strict-radius proofs | 30 | The same 32 masks, each quantified over all nine physical squares |

Neither row is a completion percentage. These are different covers and cannot be added together.

The original root counter measures exclusions even at q=Q. It must not be driven to zero: root 7820 contains an equality witness. A future proof of its q<Q obstruction is a strict-radius discharge, not a claim that its closed-Q physical domain is empty. No new per-root manifest or certificate is claimed.

## Exact active target

**Prove the full `000/01` domain impossible below Q=1105/256.** Its reversal partner `000/10` follows from the explicit coordinate-and-chain reversal in the contract.

This means an actual four-chain, a disjoint cone three-chain with its first link actual and last link weak, and two other physical squares. Keep all 36 original physical pair constraints and all 36 corners. No bound on other exceptional pairs, no chosen endpoint owner, no prescribed inner height, and no additional orientation restriction may be assumed without proof.

A universal actual-four-chain theorem would also close the remaining `000/11` domain and is welcome as a common proof. It is not an additional prerequisite. The current target is not claimed uniformly easy.

The next mathematical closure record must include the exact full row or stable root IDs discharged, the exhaustive argument, all terminal hypotheses, and boundary handling. An unfinished attempt leaves its target OPEN. A complete global terminal-extraction argument may discharge the entire frontier at once.

## Reusable results, not a separate queue

The physical 4+3 terminal closes `000/00`; the weak-middle terminal excludes `010/00` even at Q. The one-exception theorem, cap theorems, outsider bounds, endpoint transfers, perimeter inequalities, and new free-inner-height terminal are reusable conditional tools with their stated scopes. No new conditional-lemma campaign is scheduled by this ledger.

The original 15 roadmap IDs are unchanged. Full equality B.2/B.3, global assembly audit A.3, and final manuscript C.1/C.2 remain open. No independent human or kernel verification is newly claimed.

## Preserved history

The detailed pre-reset catalogue is pinned at
[ea4ff8b](https://github.com/vltanh/lean4-squares-in-circles/blob/ea4ff8bad97a58e2b8633ab69f549acb5352e573/research/nine/PROGRESS.md).
All mathematical manuscripts remain in the branch. Historical checkpoint and handoff files are evidence, not additional active instructions. No Lean files or CI configuration were changed in this continuation.
