# Continuation: free-inner-height terminal and actual solver execution

Baseline: `5fd0452a965220b7f895ee7a3273a5590613a3d2`.

**No complete moving mask or canonical positional root was closed. A.2, the unrestricted lower bound, unrestricted equality, and the final global manuscript remain OPEN.** No Lean, Lake, or CI was run. No gate IDs or mask predicates were changed.

## Accepted mathematical result

`ACTUAL_FOUR_FREE_INNER_HEIGHT_TERMINAL.md` proves a new conditional sharp terminal with **no height or orientation guards on the two inner main squares**. It retains actual separation of the four-chain, unrestricted physical separator owners, all signs, and a potentially tilted upper triple. There is no assumption of a square-0 horizontal gauge.

For its stated endpoint/shoulder position bands, a central square C with |x_C|<=2/5 and y_C>=f suffices when the five squares M0,M3,L,C,R have |sin(theta)|<=b, where

    0<b<=1/18, 3/5<=f<=4/5,
    f > 11/24 + (51023/10800)b + (47/16)b^2 + (47/12)b^3.

The three displayed choices are (b,f)=(1/64,3/5), (1/32,2/3), (1/18,3/4).
The proof replaces an orientation case table by two triangle inequalities and three positive rational reserves. Its local equality consequence produces the actual four-plus-three terminal; it does not classify the other two units.

The separate standard-library checker reconstructs two polynomial identities, all rational majorants and three parameter rows, 90 supplementary signed layers, and rejects two algebraic corruptions. The report is `free_inner_terminal_verification.json`. This is independent arithmetic reconstruction, not an independent human/agent review or kernel verification.

The endpoint and selected shoulder bands follow from the existing `000/01` routing. Its P has |x_P|<2/5. **The necessary five tilt guards and central height floor are not proved on the entire domain.** C may also be one of the two unselected squares, but those same guards must then be established. The terminal cannot be counted as a full-mask closure.

## Solver availability corrected by execution

Although no z3py package or standalone solver executable was available, the runtime contained the Z3 4.13.3 shared library. `z3_ctypes.py` now runs SMT-LIB through that library, with explicit error handling. The earlier blanket statement that no nonlinear solver could be run is superseded.

`test_z3_fixed_mask_controls.py` fixes all variables to exact rational known configurations. Its five tests returned SAT for the strict seven-square control and the closed-Q nine-square equality witness, and UNSAT for the wrong actual edge, the strict equality witness, and the wrong weak edge. A separate malformed-input check was rejected. These are regression controls, not a global proof.

The unrestricted nine-square `000/01` formula was actually run with a 20,000 ms solver budget. It returned UNKNOWN, reason timeout; the raw output is preserved. A second query adding inherited center/routing bounds and the complement of the existing wide-slide terminal also returned UNKNOWN at the same budget. No nonlinear UNSAT certificate was obtained. `run_full_mask.py` reproduces the first query. The second query and exploratory workspace are preserved in the accompanying session archive, not represented as accepted proof data.

## Floating-point discovery, explicitly outside the proof boundary

An eight-square optimization batch (six starts) and a nine-square batch (twelve starts) approached Q from above. They neither prove impossibility nor provide exact new counterexamples.

A separate continuous-pose exploration used rational-form angle arcs evaluated in floating point, position polygons, coupled physical separator relaxations, all original physical pairs, shared center/frame linear constraints, the existing physical two-square cap, and guarded sharp terminals. The search was strengthened because pairwise compatibility alone can choose different center positions for different neighbors.

At the archived conflict-learning checkpoint it processed 5,056 exploratory nodes, recorded 1,525 floating-point LP conflicts/learned clauses, and still had 33 unprocessed frontier nodes. Those 33 nodes are search domains, not the 32 fixed masks. The frontier is incomplete; none of the floating-point conflicts has an independent exact Farkas replay. The counts are not certified exclusions, completion percentages, or evidence that the remaining search is small. The saved local archive includes the search code, graph, unfinished state, generated SMT-LIB, and raw numerical results.

## Unchanged closure obligation

Close the complete moving `000/01` strict-radius predicate, or prove an exhaustive routing of every assignment into valid sharp terminals, with every guard established and the entire complement covered. Reversal then supplies `000/10`. The fixed ledgers stay **2/32 complete masks** and **5,838/7,915 historical closed-Q root exclusions**. Root 7820's equality domain must not be falsely excluded. No new mandatory conditional-lemma queue is introduced.
