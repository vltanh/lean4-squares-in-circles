# n=9 — one global proof, no original progress counters

**Theorem still OPEN:** Prove that every set of nine independently oriented unit squares inside a disk satisfies `R²≥1105/256`. An attaining configuration at equality is already available. Then classify **all** equality packings. No "58 cases", "2,513 checkboxes", nested-case percentages or new gate fractions measure progress anymore.

**Current method:** exact computer-assisted discovery and independent proof certificate **first**; compact human proof or rational tables **later**. No Lean, Lake or CI.

## One proof objective and two alternative routes

```text
T  Original unrestricted nine-square statement and equality witness
C  Trusted exact numerical/algebraic proof checker
|
+-- D  DIRECT full nine-square semialgebraic route [PRIMARY]
|     D.1.a exact unrestricted 9-pose/36-corner/36-pair emitter  <-- ACTIVE
|     D.2   proved symmetry/reduction and complete real roots
|     D.3   finite proof-producing pilot with GO/NO-GO decision
|     D.4   certify impossibility for every q<Q
|
+-- S  Structural/stress route [FALLBACK]
      S.1 same selected certificate, all original contact terms
      S.2 old three-cut theorem as conditional SOURCE only
      S.3 four-cut, S.4 every other genuine physical case
      S.5 complete global nine-square argument

              (D.4 OR S.5) + checker C
                         |
                     Q  Sharp lower bound
                         |
                     E  Equality classification
                         |
                     H  Later hand/table proof
                         |
                     L  Later Lean (deferred)
```

A direct proof **does not require** closing any historical graph case. The stress fallback must cover all physical packings rather than accumulate partial source-family progress.

## Exact unrestricted packing predicate

Square i: center `c_i=(x_i,y_i)`, axes `u_i=(a_i,b_i)`, `v_i=(-b_i,a_i)`, `a_i²+b_i²=1`, corners `c_i+(s u_i+t v_i)/2` for `s,t=±1`. For `q=R²`, impose the **36** exact squared-corner bounds `||p_i(s,t)||²≤q`. For each of the **36** pairs i<j impose at least one separating axis `n∈{u_i,v_i,u_j,v_j}` satisfying
`|n·(c_j-c_i)|≥(|n·u_i|+|n·v_i|+|n·u_j|+|n·v_j|)/2`.
The separating-axis theorem for rectangles makes this equivalent to nonoverlapping interiors, including touching. Finite signed branches replace absolute values by exact polynomials.

The proof must exclude **all** solutions with `q<Q=1105/256` without fixing a positive `ε`. The q=Q known packing must remain feasible in the direct model. Direct formulation does not assume positive stresses, a contact graph, generic orientation, or circle-loaded corners.

## Stopping rule (prevents another endless case-expansion)

The next task is **D.1.a**: provide source and mathematical equivalence proof for the direct polynomial/SAT emitter. Then signed branch correctness and equality/invalid controls. The bounded pilot **D.3** must certify one genuinely nontrivial full-nine root using an independently checked exact proof *or* report a specific unresolved root and pivot to the S route. No unlimited microgate tree is allowed. Repeating numerical samples does not count as progress.

**Acceptance:** exact full root/degeneracy coverage, certified rational/algebraic terminal proof, an independent replay checker and a human-checkable implication to the original physical domain. All unresolved roots remain OPEN. A local theorem is evidence, **not percentage of the global goal**. Global necessity, then equality, are the only mathematical completion milestones.

## Full gated mathematical obligations

Each item has a precise exit; the number of items is **not** a progress fraction.

- **`T`** — Unrestricted nine-square sharp-radius statement, Q=1105/256. **Exit:** Correct exact physical predicate; final proof has no contact-graph or stress hypotheses.
  - **`T.1`** — Nine arbitrary independent unit-square poses in one radius-squared q disk. **Exit:** Each pose uses a unit axis pair; all four corners and all pairwise interior nonoverlap tested.
    - **`T.1.a`** — Represent all 9 centers and independent orthonormal square frames. **Exit:** No unproved generic orientations or global alignment.
    - **`T.1.b`** — Exactly 36 original corner norm-squared inequalities. **Exit:** Equivalent to entire-square disk containment by convexity.
    - **`T.1.c`** — Exactly 36 pairwise separating-axis disjunctions. **Exit:** All 4 candidate square-edge axes per pair, all weak touching boundaries.
  - **`T.2`** (REUSABLE INPUT) — Exact attaining packing at q=Q. **Exit:** Known algebraic construction tested by all unrestricted constraints. **Source:** Existing exact witness in earlier full physical model; recheck needed in new emitter..
- **`C`** — Trustworthy exact computer-assisted proof checker. **Exit:** Full original root coverage and every terminal implication independently verified.
  - **`C.1`** — Sound rational/algebraic interval arithmetic and positivity. **Exit:** Outward bounds and every polynomial/strict terminal reproduced without floating error.
    - **`C.1.a`** — Exact arithmetic kernel including integer square roots and denominators. **Exit:** No excluded zero or sign face and every certificate number checked.
    - **`C.1.b`** — Exact real algebraic/interval leaf proof encoding. **Exit:** Witness is finite and independently replayable.
  - **`C.2`** — Mathematically complete finite root and boundary coverage. **Exit:** Every physical candidate reaches at least one accepted leaf.
    - **`C.2.a`** — All signed absolute-value branches and SAT or owner alternatives. **Exit:** Complete branch disjunction with touching contacts and singularities.
    - **`C.2.b`** — Closed box splits, limiting faces and unresolved status. **Exit:** No missing child and no numerical cutoff counted as proof.
    - **`C.2.c`** — Uniform sharp q<Q verification. **Exit:** No fixed Q-epsilon bound or unproved extrapolation to critical radius.
  - **`C.3`** — Independent verifier and actual physical implication. **Exit:** Independent source reconstructs terminals and soundness of their use on all nine squares.
    - **`C.3.a`** — Known valid q=Q pose and deliberately invalid controls. **Exit:** Checker accepts equality witness and rejects overlap/out-of-disk perturbations.
    - **`C.3.b`** — Human theorem of checker/root/leaf soundness. **Exit:** The accepted certificate proves the claimed real packing proposition.
- **`D`** — PRIMARY: direct graph-free semialgebraic proof that no nine squares fit for q<Q. **Exit:** Exact complete proof or a documented pilot failure and explicit pivot.
  - **`D.1`** — Unrestricted nine-square exact polynomial/SAT emitter. **Exit:** Every original packing satisfies the emitter, and every emitter solution gives a real packing.
    - **`D.1.a`** **ACTIVE** — ACTIVE: implement exact 9-pose/36-corner/36-pair constraints. **Exit:** Deterministic real-algebraic formula and proof of equivalence; zero conditional stress hypotheses.
    - **`D.1.b`** — Expand SAT/abs to finite exact signed roots. **Exit:** Prove each signed root is sound and the union is exhaustive.
    - **`D.1.c`** — Exact equality and negative controls in direct model. **Exit:** Check q=Q attaining construction and deliberate overlap/corner failures.
    - **`D.1.d`** — Report actual direct formula dimensions/branch counts. **Exit:** Reproducible root count; no assumption that general CAD will finish.
  - **`D.2`** — Exact symmetry and domain reductions. **Exit:** Every removed original pose has a valid inverse representative.
    - **`D.2.a`** — Rotation/reflection/relabeling reductions. **Exit:** A proof each normalization is legal and leaves all equality families representable.
    - **`D.2.b`** — Useful analytic bounds from complete nine-square geometry. **Exit:** Do not import a selected-circle/multiplier restriction into the direct model.
    - **`D.2.c`** — Finite exact root partition with sharp q parameter. **Exit:** All roots and singular interfaces covered without fixing epsilon.
  - **`D.3`** — Bounded exact proof-producing solver pilot and GO/NO-GO. **Exit:** A fully certified nontrivial root or a documented unresolved obstruction and conscious pivot.
    - **`D.3.a`** — Select proof-producing QE/interval/SOS/real-algebraic method. **Exit:** Outputs exact replayable certificate, not just UNSAT or timeout.
    - **`D.3.b`** — Attempt one nontrivial exact full-nine root with q<Q. **Exit:** Close root with independent soundness and no unknown leaves, or retain exact open face.
    - **`D.3.c`** — Extract a reusable mathematical obstruction or terminate the pilot. **Exit:** No unlimited series of easier microcharts without a route to all roots.
  - **`D.4`** — Sharp direct global exclusion for all real q<Q. **Exit:** Every physical root has exact contradiction and checker accepts all leaves.
    - **`D.4.a`** — Full finite original-packing cover. **Exit:** No implicitly fixed contact graph, generic orientation or selected force system.
    - **`D.4.b`** — Uniform q→Q sharpness. **Exit:** Explicit all-q<Q proof, including arbitrarily near equality.
    - **`D.4.c`** — Independent complete certificate replay. **Exit:** All root/leaf/soundness conditions C fully discharged.
- **`S`** — FALLBACK structural/stress route, only if direct exact pilot stalls. **Exit:** One global full-nine proof, not a number of 'original cases' checked.
  - **`S.1`** — Global existence of ONE compatible selected force/normal/corner system. **Exit:** Every extremal physical packing admits a common certificate satisfying all source theorems.
    - **`S.1.a`** — Full original contact and actual circle-corner stationarity. **Exit:** No deleted nonzero stress, changed contact application or new mean.
    - **`S.1.b`** — Uncrossing, owner, common-certificate property (S) and all transfer assumptions. **Exit:** Every imported local exclusion applies to the same selected stress.
  - **`S.2`** (REUSABLE INPUT) — Reuse existing complete three-cut unloaded theorem only on its proven physical scope. **Exit:** No unloaded full-three-cut cyclic region under the one selected compatible certificate. **Source:** ADOPTION_COMPLETE_DIRECT_TRIANGLE_AND_THREE_CUT_FOREST_2026_11_01.md.
  - **`S.3`** — Complete four-cut physical exclusions/reductions. **Exit:** Exact table covers all full degrees, 4 exits, outside identities and nine actual squares.
    - **`S.3.a`** — Degree-(4,3,3) four-cut direct triangle probe. **Exit:** Common junction, shared sides, singleton owners and all independent A4 moments covered.
    - **`S.3.b`** — Other four-cut unicyclic and multicycle regions. **Exit:** Exhaustive real graph/mask classification or uniform exclusion.
  - **`S.4`** — All higher cut, loaded, branched/chorded and articulation configurations. **Exit:** Entire all-nine physical domain covered, not only stress-subgraphs.
  - **`S.5`** — Full mathematical sharpness and certificate integration. **Exit:** One independently reviewed argument excludes every physical q<Q packing.
- **`Q`** — Sharp global necessity theorem. **Exit:** Either complete D.4 or complete S.5 and exact soundness C imply q>=Q.
  - **`Q.1`** — Discharge one sufficient proof route (OR logic). **Exit:** D.4 OR S.5, not both, closes all unrestricted q<Q poses.
  - **`Q.2`** — Combine with exact attaining construction. **Exit:** Sharp optimal squared radius exactly 1105/256.
- **`E`** — Exhaustive equality classification q=Q. **Exit:** Every equality packing in exact families, and all listed family members physically feasible.
  - **`E.1`** — Classify q=Q original physical roots. **Exit:** No strict-only exclusion used to discard q=Q poses.
  - **`E.2`** — Derive all forced saturated constraints and parameter families. **Exit:** Necessary full-center/orientation/contact equalities.
  - **`E.3`** — Retain sliding degrees, endpoints, tangencies and zero multipliers. **Exit:** Exact semialgebraic allowed parameter ranges.
  - **`E.4`** — Prove sufficiency and quotient by actual symmetries. **Exit:** All nine squares satisfy 36 disk and 36 pair tests; correct iff theorem.
- **`H`** — LATER: readable hand proof or finite exact rational tables. **Exit:** A complete accepted exact computer-assisted result already exists before humanization.
  - **`H.1`** — Compress the certificate into case families and tables. **Exit:** Full root coverage, arithmetic signs and singular faces preserved.
  - **`H.2`** — Paper-level source proof with independent table check. **Exit:** Self-contained sharp theorem and equality, no trusted exploratory script.
- **`L`** (DEFERRED) — DEFERRED Lean/kernel/CI work. **Exit:** Only after permission; not a prerequisite for first complete exact proof.

## Historical work policy

Old 58/2,513/38 status trackers, refined-map archives, and duplicated historical checklists are removed from the current branch; Git history preserves them if needed. Mathematical theorem manuscripts, independent reviews, original exact certificates and [the cyclic graph source manuscript](CYCLIC_CELL_LEDGER.md) remain in place solely as **mathematical sources**, not as current status bars.

Do not resurrect case-count or gate-count progress. For each real new result record only: **full claim → exact original physical domain → certified/reviewed proof or concrete unresolved obstruction → Git commit → next single active claim**.
