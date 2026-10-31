# Six-body case-table-first draft: exact exterior-hexagon cover and Type II elimination target

Date: 2026-10-30. **DRAFT RESEARCH WORK, NOT A CLOSED SIX-BODY THEOREM.**

This is a deliberate switch away from drafting/reviewing one physical contact sublemma at a time. It starts from the **original six-body biconnected positive component** `C1.6.b0`, not the nine-body `C1.6.b3` parent. Exactly **nine actual unit squares** remain present; the six core units have three arbitrary completion squares. A hand-exclusion of a positive-stress component does not automatically exclude any physical packing unless the original common-selection premises are satisfied. The still-open downstream common-selection audit is unchanged.

## A. Accurate original inventory and the computational boundary

- The exterior-hexagon graph sector has **nine** noncrossing chord classes. Its original necessary graph/load cover has **40** orbits before the already established complete bare C6 exclusions `none/013` and `none/0123`. Thus the finite screen has **38** representative load orbits: **12 three-load, 20 four-load, and 6 five-load**.
- The interior-pentagon sector has **five** graph parents and **19** original necessary load orbits; its graph/load parents were already hand-closed in the earlier accepted complete pentagon adoption. Do **not** rerun those proof reviews. The remaining original `C1.6.b0` coarse parent lies in the exterior-hexagon sector.
- Every one of the six exterior-hexagon **five-load** representatives already has a named complete whole-original-orbit hand-exclusion. This is a *union of previously proved cases*, not six new original gate checks. In particular the original D02 five-load exit was accepted by a prior proof; its alternative manuscript explicitly earns no new credit.
- For the short-chord `02` graph, **six of its eight** table rows have identified complete published original-row exits. The exact two remaining original rows are `M6.B6.HEXAGON.D02.L135` (N unloaded) and `M6.B6.HEXAGON.D02.L1345` (N loaded). Unlike `C1.6.b3`, these both belong to the six-body component and must be prioritized.
- The table below conservatively labels **25** other rows `UNRECONCILED`. This is not a claim that all 25 are open: many may already have complete published hand exclusions. The original large fine roadmap, rather than the filename search, determines actual checked/open flags. Do not modify them until reconciled exactly.

The executable verifier `scripts/n9_six_body_table.py` rebuilds each orbit from the six-cycle plus chords, using (1) loaded-path-forest and loaded-complement-connected conditions, (2) the true degree-two/three loaded-neighbor obstructions, (3) the known opposite-ear pair condition, and (4) the one complete short-chord bypass exclusion. It calculates each graph's *actual* dihedral stabilizer; it is not a numerical placement search. An assertion compares all 40 results against the separately transcribed original table. The two bare-cycle exits are then removed. No square orientation, force, radius, shared mean or physical mask is sampled.

## B. Two immediate metric/completion screens added to every row

For every original positive plane embedding, a noncrossing chord divides one bounded face into two. The table script **combinatorially constructs all resulting bounded faces**, without making the incorrect claim that extra zero-weight physical contacts can merge distinct faces. The following are existing complete geometric inputs, used only as *necessary* screens:

1. An actual three-square contact ring encloses no whole additional unit.
2. An actual four-square contact ring with **at least three physical circle-boundary squares** encloses no whole additional unit, in the stated radius window. Every positively circle-loaded square is physically boundary, even when one corner weight is zero.
3. An exterior contact pocket between **two loaded** consecutive rim units has zero whole-extra capacity. Therefore the table prints only edges with at least one unloaded endpoint as **candidate** exterior pockets; a candidate is not claimed occupied or feasible.

These screens are conservative: a bounded face not classified empty may nevertheless be empty by another physical argument. The face split itself is a consequence of the original compatible physical planar embedding, not a license to delete positive chords or truncate original higher-degree force stars.

Exactly **eight of the 38** representatives have **all** bounded faces excluded by only the triangle and three-loaded quadrilateral screens. Four have already named whole-orbit exits; the other four conservative table entries are:

| Chord graph | Loaded set | Original consequence | Missing exit |
| --- | --- | --- | --- |
| `03` | `0134` | All bounded faces empty | Exclude the complete three-extra exterior-pocket allocation |
| `02+03+35` | `1245` | Four bounded triangles empty | Exclude the complete three-extra exterior-pocket allocation |
| `02+04+24` | `135` | Four bounded triangles empty | Same, retaining full loaded three-body geometry |
| `02+04+24` | `0135` | Four bounded triangles empty | Same, retaining full loaded four-body geometry |

These are attractive **table-driven draft targets**: all three extra squares must be exterior if the common physical routing applies. That does **not** imply exterior capacity below three. A proof must bound the *joint* exterior pockets for all orientations and all circle masks. Do not count these as original fine-gate closures yet.

### Exact all-orbit table

The table is intentionally exhaustive and carries the two screens. `HAND-CLOSED` means a named complete manuscript is supplied by the script's conservative allowlist; `OPEN` is used only for the two known unfinished D02 whole rows; and `UNRECONCILED` means no whole-original-row audit was performed in this draft. Source filenames for the eleven identified exits are in the script's `WHOLE_HAND_EXITS` dictionary.

| Chords | Loaded vertices | Loads | Unresolved bounded faces | Candidate outer edges | Evidence state |
| --- | --- | ---: | --- | --- | --- |
| `none` | `024` | 3 | 012345 | 01, 12, 23, 34, 45, 50 | UNRECONCILED |
| `none` | `0124` | 4 | 012345 | 23, 34, 45, 50 | UNRECONCILED |
| `none` | `0134` | 4 | 012345 | 12, 23, 45, 50 | UNRECONCILED |
| `none` | `01234` | 5 | 012345 | 45, 50 | HAND-CLOSED |
| `02` | `014` | 3 | 23450 | 12, 23, 34, 45, 50 | HAND-CLOSED |
| `02` | `134` | 3 | 23450 | 01, 12, 23, 45, 50 | HAND-CLOSED |
| `02` | `135` | 3 | 23450 | 01, 12, 23, 34, 45, 50 | OPEN |
| `02` | `0134` | 4 | 23450 | 12, 23, 45, 50 | HAND-CLOSED |
| `02` | `0135` | 4 | 23450 | 12, 23, 34, 45 | HAND-CLOSED |
| `02` | `0145` | 4 | 23450 | 12, 23, 34 | HAND-CLOSED |
| `02` | `1345` | 4 | 23450 | 01, 12, 23, 50 | OPEN |
| `02` | `01345` | 5 | 23450 | 12, 23 | HAND-CLOSED |
| `03` | `014` | 3 | 0123, 3450 | 12, 23, 34, 45, 50 | UNRECONCILED |
| `03` | `024` | 3 | 0123, 3450 | 01, 12, 23, 34, 45, 50 | UNRECONCILED |
| `03` | `124` | 3 | 0123, 3450 | 01, 23, 34, 45, 50 | UNRECONCILED |
| `03` | `0124` | 4 | 3450 | 23, 34, 45, 50 | UNRECONCILED |
| `03` | `0125` | 4 | 3450 | 23, 34, 45 | UNRECONCILED |
| `03` | `0134` | 4 | none | 12, 23, 45, 50 | UNRECONCILED |
| `03` | `1245` | 4 | 0123, 3450 | 01, 23, 34, 50 | UNRECONCILED |
| `03` | `01245` | 5 | none | 23, 34 | HAND-CLOSED |
| `02+03` | `124` | 3 | 3450 | 01, 23, 34, 45, 50 | UNRECONCILED |
| `02+03` | `125` | 3 | 3450 | 01, 23, 34, 45, 50 | UNRECONCILED |
| `02+03` | `1234` | 4 | 3450 | 01, 45, 50 | UNRECONCILED |
| `02+03` | `1235` | 4 | 3450 | 01, 34, 45, 50 | UNRECONCILED |
| `02+03` | `1245` | 4 | 3450 | 01, 23, 34, 50 | UNRECONCILED |
| `02+03` | `12345` | 5 | none | 01, 50 | HAND-CLOSED |
| `02+04` | `125` | 3 | 0234 | 01, 23, 34, 45, 50 | UNRECONCILED |
| `02+04` | `135` | 3 | 0234 | 01, 12, 23, 34, 45, 50 | UNRECONCILED |
| `02+04` | `0135` | 4 | 0234 | 12, 23, 34, 45 | UNRECONCILED |
| `02+04` | `1235` | 4 | 0234 | 01, 34, 45, 50 | UNRECONCILED |
| `02+04` | `1245` | 4 | 0234 | 01, 23, 34, 50 | UNRECONCILED |
| `02+04` | `12345` | 5 | none | 01, 50 | HAND-CLOSED |
| `02+35` | `0134` | 4 | 5023 | 12, 23, 45, 50 | UNRECONCILED |
| `02+35` | `0145` | 4 | 5023 | 12, 23, 34 | UNRECONCILED |
| `02+03+04` | `12345` | 5 | none | 01, 50 | HAND-CLOSED |
| `02+03+35` | `1245` | 4 | none | 01, 23, 34, 50 | UNRECONCILED |
| `02+04+24` | `135` | 3 | none | 01, 12, 23, 34, 45, 50 | UNRECONCILED |
| `02+04+24` | `0135` | 4 | none | 12, 23, 34, 45 | UNRECONCILED |

## C. Draft attack on the two remaining D02 whole load rows (not independently reviewed)

The original positive graph is **rim `01 12 23 34 45 50`, chord `02`**, with exact full-star assignment `A=0,V=1,D=2,C=3,N=4,B=5`. In both load rows the full positive neighbor sets are

    A: {V,D,B},  D: {A,V,C},  V: {A,D},
    B: {A,N},    C: {D,N},    N: {B,C}.

`A,D` are unloaded genuine degree three; `V,B,C` loaded genuine degree two. In `L135`, `N` is unloaded *true degree two* and is a genuine physical one-square side/diagonal transmitter. In `L1345`, `N` is **loaded**; the unloaded transmitter equation must never be applied to it. All three other squares and every selected mean remain.

The accepted whole-roof results already exclude the parallel-`V` case and the physical-unique Type III case in both rows. For `L135` the physical-unique Type I case is also excluded. The outstanding full families are:

| Original row | Physical `V` feature | Exact remainder to prove impossible |
| --- | --- | --- |
| `L135` | One physical circle corner | Type II far-A-vertex **side**; Type II A-only **side** with `90°<alpha+beta<120°` |
| `L135` | Two physical circle corners | The two inner-face feature charts, including a zero individual circle coefficient |
| `L1345` | One physical circle corner | Loaded-`N` Type I rows `S`, `M1`, `M2`, `G` and reflections; the remaining Type II side/owner cases |
| `L1345` | Two physical circle corners | Both physical-two inner-face charts, including zero corner coefficients |

A **complete** table/certificate must cover all rows above and all three completing units. The first branch is a useful algebraic prototype; it must not be mistaken for the entire D02 graph.

### C.1. A necessary scalar inequality for the Type II A-only *both-unique* branch

The existing complete hand manuscript `TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md`, Sections 3–8, gives the following for its exact original both-unique A-only side domain:

    sigma > 0, -1 < tau = b·c < 0, 0 < K = sigma+tau < 1,
    A_B = (Delta·c)/sigma - 1 > 0,
    A_C = (Delta·b)/sigma - 1 > 0,
    r_B = A_B+x_B, r_C = A_C+x_C,
    x_B>0, x_C>0,
    r_B²+r_C² - 2*tau*r_B*r_C = 1.

**New elementary necessary comparison (draft).** Since `tau<0` and `A_B,A_C,x_B,x_C>0`, the positive quadratic `F(X,Y)=X²+Y²-2*tau*X*Y` is strictly increasing in each nonnegative coordinate. Consequently any surviving both-unique side configuration must satisfy

    (Delta·c - sigma)² + (Delta·b - sigma)²
      - 2*tau*(Delta·c - sigma)*(Delta·b - sigma) < sigma².    (T)

This statement is derived only from the original unit direction and strict positive side offsets; it does not delete the original full hub/circle/torque equations. It is a *necessary filter*, not a contradiction over the whole domain. In particular, do not claim the inequality has already been proved false or substitute an unvalidated numeric plot for an exact sign proof.

The original complete two-endpoint torque equations also give

    x_B=(gamma/P_B)*(r_B-K*r_C),
    x_C=(gamma/P_C)*(r_C-K*r_B),
    r_B-K*r_C>0, r_C-K*r_B>0,
    gamma>0, P_B>0, P_C>0.

Eliminating the same original `gamma` **without ever dividing by a potentially singular 2×2 matrix** yields the additional exact equation

    P_B*(r_B-A_B)*(r_C-K*r_B)
      = P_C*(r_C-A_C)*(r_B-K*r_C).                       (E)

This equation and (T) allow a lower-dimensional exact search: `r_B,r_C` satisfy the unit quadratic, the strict sector constraints and one original equality. The two full original circle-corner equalities, original third-root cubic, positive radius formula, both actual side means and all three completion squares **must still be imposed**. The singular-determinant case is not removed by (E).

### C.2. Table-assisted proof-certificate format

For each *remaining original load row and complete physical feature*:

1. Derive an **exact compact real-algebraic system**, including the unchanged original force/torque/contact equations, circle masks, selected port ownership, all normal signs, physical containment, pairwise separation and three additional squares. Use the original exact side-coordinate parameterizations when available; do not erase `N`'s load in `L1345`.
2. Clear denominators **only after proving them strictly positive**. Trigonometric angles can be encoded by half-angle rationals `t=tan(alpha/2)`, `v=tan(beta/2)` with exact positive denominators. Keep any square-root variable as a separate positive unknown with its squared identity.
3. **Explore** necessary scalar/contact domains with exact rational interval subdivision or CAD to find a finite cover. For a candidate sign inequality on a rational box, export its exact polynomial, rational box endpoints and an all-nonnegative Bernstein coefficient vector (or a compact algebraic elimination certificate). No floating pose sample, grid resolution or timeout is evidence of infeasibility.
4. Verify each exported certificate using **only rational arithmetic and polynomial identities**, ideally with a shared proof checker and a DAG of repeated subboxes. In eventual Lean integration, use standard kernel-checked algebra (`ring`, `norm_num`, `positivity`, or a small verified Bernstein evaluator); avoid millions of generated literal tactic lines and prohibited external axioms.
5. Record **CLOSED** only if the rows cover every actual graph/load/physical-circle mask and every equality/boundary case with the three extras. If the cover leaves boxes, publish them as precise **OPEN** subregions. Every original fine flag is changed only when its complete original obligation closes.

The finite graph-table verifier is **already executable and exact**. The suggested continuous certificate procedure is **not yet implemented** and has not established an infeasibility certificate for `L135`, `L1345` or the four no-hole unclassified graph/load rows. Do not turn the method into a claimed proof.

## D. Revised workflow and deliberate review limit

- **First:** work toward one whole D02 `L135` or `L1345` proof, using a table immediately when the analytic branches multiply. Keep the entire original six-body graph and three completing squares throughout.
- **In parallel at the draft level:** close or expose a concrete obstruction in the four bounded-hole-free rows of Section B. A successful **whole original row** is more valuable than additional smoothness/polish of a local lemma.
- **Only once a complete row is drafted:** perform a single independent audit of its complete assumptions, the exact certificate and graph/physical-mask/extras join. Do not allocate a separate full review to every 1-line inequality or subcase.
- **Then:** reconcile original fine checkboxes with already published whole-row proofs; table metadata must not be misreported as new mathematical progress. Progress is measured by complete original rows and then the parent `C1.6.b0`, not by number of research manuscripts.

**As of this draft, there are NO new original fine-gate or coarse-gate closures.** The canonical global record remains **2,373/2,513 fine checked, 37/58 coarse closed**, with `C1.6.b0` open. This is a substantive execution pivot and exact finite combinatorial/face-screening artifact, not an optimality proof.