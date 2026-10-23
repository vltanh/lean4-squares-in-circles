# n=9 — live G2 subgates: six exhaustive tree cases, two completed

**Checkpoint:** 2026-10-23 finite-tree continuation. **Unrestricted q>=Q=1105/256 remains OPEN.** The common-coordinate-separable theorem is closed at hand level. The selected physical stress's entire positive-tree branch now has a finite six-case cover, with two full completion cases excluded. Four tree cases and the cyclic branch remain open.

**CLOSED hand** below means a written exact general argument within its explicit hypotheses, not Lean verification or independent full audit. This revision consolidates the earlier ledger; historical statuses and dates remain in Git. See [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md), [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md) and [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md).

## 1. Completed branches and necessary reductions

| Gate | Proven scope | Current status |
|---|---|---|
| G2.C / C4 | Every common-coordinate-separable nine-square packing, with arbitrary individual square rotations, obeys q>=Q | [x] CLOSED hand |
| G2.O3.0.2 | Compact unrestricted minimizer, true-contact selection, normalized nonnegative exact stress | [x] CLOSED hand necessary reduction |
| G2.O3.1a–d | Sparse planar outer-loaded translational support, <=19 terms | [x] CLOSED hand necessary reduction |
| G2.O3.1e | Separate full angular certificate, <=27 atoms | [x] CLOSED hand necessary reduction |
| G2.O3.1f | Genuine shared force points, joint force/torque, planar contact-incidence network | [x] CLOSED hand necessary reduction |
| G2.O3.1g | Radial bridge law, <=4 central circle-clear bridge-cover bodies, loaded S/D formulas | [x] CLOSED hand necessary reduction |
| CAP.1–3 | Exact oblique-safe sharp cap; all-direction central-strip occupancy below Q | [x] Hand manuscripts; independent audit pending |
| ROW.1–3 | Solid-row completions and mixed 4+3 seam | [x] CLOSED hand conditional terminals |
| TREE.F1 | Every positive-tree body localized, with one-step off-origin transmitters | [x] NEW CLOSED hand reduction |
| TREE.F2 | ALL tree radii equal 17/4 in the declared window; exactly six origin-incidence cases | [x] NEW CLOSED hand exhaustive reduction |
| TREE.12 / TREE.04 | Entire nine-square completion families excluded, arbitrary remaining square orientations | [x] NEW CLOSED hand full cases |
| TREE.20 / .11 / .02 / .03 | Remaining four complete geometric families | [ ] OPEN |
| CYCLIC | All selected positive components containing a cycle | [ ] OPEN sharp inventory/capacity theorem |
| G2.X / G4 | Unrestricted lower bound after all physical completions covered | [ ] BLOCKED |
| G5.U | All unrestricted equality packings | [ ] OPEN/BLOCKED |
| G6–G8 | Independent audit, Lean kernel proof, integration | [ ] NOT COMPLETED |

**Radius-window premise:** the tree results assume 79/40<=R<=sqrt(Q). Use the established n=8 lower bound explicitly, with its current proof dependencies, or supply a separate hand lower-window argument. Do not claim the tree proofs establish this premise themselves.

**Graph distinction:** the <=19 planar translational support and <=27 physical torque-balanced incidence certificate are not the same object. The positive body-pair graph need not be planar. Trees and bridges below refer to that selected positive body-pair graph; zero-weight physical contacts still constrain completion.

## 2. The coordinate-separable branch is finished; do not reopen it

- [x] Rank-product injection and 3x3 grid exclusion force a four-chain.
- [x] Four-chain shadow and inner-pair overlap retain all physical extra squares.
- [x] Entire large-zigzag branch excluded by ZIGZAG_BRANCH_CLOSED.md.
- [x] Disjoint signed 4+3 chains close through SIGNED_MATCHED_CHAIN_STRESS.md.
- [x] Canonical residual complement has two vertical stacks, (4,1) or (3,2).
- [x] FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md closes (4,1).
- [x] The elementary five-element matching and singleton split close (3,2) by a perpendicular signed 4+3 stress.
- [x] COORDINATE_SEPARABLE_NINE_COMPLETE.md assembles the complete class and its necessary equality skeleton.

A global common-coordinate frame is **false** even for exact record-radius physical packings. The coordinate theorem is not the unrestricted theorem.

## 3. Unrestricted physical-stress input (existing proofs)

**SPARSE_MINIMIZER_STRESS.md:** compactness and strict noncontact axis selection lead to a genuine physical minimizing stress; an explicit dilation direction gives regularity. Exact conic thinning supplies <=19 positive fixed-frame terms and the center-eliminating dual attains the unknown value q0. Every positive component has circle load on at least two bodies.

**PLANAR_STRESS_CORE.md / ROTATION_STATIONARY_STRESS.md:** translational support can be planarized through actual four-way contact uncrossing, with loaded bodies on the exterior face; angular stationarity has a separate <=27-atom certificate. No unproved identification of these two stresses is used.

**PHYSICAL_CONTACT_STRESS.md:** the refined local physical-contact construction supplies joint force/torque at genuine common points. Its planar representation retains contact junction nodes. Degree-two unloaded transmitters have reserve 1 or sqrt(2); square-ended paths at q<=Q have total reserve 0,1,sqrt(2),2.

**RADIAL_BRIDGE_AND_LEAF_REDUCTION.md:** cut moments force each bridge radial; every bridge touches one of <=4 circle-clear central bodies. Choose nonradial normals at off-origin point-only vertex/vertex contacts so positive edges of that type are not bridges. The exact radial side-normal/diagonal loaded-leaf geometries are prior inputs, not newly claimed by this continuation.

## 4. New TREE.F1 — all-body localization [CLOSED hand]

Source: [TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md), commit 4f8144d.

- [x] **F1.1:** every unloaded tree body meets D_delta; otherwise all its incident radial outer forces would have the same sign and could not balance. At most four unloaded bodies occur.
- [x] **F1.2:** every loaded tree body has one unique radial force point and exact S/D form, even if its degree is two. D has degree one; S has degree at most two.
- [x] **F1.3:** an outward radial support point of a square avoiding zero has norm >1.
- [x] **F1.4:** any unloaded body avoiding zero is one side-normal transmitter to one S terminal, with incoming origin-containing neighbor(s). Such a body requires A=sqrt(R^2-1/4)-1>1; there is no arbitrary sequence of these transmitters.
- [x] **F1.5:** at least one unloaded square contains zero; a unique origin-containing body yields a subdivided star, not an unbounded topology list.

The clarification that both incoming and outgoing edges are required by force balance is recorded explicitly in TREE_FINITE_VALIDATION.md, Section 6.

## 5. New TREE.F2 — all-tree radius and finite coverage [CLOSED hand]

Source: [TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md), commit 4007bfc.

- [x] **F2.D:** a D terminal's neighbor contains zero in its open interior.
- [x] **F2.I:** origin-interior roots are impossible. Ordinary stars are already excluded; the remaining subdivided-star root has a short radial support point, either a vertex or side-interior point. Both complete analytic cases contradict force balance.
- [x] **F2.V:** an origin-vertex body has radial support radii only 1 or sqrt(2); the available tree contact radii force A=1.
- [x] **F2.S:** an origin-side body has five possible nonzero radial support-point types. A<1 and A>1 each leave at most one uncancellable horizontal positive force, so A=1.
- [x] **F2.R:** EVERY positive tree in the window has **R^2=17/4**, all unloaded bodies contain zero on their boundaries, and all loaded bodies are S terminals at centers (3/2)e and inward contacts e.
- [x] **F2.C:** if s and v count side-interior and vertex incidences of the unloaded component bodies, disjoint tangent cones give **2s+v<=4**, while star exclusion gives **s+v>=2**. Exactly six profiles result.

This excludes every other radius in the entire window for the tree branch. It does not exclude a full nine-square realization at the exceptional radius without a completion theorem.

## 6. The exact six-case tree completion inventory

| Case | s | v | Full family | Closure status |
|---|---:|---:|---|---|
| **TREE.20** | 2 | 0 | Opposed side-origin bodies; all inner offsets in the two-loaded path | [ ] OPEN; flat solid row alone closed |
| **TREE.11** | 1 | 1 | Side-origin plus vertex-origin body; include nonaligned loaded branches | [ ] OPEN |
| **TREE.12** | 1 | 2 | One side body and two vertex bodies fill the origin angle | [x] CLOSED hand |
| **TREE.02** | 0 | 2 | Two vertex-origin bodies, all compatible relative cone angles | [ ] OPEN |
| **TREE.03** | 0 | 3 | Three vertex-origin bodies, all compatible angular gaps and loads | [ ] OPEN |
| **TREE.04** | 0 | 4 | Four origin quadrants form a central 2x2 block | [x] CLOSED hand |

Each case retains all continuous parameters and every unstressed physical square. Slider endpoints change to vertex-incidence rows; they are not omitted. The table is exhaustive for the **chosen tree component**, not for arbitrary cyclic contact graphs.

### TREE.CAGE — four cardinal outer squares [CLOSED hand]

Source: [TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md).

Four axis-aligned squares centered at (+/-3/2,0),(0,+/-3/2) in D_(17/4) permit at most four additional unit squares, **with arbitrary orientations and actual oblique separators**. Inscribed-disk exclusion leaves central or diagonal center regions; the diagonal regions are eliminated by an exact all-angle corner inequality. All extra centers then lie in [-1/2,1/2]^2, whose four sign subboxes have diameter <1. Total capacity is eight.

### TREE.BLOCK — central solid 2x2 [CLOSED hand]

Any additional center must stay >=1/2 from [-1,1]^2 and have norm <=3/2. Only the four cardinal axial centers remain; exact containment equality forces alignment. Again total capacity is eight.

### TREE.12 full completion [CLOSED hand]

Origin-angle saturation aligns the three unloaded bodies. The side-origin body's equilibrium forces an upward S terminal, and total circle-force balance forces its downward opposite. Exactly two loaded bodies would imply exactly two unloaded bodies by the earlier path theorem, contradicting this three-unloaded case. Thus a horizontal pair is also forced, yielding all four cardinal terminals. Apply CAGE to **all** other physical squares.

### TREE.04 full completion [CLOSED hand]

Four vertex cones saturate 2*pi, so the unloaded bodies form the central solid 2x2 block. Apply BLOCK to **all** other physical squares.

### The four remaining full completion contracts [OPEN]

- **TREE.20:** exclude five additional physical squares for every staggered four-square path at R^2=17/4. The claim that each side holds at most two squares is false and has an exact regression witness.
- **TREE.11:** bound every full completion of the side-plus-vertex family. A nonaligned five-body positive tree exists at 17/4, so the core itself cannot simply be ruled out.
- **TREE.02 / TREE.03:** retain all allowable angles and positive loads; prove one whole-family completion inequality per case or a shared theorem covering several cases.

The completed cases are documented in commit 5acabe7 and the timestamped [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md). Two cases closed is not a global progress percentage.

## 7. CYCLIC and unrestricted assembly [OPEN]

There is a complete OUTER split: either at least one positive component is a tree (the table above applies), or every positive component has a cycle. In the second branch:

- **CY.1 OPEN:** a human-sized exhaustive geometric core inventory, including bridges, actual junctions, loaded nodes and remaining physical squares.
- **CY.2 OPEN:** sharp orientation-uniform stress/capacity inequalities, or one global cap-strip invariant covering all cyclic completions.
- **CY.3 OPEN:** all equality and zero-weight limits. Nonbridge edges need not be radial; no tree lemma is imported by renaming a cycle edge a bridge.

**O3.3 globally OPEN:** finish all six tree capacities and the cyclic branch, retaining the declared lower-radius dependency. The existence of finite graph syntax alone is not a sharp proof.

**O4 globally OPEN:** exact multipliers certify q0, not q0>=Q. Missing uniform inequalities must retain all nine physical squares.

**O5 / G2.X / G4 BLOCKED:** after complete sharp coverage, apply the minimizing reduction to rule out q<Q; construction supplies the upper bound.

## 8. Cap/row tools and equality status remain correctly scoped

- CAP.3 imposes >=5 strip-intersecting squares in every direction below Q. This can support or replace the tree/cyclic program, but is not itself a contradiction.
- The solid-row terminal includes arbitrary free-square rotations but excludes only common-height contiguous rows, not staggered paths.
- Signed matched-chain and stratified equality domains are complete only within their named hypotheses.
- A capless q=Q witness, the oblique free-pair witness and nonstratified parallel witness forbid the respective universal normalizations.
- **G5.U remains OPEN:** no theorem yet covers every unrestricted equality packing. G6 independent audit and G7–G8 Lean/integration remain incomplete.

## 9. Exact executed finite regressions and logging

[check_finite_tree_cases.py](check_finite_tree_cases.py), commit 8a6eea1, was matched to its committed Git blob and SHA-256 and executed at **2026-10-23 13:20:52 UTC**, Python 3.13.5, exit 0. [FINITE_TREE_EXACT_CHECK.json](FINITE_TREE_EXACT_CHECK.json) records 909 rational checks, the six integer cases and seven exact physical force/torque trees, plus cage and failed-shortcut controls.

These are finite exact regressions, not a universal proof, independent audit or Lean certificate. [TREE_FINITE_VALIDATION.md](TREE_FINITE_VALIDATION.md) gives the explicit nonaligned five-body and seven-body tree witnesses, boundary-slider cases and false-capacity counterexamples.

**Execution rule:** commit each complete mathematical argument promptly; append UTC source/commit/scope entries in PROGRESS_LEDGER.md; tick only entire finite cases whose stated hypotheses are covered. Do not substitute sample enumeration for continuous geometric proofs, and do not silently drop unstressed completion squares.
