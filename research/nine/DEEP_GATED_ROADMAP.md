# n=9: deep gated roadmap to an unrestricted hand proof

**Branch:** `research/nine-tablefree-hand`; **PR:** #11 (draft).
**Current mathematical boundary:** G2.C is hand-proved. The unrestricted
branch now has a proved compact minimizer, exact sparse actual-contact
stress, planar outer-loaded stress core, and separate angular-stationarity
certificate. **The sharp inequality for all unrestricted nine-square
packings is still OPEN**, as is the complete global equality classification.
No n=9 Lean build, CI run or independent full manuscript audit is claimed.

This version consolidates the earlier deep roadmap; the earlier plans
and their exact timestamps remain in Git history. CLOSED below means
**hand argument written with its stated quantifiers**, not kernel-verified.

## 0. Target, standards and dependency map

Put `Q=1105/256` and `R*=sqrt(1105)/16`. The exact construction proves
`R9 <= R*`. The missing target is

\[
 \forall S:\mathrm{Fin}\,9\to\mathrm{UnitSquare},\;o,\;R\ge0,
 \quad \mathrm{Packing}(S,o,R)\Longrightarrow R^2\ge Q. \tag{T9}
\]

All frames are independent; boundaries may touch; the disk center is
arbitrary. Equality must be necessary and sufficient under the actual
project congruence convention, including free and oblique-only squares.

**Status vocabulary:** CLOSED hand = stated implication proved;
CLOSED negative = a false proposed implication has an exact counterexample;
PARTIAL = only a specified subfamily is covered; OPEN = missing proof;
BLOCKED = depends on an open predecessor. A proof of a necessary condition
is not a proof of the desired sharp lower bound.

```text
G0 exact definitions, witness and false-shortcut controls       CLOSED hand
G1 short terminal stresses and fixed-owner weak dual           CLOSED hand
  |
  +-- G2.C entire common-coordinate-separable theorem           CLOSED hand
  |
  +-- G2.O0-O2 actual SAT owners and oblique controls            CLOSED
       |
       +-- O3.0.2 compact minimizer / exact sparse stress       CLOSED hand
       +-- O3.1a-d planar outer-loaded 19-term core             CLOSED hand
       +-- O3.1e independent 27-atom angular certificate        CLOSED hand
       |
       +-- O3.2 sharp structural core/completion alternatives  OPEN
       +-- O3.3 human-sized exhaustive terminal inventory      OPEN
       +-- O4 uniform orientation inequalities >= Q            OPEN
       +-- O5 unrestricted oblique lower bound                 BLOCKED
             |
             +-- G2.X / G4 unrestricted sharp radius           BLOCKED
             +-- G5 all equality packings                      OPEN/BLOCKED
                    |
                    +-- G6 independent hand audit             NOT COMPLETED
                    +-- G7 Lean kernel formalization          NOT STARTED
                    +-- G8 public integration/replay           NOT STARTED
```

**Three distinctions that must survive every handoff:**
1. A planar *stress support* is not the full contact graph and is not a
   global orthogonal separating frame.
2. The planar <=19-term translational stress and the <=27-atom angular
   stress can differ. No simultaneous planar/torque result is proved.
3. A stressed core may use fewer than nine squares. Its completion by
   the other physical squares cannot be omitted from a nine-square bound.

---

## G0 — Physical semantics, exact upper bound, negative controls [CLOSED hand]

### G0.1 Exact geometric encoding
- **G0.1.1:** centers `c_i`, orthonormal side axes `u_i,v_i`, and four
  corners `c_i+(epsilon*u_i+eta*v_i)/2`.
- **G0.1.2:** corner containment is equivalent to full closed-square
  containment; maximal squared radius is
  `|c_i|^2+1/2+|c_i dot u_i|+|c_i dot v_i|`.
- **G0.1.3:** genuine nonoverlap is one of eight signed own-axis SAT
  alternatives per pair, allowing equality and multiple owners.
- **G0.1.4:** centers of interior-disjoint squares have Euclidean
  distance at least one; any coordinate halfwidth is at least one half.
- **Exit:** statements match the original Packing predicate, not a
  strengthened row or common-frame definition.

### G0.2 Construction and exact witnesses
- **G0.2.1:** HAND_PROOF.md gives an exact nine-square packing at `Q`.
- **G0.2.2:** NONRIGID_WITNESS.md and NO_GLOBAL_ORTHOGONAL_FRAME.md
  provide genuinely rotated record-radius examples with true oblique
  pair separation.
- **G0.2.3:** TWO_STACK_SHARP_EQUALITY_WITNESS.md realizes a residual
  five-square horizontal chain number two, exactly at `Q`, and has a
  perpendicular signed 4+3 terminal.
- **Exit:** upper bound and falsification controls, not global optimality.

### G0.3 Rejected shortcuts
- **G0.3.1 CLOSED negative:** a central open square or positive central
  core is not universal at n=9 equality.
- **G0.3.2 CLOSED negative:** the nine frames need not all agree.
- **G0.3.3 CLOSED negative:** no single globally separating perpendicular
  frame exists for some record-radius packings.
- **G0.3.4 CLOSED negative:** center-radius and L-infinity distance
  relaxations alone are too weak; CENTER_RELAXATION_COUNTEREXAMPLE.md.
- **G0.3.5 CLOSED negative:** even nine parallel squares need not be
  horizontally stratifiable in *any* frame; NONSTRATIFIED_PARALLEL_NINE.md.
- **G0.3.6 CLOSED negative:** eight squares can have disjoint crossed
  horizontal/vertical four-chains below `Q`; the ninth square is essential.
- **Exit:** retain the exact witnesses; never promote a disproved
  normalization while rewriting a proof.

---

## G1 — Geometric terminal inequalities [CLOSED hand, conditional]

### G1.T1 Long/short four-anchor stress
- **T1.1:** derive two endpoint span inequalities with reserves 2 and 1.
- **T1.2:** combine true vertical endpoint gaps, permitting independent
  signs, with weights 23 and 9.
- **T1.3:** the all-angle square support penalty proves `q>=Q`.
- **T1.4:** equality pins all four loaded endpoints and their frames.
- **Sources:** FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md,
  SIGNED_MATCHED_CHAIN_STRESS.md.

### G1.T2 Cap row and rotated 4+3
- **T2.1:** exact orientation penalty for all square angles.
- **T2.2:** projection-separated cap-row bound using two tangents.
- **T2.3:** opposite cap bounds meet at the seam `-7/16`, giving `Q`.
- **T2.4:** equality alignment is only for the seven selected anchors.
- **Source:** ORIENTATION_STABLE_SEVEN_ANCHOR.md.

### G1.T3 Four-corner grid
- **T3.1:** two horizontal and two vertical spans with one-unit reserves.
- **T3.2:** four diagonal tangent supports give `q>=9/2>Q`.
- **Source:** GRID_FOUR_CORNER_STRESS.md.

### G1.T4 Fixed-owner dual
- **T4.1:** retain true chosen own-axis separators; fix frames.
- **T4.2:** the center problem is convex; explicit force multipliers
  and scalar completed squares eliminate center variables.
- **T4.3:** zero circle weight requires zero node force.
- **Source:** SEPARATOR_GRAPH_CONVEX_DUAL.md.
- **Original scope:** a weak bound for supplied weights. The new O3.0.2
  theorem below proves *attainment* at every unrestricted minimizer.

**G1 exit:** all statements have explicit sufficient hypotheses. Their
validity does not prove those hypotheses occur in every packing.

---

## G2.C — Entire common-coordinate-separable class [CLOSED hand]

A single orthonormal frame separates **every pair** along at least
one of its coordinate projections. Individual square frames can differ.
The condition is an added hypothesis, false for unrestricted packings.

### G2.C0 Rank and initial extraction [CLOSED]
- **C0.1:** the two projection orders have longest-chain ranks.
- **C0.2:** rank pairs inject nine squares into an `a*b` grid.
- **C0.3:** no projection chain has five members at `q<=Q`.
- **C0.4:** if both chain lengths are at most three, the full 3x3 rank
  grid gives G1.T3, a contradiction; otherwise choose a four-chain.
- **Source:** ORTHOGONAL_RANK_DICHOTOMY.md.

### G2.C1 Shadow and inner-pair incidence [CLOSED]
- **C1.1:** the four projected intervals leave total complement <1/4.
- **C1.2:** every extra interval intersects one to three consecutive
  chain intervals.
- **C1.3:** exclusive outermost shadow forces center distance <1;
  every extra square overlaps one of the two middle intervals.
- **Sources:** FOUR_CHAIN_SHADOW_BARRIER.md,
  INNER_PAIR_SHADOW_DOMINATION.md. C1.3 itself is oblique-safe once
  a four-chain exists.

### G2.C2 Large zigzag [CLOSED]
- **C2.1:** center radius <61/40 fixes four narrow horizontal bands.
- **C2.2:** a chain height gap >=2 is between the middle pair only.
- **C2.3:** the five extras fall in three regions of capacities 2,1,2.
- **C2.4:** saturation contradicts coordinate separation.
- **Source:** ZIGZAG_BRANCH_CLOSED.md. No residual 4x3 zigzag leaf.

### G2.C3 Complement and frame switch [CLOSED]
- **C3.1:** a disjoint horizontal triple outside the four-chain gives
  signed matched-chain stress, covering all endpoint signs.
- **C3.2:** the prescribed three-band 3+3+3 class gives the grid stress.
- **C3.3.a.1:** if the five extras have x-chain height <=2, their two
  horizontal rank classes are antichains with a common interval point.
- **C3.3.a.2:** coordinate separation turns these into vertical stacks
  of sizes (4,1) or (3,2).
- **C3.3.a.3:** a vertical triple's middle center has `|y|<21/40` and
  forces a middle horizontal-chain center to have `|y|>19/40`.
- **C3.3.b CLOSED:** a disjoint perpendicular four-chain plus the ninth
  square is impossible. The four middle centers fill four central
  quadrant boxes; their exclusion boxes cover every ninth-center option.
- **C3.3.c.1 CLOSED:** without a four-element x-antichain, the five-element
  height-two poset has two disjoint comparable pairs and a singleton.
- **C3.3.c.2 CLOSED:** every extra square with a successor overlaps the
  left middle anchor; a predecessor forces overlap with the right one.
- **C3.3.c.3 CLOSED:** the singleton has a successor, a predecessor, or
  neither. These three cases produce two antichains of sizes 3 and 2
  overlapping different middle anchors.
- **C3.3.c.4 CLOSED:** adjoining those anchors produces perpendicular
  projection chains of sizes 4 and 3. G1.T1 gives `q>=Q` including
  the known exact equality witness.
- **C3.3.d CLOSED negative:** do not exclude the entire (3,2) class;
  its exact equality packing is retained by the frame switch.
- **Sources:** TWO_COLUMN_COMPLEMENT_REDUCTION.md,
  FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md,
  COORDINATE_SEPARABLE_NINE_COMPLETE.md.

### G2.C4 Whole-class assembly [CLOSED hand]
The source COORDINATE_SEPARABLE_NINE_COMPLETE.md assembles all branches
into `CoordinateSeparable && Packing_9 -> q>=Q`. At equality some
frame axis supplies signed matched 4+3 chains. The seven chain
squares have the signed matched equality form. The other two squares
are not asserted to share their orientation.

**Do not reopen G2.C for minor angle/height improvements.**

---

## G2.O — Unrestricted oblique branch [PARTIAL]

### G2.O0–O2 Existing encoding and controls [CLOSED]
- **O0:** exact oblique-only upper-pair witness refutes global coordinates.
- **O1:** choose true signed own-axis separators; keep contact ties.
- **O2:** the fixed-owner center weak dual is exact as a formula, not
  automatically a sharp `Q` bound for every graph.

### G2.O3.0.2 — Minimizer and actual-contact stress [CLOSED hand]
**Source:** [SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md).

- **O3.0.2a — compactness:** normalize the disk center, bound the centers,
  use compact unit-frame circles, and express pairwise nonoverlap as
  finite unions of closed SAT inequalities. Any subcritical packing
  yields a global minimizer `q0<Q`.
- **O3.0.2b — strict selection:** a physically noncontacting closed-square
  pair has a strictly separating own axis. Select that axis; use a tight
  axis only for actual touching pairs.
- **O3.0.2c — regularity and multipliers:** freeze the frames and chosen
  axes. Radially expanding the centers while increasing `q` sufficiently
  gives a strict active-constraint direction. An elementary conic
  alternative yields normalized nonnegative circle/edge multipliers.
- **O3.0.2d — exact sparse dual:** the weighted circle-vertex and edge
  gradients balance at every center; positive edge weights occur only
  at physical contacts. At most **19 positive scalar terms** suffice
  for nine squares, and the completed-square dual equals `q0` exactly.
- **O3.0.2e — connected core:** every stress component has positive
  circle weight on at least two distinct squares. One component can
  be retained and normalized; unloaded leaves and circle-free positive
  self-stress components are impossible.

**Exit satisfied:** an arbitrary hypothetical subcritical packing can
be replaced by a globally minimizing, exactly stressed configuration,
without any row deformation or coordinate-separability assumption.
This does not prove that the attained value is at least `Q`.

### G2.O3.1 — Geometric planar core and bounded paths [CLOSED hand]
**Source:** [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md).

- **O3.1a — junction geometry:** at most four squares meet at a point;
  a four-way junction is an aligned 2x2 unit-square block.
- **O3.1b — compatible owner choice:** select parallel true axes for
  the two opposite pairs at each such junction before extracting
  translational stress. Strictly separate every noncontact pair.
- **O3.1c — stress uncrossing:** subtract the smaller crossing-diagonal
  weight from both diagonals and add it to the two matching side
  contacts. This preserves every node force and exact dual value,
  removes a diagonal, and creates no new diagonal crossing elsewhere.
- **O3.1d.1 — planarity:** resolve each at-most-four-square contact
  junction respecting the cyclic order. A quadrilateral with at most
  one diagonal is locally planar; the contact support embeds globally.
- **O3.1d.2 — boundary loading:** a circle point belongs to at most one
  square. Circle-loaded square nodes are all incident to the exterior
  face of this planar embedding.
- **O3.1d.3 — restore sparsity:** conic thinning within the planar active
  support gives <=19 positive terms, hence <=17 positive contact edges.
  Select one connected loaded component.
- **O3.1d.4 — contract transmitters:** an unloaded degree-two square
  has equal opposite forces. Suppress its maximal straight-normal
  path with the exact support-width sum retained. For `q0<=Q`, each
  such path contains only **0,1,2 internal squares**; no self-loop
  or wholly unloaded transmission cycle is possible.

**Exit satisfied:** unrestricted minimizers have connected planar,
outer-loaded, sparse actual-contact stress cores, with bounded path
labels and no unloaded leaves. This is not a theorem that the full
physical contact graph is planar or that every core has value >=Q.

### G2.O3.1e — Full angular stationarity [CLOSED hand; separate certificate]
**Source:** [ROTATION_STATIONARY_STRESS.md](ROTATION_STATIONARY_STRESS.md).

- **O3.1e.1:** encode each selected owner's support maximum by four
  smooth nonowner-vertex inequalities; do not differentiate absolute
  values at parallel-frame cusps.
- **O3.1e.2:** the same dilation direction proves active-constraint
  regularity with all angles free.
- **O3.1e.3:** derive every angular derivative, including rotation of
  the owner's separating axis, alongside center force balance.
- **O3.1e.4:** global rotational symmetry removes one gradient-space
  dimension, giving at most **27 positive atoms** for nine squares.
- **O3.1e.5:** the center-eliminating dual remains attained exactly;
  positive atoms occur only at active constraints and touching pairs.

**Critical nonclaim:** these torque equations and the planar 19-term
stress need not be realized by the same multipliers. A selected
support-vertex atom is not automatically an independent force at a
point in the actual intersection segment. No simultaneous physical-
lever, planar, torque-balanced 19-term theorem is asserted.

### G2.O3.2 — Sharp terminal extraction from the planar core [OPEN]
This is now the first genuinely missing structural theorem.

- **O3.2a — retain all packing data:** record which of the nine squares
  lie in the stressed core, which are suppressed on its paths, and
  which are unstressed. Keep all actual physical nonoverlap conditions.
  An unstressed square is not necessarily geometrically unconstrained.
- **O3.2b — core inventory:** classify connected planar core types with
  at least two outer-face circle-loaded nodes; retained unloaded nodes
  have degree >=3; path labels are 0,1,2; total represented squares
  <=9; positive corner plus edge terms <=19.
- **O3.2c — completion capacity:** for each potentially low-radius
  core, prove how many other unit squares fit in the remaining space.
  A smaller core alone need not require radius sqrt(Q). Discarding
  its unstressed complement would destroy the nine-square quantifier.
- **O3.2d — short terminal families:** derive a human-sized exhaustive
  disjunction of known signed 4+3 / grid certificates, impossible
  alternatives, or genuinely new sharp stress families. Do not treat
  a finite but huge labelled graph enumeration as closure.
- **O3.2e — falsification:** test any proposed type exclusion against
  the exact oblique, two-stack and nonstratified equality witnesses;
  an exact counterexample rejects that proposed exclusion.

**Exit:** all feasible *nine-square* minimizing configurations are
routed into explicitly defined sharp terminal classes. Not achieved.

### G2.O3.3 — Exhaustiveness and symmetry quotient [OPEN]
- **O3.3a:** prove every planarized core enters the inventory, including
  bridge/cycle, multiedge-after-contraction, multiple-circle-contact,
  and zero-weight limits. No generic-position assumption.
- **O3.3b:** quotient only by actual global isometries, relabeling and
  square quarter-turn equivalences; preserve reflection conventions.
- **O3.3c:** prove every physical completion of every surviving core
  is either covered by a terminal theorem or impossible at `q<=Q`.
- **Exit:** a complete coverage implication, not merely a list of
  attractive candidate graphs. O3.2 and O3.3 may be proved together.

### G2.O4 — Sharp uniform inequalities [OPEN]
For every surviving core/completion family:
- **O4.1a CLOSED existentially:** at a minimizer a normalized exact
  dual exists (O3.0.2). This alone gives its unknown value `q0`.
- **O4.1b OPEN constructively:** obtain explicit usable weights or
  an invariant inequality from the balances and geometry.
- **O4.2 OPEN:** prove the value >=`Q` uniformly over **all** orientations
  and completions allowed in that family, with no dense angle mesh.
- **O4.3 OPEN:** directly exclude infeasible families by exact geometry;
  optimizer failure is not an exclusion proof.
- **O4.4 OPEN:** characterize every equality slack and allow zero-weight
  free squares. Do not import torque into a planar stress without
  proving the certificates can be chosen jointly.
- **Exit:** all nine-square terminal families are sharply bounded,
  including their exact equality conditions. Not achieved.

### G2.O5 — Oblique assembly [BLOCKED]
- **O5.1:** combine core/completion coverage with the uniform sharp bounds.
- **O5.2:** check all known equality witnesses remain admissible.
- **O5.3:** remove all graph, coordinate and orientation hypotheses
  except those derived from the original Packing predicate.
- **Exit:** no unrestricted minimizing packing has `q0<Q`.

### G2.P — Optional origin-incidence route [NOT USED AS A COMPLETED PROOF]
Interior / boundary-without-interior / exterior of the square union
remain a logically exhaustive trichotomy. Individual sharp theorems
for these three branches have **not** been proved. They are not extra
mandatory prerequisites if the minimizer/contact-core route handles
all configurations. Do not describe the old central-square approach
as established or count retiring that approach as a theorem closure.

---

## G2.X and G4 — Unrestricted radius [BLOCKED]

- **G2.X.1 CLOSED as a necessary reduction:** every hypothetical
  subcritical packing has a compact unrestricted minimizer with the
  sparse planar core and separate angular certificate proved above.
- **G2.X.2 OPEN:** the core plus remaining physical squares must enter
  a *sharp* terminal class. This is exactly O3.2–O4, not a new hidden
  structural assumption.
- **G4.1 CLOSED:** the explicit construction attains `Q`.
- **G4.2 BLOCKED:** use compactness and O5 to exclude `q<Q`.
- **G4.3 BLOCKED:** transfer the squared-radius statement to radius
  `sqrt(Q)` and the repository's natural public predicates.

**Exit:** T9 with only original Packing assumptions, and no external
optimizer, undisclosed certificate table, or unproved normalization.

---

## G5 — Complete equality classification [PARTIAL]

### G5.0 Proven conditional families [CLOSED hand]
- **G5.0.1:** STRATIFIED_EQUALITY_FAMILY.md: three slider heights and
  two upper squares, necessary and sufficient within stratification.
- **G5.0.2:** SIGNED_MATCHED_EQUALITY_FAMILY.md: all signed matched 4+3
  terminal equality configurations, seven aligned chain squares,
  three slider heights and two arbitrary square frames/centers with
  15 actual SAT pair tests. Includes oblique-only free-square pairs.
- **G5.0.3:** the whole common-coordinate class enters a signed
  matched equality skeleton after one of the two frame choices.
- **Boundary:** neither family has yet been proved exhaustive for
  unrestricted nine-square equality packings.

### G5.1 Global equality necessity [OPEN/BLOCKED]
- **G5.1a:** once G4 proves optimality, *each* q=Q packing is itself a
  global minimizer; apply the stress reduction without replacing it.
- **G5.1b:** analyze every equality branch in the sharp classification.
- **G5.1c:** recover all rigid anchors and all unstressed degrees of
  freedom. A minimizer substitution alone does not classify the
  original equality packing before optimality is known.

### G5.2 Parameter domains and converse [OPEN globally]
- **G5.2a:** list each genuine equality skeleton, including independent
  sign choices and physically distinct reflection branches.
- **G5.2b:** give exact corner/support domains for free centers and
  angles; do not simply restate nine unknown-square Packing.
- **G5.2c:** prove all parameters are sufficient for containment and
  pairwise interior disjointness, using actual own-axis SAT where needed.
- **G5.2d:** prove every unrestricted equality packing is represented.

### G5.3 Congruence and uniqueness language [OPEN globally]
Use the exact rotation/relabeling equivalence; handle reflections as
required. Do not claim isolated-pose uniqueness where the examples
have continuous translation/rotation freedoms.

---

## G6 — Independent hand-proof audit [NOT COMPLETED]
- **G6.1:** consolidate the actual unrestricted dependency chain once
  G4/G5 are proved; distinguish obsolete research attempts.
- **G6.2:** independently check support/corner identities, cone
  alternatives, regularity, and all equality signs and strictness.
- **G6.3:** independently check geometric contact-junction resolutions
  and exhaustive core/completion coverage; a graph picture is not proof.
- **G6.4:** retain all negative controls and exact equality witnesses.
- **G6.5:** verify theorem-to-source versions and explicit scope of
  every computation. A rational example check is not a universal proof.

**Local executed checks now available:** `check_sparse_stress.py`
was matched by Git blob and SHA-256 to the committed source and run
with exact Fraction arithmetic. SPARSE_STRESS_EXACT_CHECK.json records
36 pair SAT tests, 36 corners, force/angle balance, the uncrossing
identity, exact dual value Q, runtime version and exit code. This
closes those **regression checks only**, not G6's independent audit.

## G7 — Lean/Palomar-standard kernel formalization [NOT STARTED]
- **G7.1:** natural n=9 constants, construction and equality type,
  preserving existing unrestricted geometric semantics.
- **G7.2:** support, SAT, compactness and the finite conic argument,
  using standard mathematical lemmas or fully formalized proofs.
- **G7.3:** sparse/planar/angle reductions and short terminal inequalities.
- **G7.4:** the actual exhaustive sharp core/completion theorem,
  without replacing Packing by an assumed normal form.
- **G7.5:** radius attainment/lower bound and full equality converse.
- **G7.6:** compile, inspect axioms and dependencies, and independently
  replay in the standard kernel. No native-kernel shortcuts or oracles.

## G8 — Public integration and handoff [NOT STARTED]
- **G8.1:** integrate n=9 into Optimum and the radius/packing registries.
- **G8.2:** update Challenge mirror, README and proof textbook.
- **G8.3:** check n=1–8 regressions, source provenance and replay record.
- **G8.4:** only then finalize the PR; no merge or completion claim
  before the actual advertised result is proved and checked.

---

## Immediate execution contract

1. **Do not redo the common-coordinate theorem.** It is now closed.
2. **Do not redo compactness or merely ask for a stress.** The exact
   actual-contact stress exists at every unrestricted minimizer.
3. **Do not enumerate arbitrary SAT owners.** Use the proved connected
   planar outer-loaded core, bounded transmission paths and the separate
   angular necessary conditions, while retaining unstressed squares.
4. **Close a full remaining structural family or a universal inequality.**
   The target is the sharp value `Q`, not another small center/angle bound.
5. **If a proposed family exclusion is false, retain its exact witness.**
   In particular preserve known q=Q two-stack and oblique examples.
6. **Never combine separate certificates silently.** Planarity is proved
   for translational stress; full angular balance has a separate support
   bound. A proof needing both simultaneously must supply that bridge.
7. **Status truth:** currently O3.2–O4, G4 and global G5 remain open;
   G6–G8 are not completed. The new results close reductions, not T9.
