# n=9: deep gated roadmap to an unrestricted hand proof

**Branch:** `research/nine-tablefree-hand`; **PR:** #11 (draft).
**Current mathematical boundary (2026-10-23):** G2.C is closed at the
hand-proof level. The unrestricted branch has a compact minimizer,
sparse stressed contact core, a physical torque-balanced incidence
network, a radial bridge/loaded-leaf reduction, and newly imported
cap, solid-row and tree terminal manuscripts. **No exhaustive sharp
core-plus-completion theorem is proved:** the unrestricted nine-square
lower bound, global equality classification, full independent audit,
Lean kernel proof and integration remain OPEN.

**Progress record:** [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md) is the
append-only, timestamped source/commit and scope ledger. The most
recent cap/tree manuscripts entered this draft research branch on
2026-10-23, after GitHub's prior head 028a63b (11:35:37 UTC).
Their hand proofs have **not** received independent full audit; their
accompanying exact-regression script/report remain in the conversation
proof package rather than the GitHub tree.

**Completion metric:** close a *finite exhaustive* family of all
physically realizable nine-square cores **together with unstressed
completions**, or prove one universal sharp invariant. An additional
conditional class is useful but does not by itself close G2.O3.2–O4.

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
       +-- O3.1e separate 27-atom angular certificate         CLOSED hand
       +-- O3.1f physical force/torque incidence and transmitters CLOSED hand
       +-- O3.1g radial bridges / central cover / S-D leaves    CLOSED hand
       +-- O3.1h cap theorem and all-direction strip occupancy  HAND DRAFT; AUDIT PENDING
       +-- O3.1i solid four-row completions and mixed seam      HAND DRAFT; AUDIT PENDING
       +-- O3.1j star exclusion / two-loaded tree path          PARTIAL; AUDIT PENDING
       |       window 79/40 <= R <= sqrt(Q), n=8 lower-window dependency
       |
       +-- O3.2 ALL remaining core+completion alternatives      OPEN
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
3. The <=27-atom **physical** force/torque certificate has a
   planar **contact-point incidence network**, not necessarily a
   planar body-pair graph. Do not transplant the <=19 planar-body
   bound into that stronger certificate without an additional proof.
4. A stressed core may use fewer than nine squares. Its completion by
   the other physical squares cannot be omitted from a nine-square bound.
5. Tree/star theorems below explicitly require 79/40 <= R <= sqrt(Q).
   Importing the n=8 lower bound is a declared dependency, not a
   new table-free proof of that prerequisite.

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
- **G0.3.7 DRAFT exact negative witness:** [UNRESTRICTED_THREE_SQUARE_CAP.md](UNRESTRICTED_THREE_SQUARE_CAP.md),
  Section 7, gives a record-radius nine-square packing with **no
  triple sharp cap in any frame**. A theorem claiming every equality
  packing has a three-square cap is false; the cap method must
  allow a separate no-cap equality terminal.
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

### G1.T5 New oblique-safe cap and solid-row terminals [HAND DRAFT; AUDIT PENDING]
- **T5.1 CAP.1:** [UNRESTRICTED_THREE_SQUARE_CAP.md](UNRESTRICTED_THREE_SQUARE_CAP.md)
  proves a clipped horizontal section of length at least one for
  any oriented square inside D_Q above the line y=7/16, strictly
  greater than one if the square is tilted. The test segment is
  [-3/2,3/2] at y=5/4; no pairwise coordinate separation is assumed.
- **T5.2 CAP.2:** three physically disjoint squares in that cap
  force q=Q and rigid outer axis-aligned centers (-1,15/16),
  (1,15/16), with a sliding center (0,eta),
  15/16 <= eta <= sqrt(1041)/16-1/2.
- **T5.3 CAP.3 (unrestricted necessary condition):** for any
  hypothetical nine-square packing with q<Q, in **every frame**
  at least five squares meet the open strip |y|<7/16.
  Their vertical projection interval order has height <=2;
  their physical separators need not be perpendicular to the strip.
- **T5.4 ROW.1-2:** [SOLID_FOUR_ROW_UNRESTRICTED_NINE.md](SOLID_FOUR_ROW_UNRESTRICTED_NINE.md)
  proves that every nine-square completion of a **solid** axis-aligned
  4x1 row at q<=Q has q=Q, even when all five remaining square
  frames/separators are arbitrary. It pins the three-square opposite
  cap but not the two free squares.
- **T5.5 ROW.3:** the same manuscript derives a seven-square
  four-over-three seam terminal without assuming horizontal
  projection separation among the **three** cap squares.
- **Exit for T5:** the manuscripts give terminal sharp inequalities
  under explicit cap/row/seam hypotheses and one unconditional
  subcritical necessary strip condition. They do **not** extract a
  cap or a solid row from arbitrary nine-square Packing, nor
  close global optimality. Independent detailed audit pending.

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

### G2.O3.1f — Physical contact-force and angular incidence [CLOSED hand; prior branch]

**Source:** [PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md).
This is a global **necessary** reduction, not an inequality q>=Q.

- **O3.1f.1:** select smooth local constraints for actual vertex/edge,
  vertex/vertex, and shared-side-segment contacts; the contact forces
  have application points in the true common intersection.
- **O3.1f.2:** retain joint translation and rotation balances in one
  <=27-atom physical certificate. Its straight-line contact-point
  **incidence** graph is planar and loaded bodies are externally
  incident; this is not planarity of the body-pair graph.
- **O3.1f.3:** an unloaded two-force transmitter uses opposite sides
  or vertices and has projected reserve exactly 1 or sqrt(2).
  For square-ended transmitter paths q<=Q, possible total internal
  reserves are 0, 1, sqrt(2), 2.
- **Limit:** no sharp nine-square completion bound follows merely from
  discrete path lengths, incidence planarity or stationarity.

### G2.O3.1g — Radial bridges, central cover and circle-loaded leaves [CLOSED hand; prior branch]

**Source:** [RADIAL_BRIDGE_AND_LEAF_REDUCTION.md](RADIAL_BRIDGE_AND_LEAF_REDUCTION.md),
already present at branch commit 028a63b; **not** credited as new in
the 2026-10-23 cap/tree import.

- **O3.1g.1:** exact cut-force/cut-moment identities imply every
  bridge of the positive body-pair graph carries force on a radial line
  through the disk center; both cut sides have circle weight.
- **O3.1g.2:** every bridge touches one of <=4 central, physically
  circle-clear squares; this vertex set covers **bridges only**.
  Do not treat it as a cover of all positive edges or all contacts.
- **O3.1g.3:** a suitable choice of true normals makes every
  off-origin point-only vertex/vertex positive edge cyclic, never a
  bridge. It is an existence statement about the chosen stress.
- **O3.1g.4:** a circle-loaded degree-one body has an exact radial
  **S leaf** (side normal, contact radius sqrt(R^2-1/4)-1) or
  **D leaf** (diagonal, contact radius R-sqrt(2)), with determined
  center and circle-atom pattern.
- **Limit:** nonbridge contacts may be nonradial. The S/D terminal
  formula does not eliminate the remaining physical unstressed bodies.

### G2.O3.1h — Sharp three-square cap and global strip occupancy [HAND DRAFT; AUDIT PENDING]

**Source:** [UNRESTRICTED_THREE_SQUARE_CAP.md](UNRESTRICTED_THREE_SQUARE_CAP.md),
imported on 2026-10-23. The finite rational checks supporting
regression live in the local proof package, not yet in GitHub.

- **O3.1h.1 CAP.1:** a unit square inside the exact cap
  D_Q intersect {y>=7/16} has length >=1 on
  [-3/2,3/2] x {5/4}, strictly >1 if rotated.
  The hand proof treats both signed tilt cases and line clipping.
- **O3.1h.2 CAP.2:** three physical squares in the cap force
  three aligned unit sections, exact outer centers (+/-1,15/16)
  and one sliding middle center. Four cannot fit the cap.
  This is independent of common-coordinate separability.
- **O3.1h.3 CAP.3:** for **every** frame of any packing with q<Q,
  at most two squares are wholly in each of the opposite 7/16 caps;
  at least five meet the central strip |y|<7/16.
  The vertical-interval order of those strip squares has height
  <=2, but that does not make their own physical separators x/y.
- **O3.1h.4 CAP.N (negative):** an exact q=Q nine-square
  configuration has **no** three-square sharp cap in any direction.
  It explicitly rejects any global cap-extraction normalization
  for the equality family.
- **O3.1h.5 OPEN bridge to sharpness:** combine this *all-direction*
  strip occupancy with physical contact stresses/packing capacity,
  or prove an alternative **exhaustive** sharp structural disjunction.
  Neither CAP.1 nor CAP.3 alone proves q>=Q.
- **Exit:** the cap and every-direction necessary inequality have
  complete written arguments, **pending independent audit**. The
  universal sharp-n9 bridge in h.5 is **OPEN**.

### G2.O3.1i — Solid four-row and mixed-seam completions [HAND DRAFT; AUDIT PENDING]

**Source:** [SOLID_FOUR_ROW_UNRESTRICTED_NINE.md](SOLID_FOUR_ROW_UNRESTRICTED_NINE.md).

- **O3.1i.1 ROW.1:** assuming four common-height, aligned squares
  form a contiguous 4x1 solid rectangle, all remaining five
  squares in D_Q must lie wholly above/below it; no square can
  wrap around an endpoint.
- **O3.1i.2 ROW.2:** pigeonhole gives three on one side; CAP.2
  yields q=Q and pins the solid row and three opposite-cap squares,
  allowing the other two to rotate and separate obliquely.
- **O3.1i.3 ROW.3:** a seven-square seam with a horizontally
  projection-disjoint four-chain and three arbitrary physically
  disjoint squares on the other side also gives q=Q, with
  no projection-order assumption on the three.
- **O3.1i.4 OPEN extraction:** nothing shows that an arbitrary
  nine-square minimizer has a **solid** row or the mixed-seam
  hypothesis. A staggered four-chain is not a solid row.
- **Exit:** a whole physically complete class is sharply bounded;
  the global extraction claim remains **OPEN**, and the hand
  proof needs independent audit.

### G2.O3.1j — Small positive-stress trees [PARTIAL; AUDIT PENDING]

**Source:** [SMALL_TREE_STRESS_CORES.md](SMALL_TREE_STRESS_CORES.md),
imported 2026-10-23. Its theorems assume the explicit window
**79/40 <= R <= sqrt(Q)**. For a hypothetical nine-square
minimizer, the lower window can be imported from the repo's
n=8 result by deletion, **with a separately declared n=8
dependency**. A self-contained table-free lower-window proof is
not supplied by this manuscript.

- **O3.1j.1 TREE.1 (closed conditional hand):** every tree
  positive-stress component with exactly two circle-loaded
  square bodies in this window is a four-square side-normal
  transmission path at R^2=17/4, with aligned frames and
  center positions (-3/2,0),(-1/2,tau_1),(1/2,tau_2),(3/2,0),
  -1/2 <= tau_1,tau_2 <= 1/2.
- **O3.1j.2 TREE.2 (closed conditional hand):** all positive
  **star** components with >=2 loaded leaves are excluded in
  this radius window, for every degree and every orientation,
  using radial S/D leaf geometry. A single-edge two-body
  component is also excluded by the bridge-loaded condition.
- **O3.1j.3 TREE.3 (closed conditional hand):** the flat
  tau_1=tau_2=0 subcase of TREE.1 cannot be completed by five
  squares at R^2=17/4, by the solid-four-row terminal.
- **O3.1j.4 OPEN:** eliminate or sharply bound **all**
  staggered tau_1,tau_2 path completions (not only the flat
  subcase), retaining the five other physical squares with
  possible oblique pairwise separators.
- **O3.1j.5 OPEN:** resolve non-star branching trees, arms
  with transmitters, and cyclic stressed components with
  all remaining squares. The star result alone does not
  complete the tree branch.
- **Exit:** j.1–j.3 are hand manuscripts pending independent
  audit; j.4–j.5 are the remaining major global core classes.
  The finite path labels and radius window are **not** an
  exhaustive terminal inventory.

### G2.O3.2 — Sharp terminal extraction from physical core **and all nine squares** [OPEN]
The preceding constraints sharply reduce unrestricted minimizers,
but the first genuinely missing global theorem is **still** an
exhaustive sharp bound on *complete nine-square realizations*. The
new CAP/ROW/TREE manuscripts do not by themselves cover all such
realizations.

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
  exact oblique, two-stack, nonstratified and capless equality
  witnesses; an exact counterexample rejects that proposed exclusion.
- **O3.2f — global cap/strip constraint:** use O3.1h.3's
  every-direction five-square central-strip occupancy as a
  constraint on **every** hypothetical q<Q minimizer, possibly
  combined with bridge geometry. Do not assume the strip antichains
  are x/y separable.
- **O3.2g — remaining two-loaded trees:** analyze the complete
  tau_1,tau_2 staggered path together with five other unit squares
  and their real SAT axes. The solid tau_1=tau_2=0 row is closed.
- **O3.2h — remaining graph types:** star cores in the stated
  radius window are excluded, but non-star branching trees,
  cycles, multibridges, zero-load limits and contact-junction
  structures remain. Prove a global **capacity** inequality for
  each family or one invariant covering them all.
- **O3.2i — proof architecture decision:** before investing in
  another named special core, exhibit a finite *exhaustive*
  combinatorial/geometric classification containing every
  remaining physical nine-square minimizer, or pivot from
  type enumeration to a global integral/strip/support inequality.
  No fixed number of small positional subcases counts as progress
  toward O3.2 unless it reduces the whole quantified parent.

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

### G2.P — Optional origin-incidence / central-strip route [PARTIAL necessary constraint; sharp bridge OPEN]
Interior / boundary-without-interior / exterior of the square union
remain a logically exhaustive trichotomy. Individual sharp theorems
for these three branches have **not** been proved. The new CAP.3
theorem says every q<Q packing has at least five physical squares
meeting the central strip |y|<7/16 **in every direction**; it is a
global necessary constraint that might supersede case-by-case
origin incidence. Their interval ranks do not imply common-frame
physical separation. **P.1 OPEN:** combine the every-direction strip
inequality with planar physical stresses into a sharp obstruction,
or prove another exhaustive terminal disjunction. This is an
optional alternative to O3.2–O4, not a third obligation if those
gates already prove T9.

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
- **G5.0.4 (conditional hand draft):** a triple sharp cap at Q
  forces two rigid outer cap squares and one vertical slider;
  a solid four-row equality pins a seven-square skeleton, while
  the remaining two squares may rotate. Sources:
  UNRESTRICTED_THREE_SQUARE_CAP.md and
  SOLID_FOUR_ROW_UNRESTRICTED_NINE.md.
- **G5.0.5 (negative):** the capless exact q=Q witness disproves
  a global equality normalization requiring a triple sharp cap.
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
- **G6.6 (new audit queue):** independently derive the exact
  cap clipped-section inequality and its two signed angle cases,
  solid-row end-bypass rigidity, and radial S/D star second-moment
  identities. Check the source's n=8 lower-window dependency and
  every equality/strictness claim.
- **G6.7:** keep the local check_three_square_cap.py / JSON report
  distinct from GitHub hand proofs and from any future Lean
  certificate. The recorded finite rational sample is an
  algebra/negative-control regression, never an all-angle proof.
- **G6.8:** record source commits and UTC progress entries in
  PROGRESS_LEDGER.md, including rejected global normalizations.

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
7. **Account for imported cap/tree results:** CAP.3 is an
   unrestricted **necessary condition**; ROW.2 is a whole but
   conditional solid-row class; TREE.2 excludes all stars only
   in 79/40 <= R <= sqrt(Q). None is an exhaustive obstruction.
8. **Progress log requirement:** append a UTC-stamped entry to
   PROGRESS_LEDGER.md with commit hashes, exact quantified scope,
   proof status, falsification controls, and the unchanged
   global missing implication. Update the deep roadmap/G2 ledger
   together when a gate changes.
9. **Status truth:** O3.2–O4, G4 and unrestricted G5 remain OPEN;
   G6–G8 are not complete. No independent full audit or Lean
   kernel proof is claimed.
