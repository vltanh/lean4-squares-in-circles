# n = 9: gated roadmap to an unrestricted, table-free proof

**Updated 2026-10-22.** Research branch: research/nine-tablefree-hand,
draft PR #11. This is a **research plan**, not a claim that the
unrestricted n = 9 theorem is established. The sharp independently rotated seven-anchor inequality is now **proved by a table-free hand argument (G1)**.
The central unresolved mathematical task is **G2 (unrestricted structural
extraction)**, followed by G3's remaining branches.

## 0. Exact target, definitions, and closure conditions

Write
\[
q_*=\frac{1105}{256},\qquad
R_*=\frac{\sqrt{1105}}{16}.
\]
This is the best-known construction radius, conjectured optimal for
nine freely rotatable unit squares; it is **not** an established
unrestricted lower bound. The target theorem is

\[
\begin{gathered}
\forall (S:\operatorname{Fin}(9)\to\mathrm{UnitSquare})
\ \forall o\in\mathbb R^2\ \forall R\ge0,\quad
\mathrm{Packing}(S,o,R)\ \Longrightarrow\ R^2\ge q_* .
\end{gathered}\tag{T}
\]

The definition of Packing is the existing one in
SquaresInCircles/Geometry.lean: arbitrary independent orientations,
closed-disk containment of all square points, and pairwise disjoint
*open interiors*. At equality, prove a second theorem classifying
every packing up to the repo's precise congruence/relabeling relation;
a single pose is **not** enough.

A gate is **CLOSED** only when the stated implication is proved for
*all* objects quantified in it, its case coverage is justified, and
every auxiliary lemma has a proof or an existing verified dependency.
Constructions, optimizers, uncompiled code, and empirical sweeps
may falsify a proposed lemma or suggest a route; they do not close a
mathematical gate.

**Target proof standard:** a finite number of geometrically meaningful
cases, exact symbolic inequalities, supporting lines/angles/convexity
when useful, and no long state-grid, generated rational table, or
unexplained computation. Finite means all *structural possibilities*
are covered, not that an arbitrary interval mesh has finitely many
cells. If a method produces a growing family of ad hoc subcases,
rethink the invariant rather than endlessly refining it.

### Dependency chart

~~~text
G0  Exact inputs, negative controls, and geometric vocabulary [CLOSED]
 |\
 | +--> G1  Orientation-stable sharp 4-versus-3 estimate [CLOSED, HAND]
 |
 +----> G2  Unrestricted extraction, center-status branches [OPEN]
             |
             +--> G3  Exclude every alternative pattern [OPEN]
                       |
           G1 + G2 + G3
                 |
                 v
             G4  Assemble universal lower bound [OPEN]
                 |
                 v
             G5  All equality configurations [OPEN]
                 |
                 v
             G6  Independent hand-proof audit [OPEN]
                 |
                 v
             G7  Lean formalization, kernel replay [NOT STARTED]
                 |
                 v
             G8  Public n=9 theorem, registry, documentation [NOT STARTED]
~~~

G1 and G2 may be investigated independently. G3 may turn out empty,
but may **not** be marked empty merely because the desired candidate
has a 4-versus-3 pattern. G4 is an assembly gate, not another hidden
geometric assumption.

## G0 — Exact inputs and false-shortcut tests [CLOSED as hand arguments]

**G0.1 (record construction):** [HAND_PROOF.md](HAND_PROOF.md), §1
gives an exact nine-square packing with rows of sizes 2,4,3 at q_*.
Consequently the universal optimal squared radius is at most q_*.

**G0.2 (special-case lower bound):** §§3--6 prove capacity bounds,
the sharp 4-above-3 (or reversed) theorem for seven same-frame squares,
the full horizontally **stratified** nine-square case, and four pinned
boundary anchors when the same-frame seven-anchor hypotheses hold.

**G0.3 (independent-rotation witness):**
[NONRIGID_WITNESS.md](NONRIGID_WITNESS.md) proves that the two
nonanchor squares need not share the anchors' frame.

**G0.4 (negative controls):**
[STRUCTURAL_NEGATIVE_TESTS.md](STRUCTURAL_NEGATIVE_TESTS.md) provides
three exact obstacles to naïve normalization:

- The record packing has **no square whose open interior contains the
  disk center**. The center lies on the common edge of two squares.
  Therefore the n=8 positive-central-core lemma cannot be imported.
- Even three axis-parallel, nonoverlapping squares in a smaller disk
  need not admit horizontal stratification in a given frame.
  Nine-square stratification, if used, needs a special theorem.
- An optimal-radius *candidate* can have a rotated nonanchor square;
  a theorem saying that all nine frames agree cannot be an equality
  classification.

**G0.5 (complete geometric encoding):** For square i with center c_i,
orthogonal side vectors u_i,v_i, and unit e, put

\[
h_i(e)=\tfrac12(|e\cdot u_i|+|e\cdot v_i|).
\]

The disk constraint has the exact finite form

\[
 \|c_i\|^2+\tfrac12+
 |c_i\cdot u_i|+|c_i\cdot v_i|\le q. \tag{D}
\]

For each pair i,j, disjoint interiors are equivalent to separation
along one of the four *actual* edge axes of i or j:

\[
  |(c_i-c_j)\cdot e|\ge h_i(e)+h_j(e),\qquad
  e\in\{u_i,v_i,u_j,v_j\}. \tag{SAT}
\]

There is no need to sample a continuum of arbitrary separating axes.
This is a finite **logical input formula**, not permission to expand
36 pairwise disjunctions into an enormous case table. Compress them
geometrically first.

**Closure status:** G0 statements are recorded as mathematical
hand arguments, with exact rational checks of the witness. No
n=9 Lean kernel compilation, full independent audit, or unrestricted
theorem is claimed.

## G1 — Sharp orientation-stable seven-anchor inequality [CLOSED: HAND PROOF]

The conjectured seven-anchor terminal lemma is now **proved** with
no small-angle assumption or computer-assisted verification.

**Primary source:**
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md).

**G1.1 (exact structural hypothesis): CLOSED.**
Fix any orthonormal frame (e,f). Four squares have pairwise disjoint
interior projections along e, three other squares also do, and
every point of every square in the group of four is above every point
of every square in the group of three along f. All seven unit squares
have **independent arbitrary orientations**.

**G1.2 (sharp terminal theorem): CLOSED.** Under these hypotheses,
\[
 q\ge q_*=\frac{1105}{256}.
\]
Its mathematical mechanism is a more general cap-row theorem: for
m horizontally projection-separated, independently rotated squares
above a common floor y=s, with \(0\le s+1\le m/2\),
\[
 q\ge \frac{m^2}{4}+(s+1)^2.
\]
The reflection covers squares below a ceiling.
The general bound is proved by adding the two tangent inequalities
with vectors \((\pm m/2,s+1)\) and an explicit one-square nonnegative
orientation penalty. The orientation penalty is proved by two
elementary sign cases; no discretization or trigonometric enclosure.

**G1.3 (equality and stress): CLOSED.**
Equality in the cap-row theorem (with positive height parameter)
forces all the participating square frames to be axis aligned,
all horizontal interval gaps to vanish, and the extreme top or
bottom corner vertices to lie at the exact tangent points.
For the 4-over-3 pair, equality forces the common dividing line
at \(s=-7/16\), all seven frame alignments, horizontal centers
\((-3/2,-1/2,1/2,3/2)\) and \((-1,0,1)\), and the four
outer pinned anchor heights \(1/16\) and \(-15/16\).
The two remaining squares in a nine-square packing are unrestricted.

**Scope boundary:** G1 does **not** imply that any nine-square
packing admits this seven-anchor pattern. That is the unproved
structural-extraction task G2. The independently rotated witness
NONRIGID_WITNESS.md is compatible with G1 because its rotated
square is *not* one of the seven anchors.

**Verification:** hand derivation and numerical spot checks only;
no Lean source, Lean compilation or kernel-verified formalization yet.

## G2 — Extract a global geometric skeleton from arbitrary nine squares [OPEN]

This is the dominant global obstacle. No layer structure, common
frame, active contact graph, or central square may be assumed without
proof. The extraction must cover *every* possible Packing at
q≤q_*, not only minimizers that resemble the record.

### G2.0 — Choose an invariant before enumerating states [OPEN]

Preferred data: circle-center incidence, cyclic order of visible
squares, support intervals along a chosen direction, and a small
graph of *actual* separating axes from (SAT). Establish a principle
that reduces these to a **constant-size** list of geometric patterns,
ideally one terminal 4-versus-3 pattern plus a few directly excluded
alternatives.

A possible, **unproved**, simplification is to select e from one of
the 18 individual square edge directions. This would make frame
selection finite. Test it against configurations before using it;
otherwise allow a general e and prove its existence.

Use the finite trichotomy below as a bookkeeping partition, not
as proof of any exclusion.

### G2.1 — Origin lies inside one open square [OPEN]

There is at most one such square. Its other eight squares require a
global angular/support argument. At q_*>4 the n=8 small-core
constants are inapplicable without new proof. Establish either a
direct q≥q_* obstruction or a certified implication into the
G1 terminal pattern. Deal with arbitrary orientations and contacts.

### G2.2 — Origin lies on square boundary but inside no square [OPEN]

This branch includes the record construction and is therefore
**essential at equality**. Determine a rigorous finite description
of the central seam/corner possibilities, from which the needed
four-versus-three support chains (or alternative terminal structures)
follow. The record's two middle squares sharing an edge is an
example, not a universal normalization.

### G2.3 — Origin is outside every closed square [OPEN]

Derive a circle/angular-budget or support-width bound for the nine
exterior squares. Explicitly account for arcs of a square that may
be disconnected and for arbitrary rotations. Close by excluding the
branch at q≤q_* or routing it to a proved G1/G3 terminal theorem.

### G2.4 — Prove structural coverage [OPEN]

Write an explicit theorem with conclusion a **finite disjunction** of
named terminal patterns and with original hypotheses only:
\[
 \mathrm{Packing}_9(q)\ \wedge\ q\le q_*
       \Longrightarrow
       \mathcal P_{4,3}\ \vee\
       \mathcal P_{3,4}\ \vee\
       \mathcal E_1\ \vee\cdots\vee \mathcal E_k . \tag{E}
\]

The alternatives E_j must be explicitly defined geometric invariants,
not strings like "all other cases". Every alternative must be routed
to a named analytic proof gate in G3. It is acceptable to change the
proposed terminal pattern if G1 fails; it is not acceptable to leave an
unnamed residual class.

**Gate G2 closes iff** (E) is proved for **all nine freely oriented
squares** and every central-incidence case is accounted for. Proving
a single 2--4--3 subfamily, or 3/4/5/6-square classifications in
succession, is not closure.

## G3 — Eliminate all exceptional structural branches [OPEN]

For each E_j returned by G2, give a hand theorem of the form
\(E_j\Longrightarrow q\ge q_*\), or show that E_j reduces by a
valid geometric deformation/support argument to G1.

Potential common tools: cyclic marker angles, a global
projection-capacity inequality, and supporting-line dual stresses.
A proposed deformation must preserve containment and disjoint
interiors throughout; moving freely positioned squares to a
template without such a proof is invalid. If a claimed bound is
false, produce an exact counterexample and revise the structural
alternative rather than creating arbitrary parameter subdivisions.

**Gate G3 closes iff** the finite disjunction in (E) has **no
unresolved leaf**. Each leaf points to a proved terminal theorem;
the entire ledger is independently checkable on a page or two.
Avoid huge generated tables, even if their number of cells is
technically finite.

## G4 — Unrestricted sharp-radius hand theorem [OPEN]

Combine G0's construction with G1, G2 and G3 to prove (T)
with only the original Packing assumptions. Check all equality
and strict-boundary cases; a proof only for q<q_* gives the lower
bound but is insufficient by itself for the equality theorem.

**Closure criterion:** one self-contained unrestricted theorem with
a complete dependency graph and no unpublished certificates,
"all remaining cases" placeholders, or hidden restrictions on
orientations.

## G5 — Complete equality packing classification [OPEN]

### G5.1 — Classify equality skeletons [OPEN]

Rerun G2/G3 using q=q_* **without discarding equality
alternatives**. Determine which terminal patterns permit q=q_*.
Do not infer uniqueness from an inequality whose zero set was
not analyzed.

### G5.2 — Recover rigid anchors [OPEN]

In the aligned 4+3 branch, use [HAND_PROOF.md](HAND_PROOF.md),
§6: center x-coordinates are exactly
\[
 M:\ -3/2,-1/2,1/2,3/2,\qquad
 B:\ -1,0,1,
\]
with four outer anchor squares pinned in both coordinates.
Establish from G1's equality cases when alignment itself is
forced. Allow additional equality skeletons if G5.1 requires them.

### G5.3 — Give necessary-and-sufficient freedom parameters [OPEN]

Describe the remaining interior sliders and last two squares with
independent centers/orientations by exact circle-corner and
separating-axis inequalities. Simplify them to a concise
geometrically meaningful parameter domain; do not merely restate
Packing over nine unknown squares. The rotated witness in
NONRIGID_WITNESS.md must be included.

### G5.4 — Prove converse and quotient by congruence [OPEN]

For every allowed parameter choice, prove containment and all
pairwise nonoverlaps. Conversely, prove every equality packing has
one of the listed forms. Explain reflection and relabeling as
required by the exact Congruent convention; do not assert
discrete uniqueness when continuous freedom exists.

**Gate G5 closes iff** necessity, sufficiency, and full symmetry
quotient are proved for all equality packings.

## G6 — Independent, table-free hand-proof audit [OPEN]

Produce a consolidated manuscript with a proposition/lemma ledger.
Audit independently:

- all exact corner and support identities, signs and root branches;
- every case in (E), including equality, tangency, contact at a
  square vertex, and squares with multiple feasible separators;
- every application of a strict inequality in a closed-disk
  problem;
- negative controls N1--N3 and any exact disproof discovered;
- construction, unrestricted lower bound, and equality converse.

Accept algebraic identities and a few exact rational comparisons.
Reject silent numerical optimization, parameter discretization
that is not independently certified, and an alleged hand proof
whose central work is a large generated table.

**Gate G6 closes iff** every mathematical lemma can be reviewed
from the manuscript without executing a program. The final
status must distinguish hand-verified from Lean-verified claims.

## G7 — Lean 4 formalization in dependency order [NOT STARTED]

Start **only after** G6's complete hand proof. Preserve the
project's existing unrestricted square model, natural statements,
and Palomar-style kernel-checking standard.

- **G7.1:** state the n=9 radius, witness, and formal equality
  family; show the model is nonempty.
- **G7.2:** formalize the exact support/corner formulas, the
  separating-axis condition (SAT), and the now-completed hand
  cap-row and seven-anchor theorems in ORIENTATION_STABLE_SEVEN_ANCHOR.md.
- **G7.3:** formalize G2's full structural coverage with no
  unrestricted assumptions replaced by an ad hoc normal form.
- **G7.4:** implement every G3 terminal case and assemble the
  radius lower bound and full equality reconstruction.
- **G7.5:** compile the actual final theorem, inspect its axiom
  dependencies, and perform an independent kernel/Palomar replay.
  No native-kernel shortcuts, external proof oracles, or admitted
  axioms.

A source draft, even with no textual sorry/admit, is not a
compiled proof. A Lean theorem whose normalization hypothesis
is stronger than Packing does not close G7.

## G8 — Public integration and handoff [NOT STARTED]

Integrate n=9 into the existing Optimum, optimalRadius and
optimalPackings interfaces, Challenge mirror, README, illustrated
proof documentation, and theorem/equality statements. Keep
precise commit-time provenance and a clean change ledger.
Update PR #11 from draft only after the hand proof and compiled
formal proof are fully verified. Preserve the previous n=1--8
theorems and do not merge until regression checks pass.

## Work selection, falsification and stopping rules

1. **Immediate priority:** attack G2.2 (center on a seam), since
   the record packing lies there. The exact G1 terminal lemma is
   available; find a global extraction theorem that actually supplies
   its projection-separation and cross-group support-order hypotheses.
2. **In parallel:** investigate G2.1 (center in an open square) and
   G2.3 (origin outside the union). Any exceptional pattern must have
   a named, independently proved terminal geometric obstruction.
3. **Checkpoint:** no large-scale case classification until its
   terminal inequalities and complete coverage theorem are
   precisely formulated. An "exhaustive classification" must
   reduce *all* nine-square packings, not merely a particular
   boundary arrangement.
4. **If a proposed gate is false:** archive a simple exact
   counterexample, mark the statement REJECTED, and make one
   structural pivot (e.g. dual support rather than layer
   extraction). Do not keep narrowing to infinitesimal
   subclasses of a failed claim.
5. **If q_* itself is beaten:** verify a strictly smaller
   packing by exact inequalities, mark the conjectured lower
   bound false, and replace the target rather than continuing a
   proof of a false theorem.
6. **Per-commit deliverable:** a named proposition, proof or
   explicit obstruction; updated status, dependencies, and
   exact commit time. Research-only commits use [skip ci].
   No claim of Lean/kernel checking before G7.5.
7. **No fake completion:** the only proofs currently closed
   are G0's exact constructions and conditional geometric
   results. G1 and G2 are genuinely open; neither is currently
   known to be obtainable by a short argument.

## Live status ledger

| Gate | Mathematical deliverable | State | Blocks |
|---|---|---|---|
| G0 | Construction, conditional bounds, false-shortcut tests | CLOSED (hand) | None |
| G1 | Orientation-stable seven-anchor obstruction | CLOSED (hand) | None |
| G2 | All-packings structural coverage (three origin states) | OPEN | G3, G4 |
| G3 | Analytic closure of every exceptional alternative | OPEN | G4 |
| G4 | Global sharp lower bound | OPEN | G5 |
| G5 | Every equality packing, both directions | OPEN | G6 |
| G6 | Independently auditable table-free hand manuscript | OPEN | G7 |
| G7 | Lean kernel-verified theorem and classification | NOT STARTED | G8 |
| G8 | Public interfaces, docs, validation, PR close | NOT STARTED | — |

**Next mathematical checkpoint:** derive a genuinely unconditional
support/center-seam lemma for G2.2 and complete the finite coverage
implication (E). The G1 terminal theorem is now available, but G2
must show it applies (or handle every exception) from unrestricted
Packing hypotheses.
