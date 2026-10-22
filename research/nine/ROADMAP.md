# n=9 research roadmap: geometric proof without large tables

## Goal and verification discipline

Target: prove, from the unrestricted repository definition
\(\mathrm{Packing}\), that nine independently rotatable unit squares
require squared containing radius at least
\[
                  q_*=\frac{1105}{256},
\]
and ultimately classify every attaining configuration.

Prefer geometric and analytic arguments: supporting lines, angular
order, convexity, and exact inequalities with a fixed small number of
geometrically meaningful cases. Do **not** replace a missing structural
lemma by sampling poses, enumerating tiny parameter boxes, or classifying
one of infinitely many subclasses. A diagram, numerical optimizer, or
uncompiled Lean draft cannot discharge a global hand-proof gate.

This branch is scoped to n=9 and makes no change to the existing n=1--8
theorems.

## Completed results (proved hand arguments)

| Gate | Result | Source | Status |
|---|---|---|---|
| A0 | Exact 2--4--3 nine-square construction at \(q_*\) | HAND_PROOF.md, Section 1 | **CLOSED** |
| A1 | Horizontally separated groups have explicit \(m=1,2,3,4\) capacity bands | HAND_PROOF.md, Section 3 | **CLOSED** |
| A2 | Four horizontally separated squares entirely above three horizontally separated squares, all sharing a frame, force \(q\ge q_*\), even with vertical staggering | HAND_PROOF.md, Section 4 | **CLOSED** |
| A3 | Every *horizontally stratified* nine-square packing has \(q\ge q_*\), with a five-case hand classification by number of layers | HAND_PROOF.md, Section 5 | **CLOSED** |
| A4 | Equality rigidly pins the two outer squares in the four-group and the two outer squares in the three-group, while internal heights may slide | HAND_PROOF.md, Section 6 | **CLOSED within the A2 hypothesis** |
| A5 | An exact record-radius packing with one rotated and eight axis-parallel squares; no global common frame can be assumed for every equality packing | NONRIGID_WITNESS.md | **CLOSED** |

All closed gates are mathematical hand arguments. None is claimed to
be Lean compiled. In particular A2--A4 have nontrivial structural
hypotheses.

## Remaining unrestricted gates

### G1. Seven-anchor geometric pattern: OPEN

Starting with nine arbitrary square orientations and \(q<q_*\), find an
unconditional geometric dichotomy that exposes the source of the
2--4--3 packing obstruction without assuming a grid. A candidate is a
direction \(e\), its perpendicular \(e^\perp\), and two groups of four
and three squares with separated projections along \(e\) and separated
supports along \(e^\perp\). If that pattern cannot always be extracted,
identify a small number of genuinely different alternatives and prove
a direct obstruction for each.

**Not established:** every axis-parallel packing has a horizontal
stratification; every arbitrary packing has seven parallel squares;
every optimal packing has all nine squares parallel. The last would
give a false equality statement by A5.

**Closure criterion:** every configuration satisfying the *original*
packing predicate enters an explicitly proved terminating branch.
A list of promising examples or a list of subfamilies is insufficient.

### G2. Orientation-stable support inequality: OPEN

A2 assumes the seven anchors share an orientation. Replace this by an
analytic inequality that allows independent square frames and
separation along *actual* supporting axes. Useful exact ingredients:

- For a square with center \(c\), orthogonal edge directions \(u,v\),
  and \(|u|=|v|=1\), its maximal corner squared norm is
  \[
   |c|^2+\tfrac12+|c\cdot u|+|c\cdot v|.
  \]
- In any fixed direction \(e\), its projection width is
  \(|e\cdot u|+|e\cdot v|\ge1\), with equality precisely at an
  edge-aligned direction.
- The four-square row and three-square row in A2 saturate *different*
  circle-corner bounds, so the proposed analytic certificate should
  couple horizontal span, vertical ordering, and orientation.
  Single-direction width bounds alone miss the upper/lower corner
  trade-off.

Seek a small exact dual-weight or convexity identity in which the
positive terms represent rotations and separator slack; ideally the
A2 inequality is its zero-tilt specialization. Beware using a fixed
separating direction at contacts when tilted squares may use a
different true support line.

**Closure criterion:** a proved lower bound \(q\ge q_*\) for the
geometrically stated pattern produced by G1, without assuming exact
alignment. The equality implications must be justified, not inferred
from pictures.

### G3. Other contact patterns: OPEN

If G1 yields branches beyond seven anchors, exclude them by global
geometric invariants (projection capacities, circular arc measures,
or a small cyclic separator classification). Do not proliferate
arbitrary numerical thresholds. Reuse exact \(q_*\) instead of
introducing decimal enclosures.

**Closure criterion:** finitely many *structural* alternatives, each
excluded or mapped to G2 by a proof.

### G4. Unrestricted attaining-family classification: OPEN

After G1--G3 close the radius theorem, recover all equality packings.
A4 gives rigidity of four extremal boundary squares in the aligned
anchor pattern, but does not determine all interior sliders or the
two remaining squares. A5 already proves that individual rotations
of nonanchor squares are possible at record radius.

**Closure criterion:** necessary *and* sufficient parameters for all
unrestricted equality packings, including rotated/free squares,
up to the repository's exact congruence convention.

### G5. Lean formalization: NOT STARTED

Only after a complete unrestricted hand proof has been independently
audited, translate the named analytic lemmas into Lean 4 using the
repo's Geometry/Packing definitions. Keep symbolic rational
inequalities short. Do not introduce numerical tables, external
certificate axioms, or unsupported missing lemmas.

## Priority

Work on **G2's orientation-stable seven-anchor estimate** together
with **G1's structural extraction**. A proof of A2 for another small
subset of configurations is not closure unless it has a route into
G1--G3. If a G1 extraction conjecture fails, find and write an
explicit geometric counterexample before modifying the roadmap.

## Handoff status

At this checkpoint, a short, exact and noncomputational hand proof
is complete for the stratified case, and a nonparallel record-radius
construction is verified. There is **no unrestricted n=9 lower bound**,
no equality classification, and no Lean formalization in this branch.
