# n=9: current physical-stress extension of the deep roadmap

This is the latest extension of the O3.1 reductions in
[DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md) and
[G2_SUBGATES.md](G2_SUBGATES.md). The earlier distinctions between
the 19-term planar translational certificate and the 27-atom
selected-owner angular certificate remain correct. A **third,
stronger physical incidence certificate** is now proved below.
The unrestricted sharp bound and global equality necessity remain OPEN.

## New gate O3.1f — physical contact points and simultaneous incidence planarity [CLOSED hand]

**Source:** [PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md).

### O3.1f.1 — Local contact-type cover [CLOSED]
Every touching square pair has either a single vertex/edge contact,
a single vertex/vertex contact, or a positive-length common side.
These cases cover all arbitrary orientations and all degeneracies.
Noncontacting pairs stay disjoint in a sufficiently small open
neighborhood and impose no active contact row.

### O3.1f.2 — Smooth sufficient branches with genuine levers [CLOSED]
- A vertex/edge contact uses its edge owner's varying normal and
  the other square's unique support corner.
- A point-only vertex/vertex contact admits a fixed normal strictly
  exposing both corners.
- A positive-length side contact uses the two **actual overlap
  endpoints**, one corner from each square. Requiring their two smooth
  inequalities is a sufficient local feasible branch: one or the other
  is the full SAT condition according to the sign of relative rotation.

The partial-side contact is essential. Merely differentiating all
support vertices of one owner can assign forces outside the actual
shared segment. The two-endpoint construction avoids that defect.
All active gradients are exact equal-and-opposite normal forces at
points physically belonging to both squares.

### O3.1f.3 — Joint physical equilibrium with <=27 atoms [CLOSED]
The center-expansion / radius-increase direction strictly decreases
all active constraints. The finite conic argument therefore gives
normalized nonnegative circle and contact multipliers satisfying
**both** center force balance and angular balance with their true
contact-point lever arms. Global infinitesimal rotation removes one
dimension, so <=27 positive scalar atoms suffice for nine squares.
The fixed-frame center dual is attained at the minimizing q0.

### O3.1f.4 — Aggregate and embed the actual contact incidence network [CLOSED]
Combine the two collinear endpoint forces on a shared side into one
force at their weighted average, which remains in the shared segment.
For each distinct actual application point create a junction node;
join it to the centers of the incident stressed squares. Segments
are interior to their own square except at their contact endpoint,
so this is a **straight-line planar incidence network**.

A contact junction has degree 2, 3 or 4; the force vectors there sum
to zero. All circle-loaded square nodes are incident to its exterior
face. Force and angular balances remain exact because the physical
application points are retained. Select one connected positive-stress
body component and normalize its circle weights if needed.

**Nonclaim:** the simple square-to-square graph may still be nonplanar
at a four-way junction. This theorem uses contact-point vertices.
It does not merge the older 19-term certificate with torque equations.

### O3.1f.5 — Unloaded two-force squares have discrete frames [CLOSED]
After aggregating each body pair, an unloaded square of degree two
has equal opposite forces. Angular balance makes their two physical
application points collinear with the force direction. The square
therefore transmits either across opposite sides (width 1) or across
opposite corners (width sqrt(2)). No other orientation is possible
for that square relative to the force line.

### O3.1f.6 — Four exact square-ended transmission reserves [CLOSED]
For a path between two retained **square** endpoints whose internal
squares are unloaded degree-two transmitters, the exact gap adds
the endpoint halfwidths and all internal widths. At q0<=Q, the
center diameter is <61/20. Consequently the internal reserve is one
of **0, 1, sqrt(2), 2**. The reserve 2 consists of two side-normal
squares; two internal squares with even one diagonal transmitter
are impossible. Three internal squares are also impossible.

Do not apply this bound to paths ending at contact-junction points
rather than square centers. Do not infer a simple planar body graph
by contracting across a junction with other incidences.

## Completed regression subgate (not independent proof audit)

[check_physical_contact_stress.py](check_physical_contact_stress.py)
was executed after its bytes and imported dependency were matched to
the committed Git blobs. [PHYSICAL_STRESS_EXACT_CHECK.json](PHYSICAL_STRESS_EXACT_CHECK.json)
records the source hash, Python version, UTC execution time and exit 0.
All seven concrete pair-force application points lie in the actual
intersections and correct support faces; all nine physical force and
angular residuals vanish. Exact rational rotations check the local
two-endpoint/support identities. These are finite regression checks,
not a proof of global optimality or an independent manuscript audit.

## Remaining O3.2–O4: unchanged logical goal, stronger available input

The missing theorem now has these proved inputs for every hypothetical
unrestricted subcritical minimizing packing:

1. There is an actual-contact **physical force-and-angle** certificate
   with <=27 atoms and a planar contact-incidence drawing.
2. The circle-loaded square nodes are on the outer face; unloaded
   two-force squares have only the two exact transmission frame types.
3. There are exactly nine physical squares in the full packing,
   whether or not they receive nonzero stress.

**Still required:** classify the remaining loaded/branching core and
its unstressed-square completions exhaustively and prove q0>=Q by a
short orientation-uniform inequality, or prove one global invariant
covering them all. Physical network stationarity is necessary, not
sufficient for minimizing the nonconvex orientation problem. The
existence and sparsity theorems do not evaluate the unknown q0.

## Gate ledger after this extension

| Gate | State |
|---|---|
| G2.C whole common-coordinate class | CLOSED hand |
| O3.0.2 compact minimizer / attained exact stress | CLOSED hand |
| O3.1a–d planar <=19-term translational body core | CLOSED hand |
| O3.1e <=27-atom selected-owner angular certificate | CLOSED hand |
| **O3.1f.1–6 physical levers, joint incidence planarity, discrete transmitters** | **CLOSED hand** |
| O3.2–O3.3 sharp exhaustive core + completion types | OPEN |
| O4 uniform orientation inequality >=Q | OPEN |
| O5 / G2.X / G4 unrestricted lower bound | BLOCKED |
| G5.U unrestricted equality necessity/converse | OPEN/BLOCKED |
| G6 independent full hand audit | NOT COMPLETED |
| G7–G8 Lean/kernel verification and public integration | NOT STARTED |

No CI, Lean build, universal optimality, or end-to-end independent
verification is claimed. The new theorem narrows the actual global
contact structure; it does not close the sharp-radius gate by itself.
