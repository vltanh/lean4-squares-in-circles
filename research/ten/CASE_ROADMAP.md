# The n=10 case tree and proof progress

The unrestricted lower bound is **not proved**. This ledger states exactly
which finite families remain, and separates a closed case from a useful
lemma that does not close its family. All lower-bound cases below concern
`R^2<9/2`; equality and Lean integration have separate gates.

<!-- CASE_PROGRESS_START -->
**Main gates:** `███░░░░` **3/7 closed**.

**G3 lower-bound case ledger:** `███████████████░░░░░░`
**15 hand closed · 0 computer closed · 6 open / 21 terminal families.**

**C20 larger-cycle subcases:** `█▎░░░░░░░░░░░░░░░░░░░░░░` **15/279 closed; 264 open.**

`█` reviewed hand deduction; `▓` reviewed computer-assisted result; `░` open. These are counts of the fixed ledger entries, **not a percentage of the proof or remaining effort**. Every currently closed family has a reviewed hand deduction; imported dependencies remain as stated in each proof.

| Gate | Obligation | Status |
| --- | --- | --- |
| G0 | Physical model and existence | CLOSED |
| G1 | Exact attaining construction | CLOSED |
| G2 | Sharp common-coordinate theorem | CLOSED |
| G3 | Unrestricted lower bound | OPEN |
| G4 | Unrestricted equality classification | OPEN |
| G5 | Lean formalization and kernel checks | OPEN |
| G6 | Public integration | OPEN |

| ID | Status | Exact family and current evidence |
| --- | --- | --- |
| C00 | HAND CLOSED | **Acyclic positive component.** Every nonzero tree component. [Proof / reduction](EXPANDED_TREE_INVENTORY.md). |
| C01 | HAND CLOSED | **Entirely loaded cyclic component that is not a seven-body simple cycle.** The all-loaded reduction forces an enclosing seven-cycle in a strictly subcritical ten-packing. [Proof / reduction](ALL_LOADED_COMPONENT_RINGS.md). |
| C02 | HAND CLOSED | **Seven loaded bodies with a common signed frame offset.** Includes the smooth uniform ring and the radial-side/diagonal endpoints. [Proof / reduction](REGULAR_SEVEN_LOADED_RING.md). |
| C03 | HAND CLOSED | **Nonuniform strict one-chirality seven-ring.** After C02: the fixed side/vertex pattern, allowing reflection and cyclic relabeling. A hand cap theorem traps all three inner squares below the three-square minimum radius. [Proof / reduction](SEVEN_RING_RADIAL_CAP_BOUND.md). |
| C04 | OPEN | **Other seven-loaded-ring contact ownership.** After C02 and C03: other vertex/edge ownership, geometric circle-contact types, or boundary degeneracies. [Proof / reduction](SEVEN_RING_INTERNAL_CONCURRENCE.md). |
| C05 | OPEN | **Mixed cyclic component whose whole graph is not a simple cycle.** Includes branching cyclic blocks and bridges attached to cyclic blocks; two loaded bodies are allowed here. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C06 | HAND CLOSED | **Mixed simple cycle of length at most four.** All load assignments. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C07 | HAND CLOSED | **Mixed simple cycle of length at least five with at most two loads.** The two-terminal transmission-path theorem applies to a whole simple cycle. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C08 | HAND CLOSED | **Five-cycle with three loads and adjacent unloaded bodies.** The middle loaded body touches every other loaded body. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C09 | HAND CLOSED | **Three-loaded five-cycle with radial-side central body.** Nonadjacent unloaded bodies; the central loaded square has two geometric circle vertices. S-S, mixed S-D, and D-D are all excluded. [Proof / reduction](RADIAL_SIDE_DD_EXCLUSION.md). |
| C10 | HAND CLOSED | **Unique-circle-vertex central body: parallel transmissions.** Nonadjacent unloaded bodies; apply this predicate before C11–C17. [Proof / reduction](PARALLEL_MIXED_FIVE_CYCLE.md). |
| C11 | HAND CLOSED | **Unique-circle-vertex central body: coincident contacts.** After C10; equal and mixed transmission types are excluded. [Proof / reduction](COMMON_CORNER_MIXED_TRANSMISSIONS.md). |
| C12 | HAND CLOSED | **Unique-circle-vertex central body: two distinct vertex contacts.** After C10–C11. [Proof / reduction](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md). |
| C13 | HAND CLOSED | **Unique-circle-vertex central body: two side-normal transmissions.** After C10–C12; includes two side-interior contacts. [Proof / reduction](SIDE_NORMAL_MIXED_FIVE_CYCLE.md). |
| C14 | HAND CLOSED | **Remaining vertex/side pattern: D-D.** First letter is the transmitter at the central vertex contact; second is at the side-interior contact. [Proof / reduction](DIAGONAL_MIXED_FIVE_CYCLE.md). |
| C15 | OPEN | **Remaining vertex/side pattern: S-S.** Same ordered convention as C14; a vertex-supported first endpoint cannot have a rightward incident edge. Side contacts and other vertex orientations remain open. [Proof / reduction](SIDE_TRANSMISSION_VERTEX_REDUCTION.md). |
| C16 | OPEN | **Remaining vertex/side pattern: S-D.** Same ordered convention; the first loaded endpoint must be contacted in a relative side interior. [Proof / reduction](SIDE_TRANSMISSION_VERTEX_REDUCTION.md). |
| C17 | HAND CLOSED | **Remaining vertex/side pattern: D-S.** Same ordered convention; endpoint classification and a printed exact clearance table exclude both remaining circle-load patterns. [Proof / reduction](DIAGONAL_SIDE_EXCLUSION.md). |
| C18 | HAND CLOSED | **Five-cycle with four loads: side transmitter.** Its only unloaded body is a degree-two side transmitter. [Proof / reduction](MIXED_FIVE_FOUR_LOADED.md). |
| C19 | OPEN | **Five-cycle with four loads: diagonal transmitter.** Its diagonal transmitter contains zero in its interior and has center norm below 3/5; completion capacity remains open. [Proof / reduction](MIXED_FIVE_FOUR_LOADED_GEOMETRY.md). |
| C20 | OPEN | **Mixed simple cycles of lengths six through ten.** At least three loaded bodies; finite cyclic load words with S/D transmission decorations. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
<!-- CASE_PROGRESS_END -->

## How the case tree is exhaustive

Take a hypothetical strictly subcritical ten-packing and a radius-minimizing
packing no larger than it. The physical stress certificate supplies a
nonzero positive component; its source and radius dependencies are pinned
in [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) and
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md). Every such component
has at most ten bodies and at most seven loaded bodies. An unloaded set with
at most one outside neighbor is impossible by the force-sum argument. This
excludes zero or one loaded body in a component with other bodies. An
isolated loaded body is also impossible: balanced circle loads would put
zero in the convex hull of its circle vertices, contrary to its diameter
and the radius window. In particular, **two loaded
bodies remain allowed in the branching family C05**.

Choose any one nonzero positive component and follow this tree. Tests at
each node are ordered, so a configuration belongs to one terminal family.
`H`, `C`, and `O` mean hand closed, computer closed, and open.

```text
Nonzero minimizing positive component
├─ Acyclic ............................................... C00 H
└─ Contains a cycle
   ├─ Every body is loaded
   │  ├─ Not a seven-body simple cycle .................... C01 H
   │  └─ Seven-body physical ring
   │     ├─ Common signed frame offset ................... C02 H
   │     ├─ Otherwise, strict one-chirality ownership ..... C03 H
   │     └─ Other contact ownership / boundary cases ...... C04 O
   └─ Some bodies are unloaded
      ├─ Whole graph is not a simple cycle ................ C05 O
      └─ Whole graph is a simple cycle
         ├─ Length <=4 ................................... C06 H
         ├─ Otherwise, <=2 loaded bodies .................. C07 H
         └─ Length >=5 and >=3 loaded bodies
            ├─ Length five, three loaded bodies
            │  ├─ Unloaded bodies adjacent ............... C08 H
            │  └─ A-U-C-V-B-A; C meets both transmitters
            │     ├─ C has two geometric circle vertices .. C09 H
            │     └─ C has one geometric circle vertex
            │        ├─ Parallel transmissions ........... C10 H
            │        ├─ Otherwise, coincident C contacts .. C11 H
            │        ├─ Otherwise, two vertex contacts .... C12 H
            │        ├─ Otherwise, two side normals ....... C13 H
            │        └─ Remaining vertex/side normal form
            │           ├─ D-D ........................... C14 H
            │           ├─ S-S ........................... C15 O
            │           ├─ S-D ........................... C16 O
            │           └─ D-S ........................... C17 H
            ├─ Length five, four loaded bodies
            │  ├─ Unloaded transmitter S ................. C18 H
            │  └─ Unloaded transmitter D ................. C19 O
            └─ Length six through ten .................... C20 O
               └─ 80 load-word families / 279 S-D cases
```

The entirely loaded ring theorem supplies the first major reduction.
For mixed simple cycles, the cyclic-stress reductions eliminate small
cycles and two-terminal cycles. A three-loaded five-cycle has either
adjacent unloaded bodies or the displayed unique central body C. C has
one or two geometric circle vertices in the radius window. In the unique
vertex branch, the contact reductions prove that all remaining cases have
exactly one vertex contact and one side-interior contact. The four ordered
S/D choices are then exhaustive. The first letter always belongs to the
transmitter at C's vertex contact.

This is a **finite partition into proof families**, not a claim that there
are finitely many geometric packings. Each family still permits continuous
coordinates, orientations, and positive force magnitudes.

## What is left, concretely

There are six open physical families. Every closed family in the main
ledger now has a reviewed hand deduction, with its imported dependencies
stated in the linked proof:

| Family | Next result needed |
| --- | --- |
| C04: other loaded-ring ownership | Classify and exclude the remaining contact patterns, or prove one capacity theorem covering all of them. The strict one-chirality theorem does not cover mixed ownership, vertex/vertex contacts, or its boundary cases. |
| C05: branching mixed components | Classify or exclude the connected cyclic graphs that are not whole simple cycles, including bridge attachments and exactly two loaded bodies. |
| C15: unique-circle S-S five-cycle | Exclude the remaining exact vertex/side core, or prove its completion has capacity at most nine. |
| C16: unique-circle S-D five-cycle | Exclude the side-interior first-endpoint case, or bound every completion by nine. |
| C19: four-loaded five-cycle with D | Exclude this component or its ten-square completion. |
| C20: larger mixed simple cycles | Exclude the [279 enumerated graph/transmitter cases](CYCLE_CASES.md), refining physical contact ownership where needed. |

The recently proved two-row, block, cap, channel, and corner-moment lemmas
are tools for these obligations. A proof for a special core does **not**
close a leaf unless every configuration in that leaf has been reduced to
that core.

## The two broad finite families are still classification work

**C04, seven-loaded ownership.** First relabel each square's local frame so
its geometric circle vertex, or adjacent circle-vertex pair, has a canonical
label. A fully explicit finite encoding then uses, for
each of seven bodies, its circle-contact type (one geometric vertex, or two
with the first, second, or both weights positive) and the incidence of each
of its two original pair-contact points (one of four vertices or one of four
relative side interiors). This gives at most `4^7 * 8^14 = 2^56` labeled
incidence records before symmetry, force, and geometry restrictions. The
normal at a vertex ranges over its supporting cone; it is not replaced by
an edge normal. The records are finite, but this enormous raw list has
**not** been reduced to a practical audited catalog. That reduction is an
open subgate of C04. Alternatively, a theorem covering all records closes
the family directly.

**C05, branching mixed graphs.** A precise finite envelope consists of
`m<=10` labeled vertices, an edge mask in `{0,1}^{m choose 2}`, and a loaded
subset of size `2..min(7,m-1)`. Keep connected graphs containing a cycle
and at least one vertex of degree at least three. Contacts retain their
vertex/side incidence and physical force witnesses. This includes cyclic
blocks joined by bridges. The degree-two S/D reduction applies only to
vertices of degree two in the **whole positive graph**. The list has not
been enumerated or reduced by graph isomorphism here; it is a finite,
explicitly defined remaining family, not a closed classification theorem.

**C20 is already enumerated.** [CYCLE_CASES.md](CYCLE_CASES.md) lists all
279 stable case IDs and their canonical words. Independent enumerations and
a Burnside count check the complete [manifest](cycle_cases.json). The live
bar above and the inventory give the current closed/open counts, with a
proof link for every exclusion. The latest exclusions use
[seven-loaded path adjacency](SEVEN_LOADED_LONG_PATHS.md) and
[shared-endpoint angular budgets](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md).
An entry is never claimed feasible or excluded merely because it appears
in the list.

## Orthogonal filters and later gates

The center-radius route gives an independent filter:

```text
Centers in the open unit disk:  <=2 [CLOSED]  3 [OPEN]  4 [OPEN]  5 [CLOSED]
```

The moment theorem rules out five; the center-radius theorem closes at
most two. At most five is already proved. The stress tree above covers the
remaining three- and four-inner-center possibilities jointly. These filters
are **not additional terminal leaves** and are not added to the progress
count. Four-center radial localization remains a separately labeled
computer-assisted input, not a hidden premise of every hand theorem.

G4 requires the equality classification at `R^2=9/2`, particularly the
three- and four-inner-center classes. The strict-subcritical stress ledger
does not automatically settle equality. G5 requires Lean statements,
elaboration, axiom review, and kernel verification; no n=10 Lean theorem
has been compiled here. G6 follows only after those gates close.

## Updating the progress bar

The source of the family statuses is [case_progress.json](case_progress.json).
After a reviewed result closes an entire leaf, update that leaf's status and
evidence, then run:

```sh
python3 research/ten/check_cycle_cases.py
python3 research/ten/update_case_roadmap.py
```

The renderer updates this ledger, the README progress bars, and the larger
cycle index. The 21-family denominator is the fixed first version of the
ledger. If a broad family is refined, record the partition change explicitly;
do not present the changed denominator as mathematical progress.
C20 closures are tracked separately in [cycle_progress.json](cycle_progress.json),
so the original inventory remains a stable denominator. Add a reviewed proof
reference there when an entire graph/transmitter case is excluded.
