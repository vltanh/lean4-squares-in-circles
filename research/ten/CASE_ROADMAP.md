# The n=10 case tree and proof progress

The unrestricted lower bound is **not proved**. The [fixed 336-family master ledger](MASTER_CASES.md) states exactly
which finite families remain, and separates a closed case from a useful
lemma that does not close its family. All lower-bound cases below concern
`R^2<9/2`; equality and Lean integration have separate gates.

<!-- CASE_PROGRESS_START -->
**Fixed strict-lower-bound master ledger:** `███████████████████▌░░░░` **273/336 closed; 63 open.** (273 hand; 0 computer-only.) [All stable IDs and the exact remaining obligations](MASTER_CASES.md).

The denominator is frozen: 19 other terminal families + 38 branching families + 279 cycle signatures. A branching family includes every permitted graph and continuous realization for its fixed `(k,b)`. These are proof-family counts, **not a percentage of effort or of the full n=10 deliverable**. Equality and Lean verification have separate gates.

**Main gates:** `███░░░░` **3/7 closed**.

**G3 lower-bound case ledger:** `███████████████████░░`
**19 hand closed · 0 computer closed · 2 open / 21 terminal families.**

**C20 larger-cycle subcases:** `█████████████████████▏░░` **246/279 closed; 33 open.**

C05 optional b=0 drilldown: 42,532/45,666 raw records excluded; 3,134 remain. [Catalog and certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md). 

C05 optional b=1 drilldown: 385,071/524,870 raw records excluded; 139,799 remain. [Catalog and proof decoder](BRANCHING_ONE_UNLOADED_FILTERS.md). Larger b is already covered by the fixed master families. These drilldowns do not add master progress.

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
| C04 | HAND CLOSED | **Other seven-loaded-ring contact ownership.** For the jointly selected certificate, outer-row extra corners have squared norm below 33/20. The enlarged core boundary and all SS/SV/VS/VV caps place the three inner squares below squared radius 83/50, contradicting 425/256. This closes every loaded seven-ring ownership pattern. [Proof / reduction](SEVEN_RING_COMPLETE_CAPACITY.md). |
| C05 | OPEN | **Mixed cyclic component whose whole graph is not a simple cycle.** Includes branching cyclic blocks and bridges. A universal hand theorem excludes exactly two loaded bodies for every b, so every remaining component has at least three loads. Existing fixed catalogs retain b=0 (3,134 remaining of 45,666) and b=1 (139,799 remaining of 524,870); b>=2 is one bounded remaining family. At most one distinct SS/effective-width-two endpoint pair occurs in the whole selected graph. [Proof / reduction](OUTER_CENTER_EXPOSURE_AND_WIDTH_TWO_UNIQUENESS.md). |
| C06 | HAND CLOSED | **Mixed simple cycle of length at most four.** All load assignments. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C07 | HAND CLOSED | **Mixed simple cycle of length at least five with at most two loads.** The two-terminal transmission-path theorem applies to a whole simple cycle. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C08 | HAND CLOSED | **Five-cycle with three loads and adjacent unloaded bodies.** The middle loaded body touches every other loaded body. [Proof / reduction](CYCLIC_STRESS_REDUCTIONS.md). |
| C09 | HAND CLOSED | **Three-loaded five-cycle with radial-side central body.** Nonadjacent unloaded bodies; the central loaded square has two geometric circle vertices. S-S, mixed S-D, and D-D are all excluded. [Proof / reduction](RADIAL_SIDE_DD_EXCLUSION.md). |
| C10 | HAND CLOSED | **Unique-circle-vertex central body: parallel transmissions.** Nonadjacent unloaded bodies; apply this predicate before C11–C17. [Proof / reduction](PARALLEL_MIXED_FIVE_CYCLE.md). |
| C11 | HAND CLOSED | **Unique-circle-vertex central body: coincident contacts.** After C10; equal and mixed transmission types are excluded. [Proof / reduction](COMMON_CORNER_MIXED_TRANSMISSIONS.md). |
| C12 | HAND CLOSED | **Unique-circle-vertex central body: two distinct vertex contacts.** After C10–C11. [Proof / reduction](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md). |
| C13 | HAND CLOSED | **Unique-circle-vertex central body: two side-normal transmissions.** After C10–C12; includes two side-interior contacts. [Proof / reduction](SIDE_NORMAL_MIXED_FIVE_CYCLE.md). |
| C14 | HAND CLOSED | **Remaining vertex/side pattern: D-D.** First letter is the transmitter at the central vertex contact; second is at the side-interior contact. [Proof / reduction](DIAGONAL_MIXED_FIVE_CYCLE.md). |
| C15 | HAND CLOSED | **Remaining vertex/side pattern: S-S.** Same ordered convention as C14; vertex exclusions and an analytic side-interior clearance proof rule out the entire S-S pattern. [Proof / reduction](SIDE_SIDE_EXCLUSION.md). |
| C16 | HAND CLOSED | **Remaining vertex/side pattern: S-D.** Same ordered convention; physical torque balance forces a far vertex to carry circle load, while elementary analytic bounds place it strictly inside the circle. [Proof / reduction](SIDE_DIAGONAL_EXCLUSION.md). |
| C17 | HAND CLOSED | **Remaining vertex/side pattern: D-S.** Same ordered convention; endpoint classification and a printed exact clearance table exclude both remaining circle-load patterns. [Proof / reduction](DIAGONAL_SIDE_EXCLUSION.md). |
| C18 | HAND CLOSED | **Five-cycle with four loads: side transmitter.** Its only unloaded body is a degree-two side transmitter. [Proof / reduction](MIXED_FIVE_FOUR_LOADED.md). |
| C19 | HAND CLOSED | **Five-cycle with four loads: diagonal transmitter.** For the generic selected certificate, D transmitter neighbors must be contacted in side interiors. The nearer-endpoint theorem forbids side support, excluding the component. The certificate is selected before classification. [Proof / reduction](DIAGONAL_FIVE_CYCLE_EXCLUSION.md). |
| C20 | OPEN | **Mixed simple cycles of lengths six through ten.** At least three loaded bodies. Reviewed cap, loaded-pair angle, and six-cycle arguments close 246 of 279 fixed signatures. Thirty-three remain: 11 at length six, 15 at seven, and 7 at eight. [Proof / reduction](CYCLE_CASES.md). |
<!-- CASE_PROGRESS_END -->

## How the case tree is exhaustive

Take a hypothetical strictly subcritical ten-packing and a radius-minimizing
packing no larger than it. The physical stress certificate supplies a
nonzero positive component; its source and radius dependencies are pinned
in [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) and
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md). Before classifying
its graph, choose the [generic contact normals](GENERIC_CONTACT_NORMAL_SELECTION.md)
that also avoid both incident square diagonals at point-only vertex/vertex
contacts. This preserves the earlier strict/nonradial convention and is
the selection used to close C19. It is an existence choice before the
multiplier theorem, not a modification keeping an older graph fixed.
The [finite concurrence-polynomial exclusions](LOADED_VV_GENERIC_RESTRICTION.md)
can be imposed jointly with those choices and give the stated additional
restriction on loaded-ring VV pairs.
The [planar selection theorem](PLANAR_SELECTED_PHYSICAL_STRESS.md) also
supplies a stress whose loaded vertices occur on the exterior face in
radial order. Its local force replacements are compatible with the generic
polynomial exclusions and the open normal intervals used in the ring
capacity proof. All these choices precede classification of the resulting
positive graph; planarity is not asserted for arbitrary earlier certificates.
Every such component
has at most ten bodies and at most seven loaded bodies. An unloaded set with
at most one outside neighbor is impossible by the force-sum argument. This
excludes zero or one loaded body in a component with other bodies. An
isolated loaded body is also impossible: balanced circle loads would put
zero in the convex hull of its circle vertices, contrary to its diameter
and the radius window. The new
[two-loaded component theorem](TWO_LOADED_COMPONENT_EXCLUSION.md) excludes
exactly two loaded bodies as well, for every graph and every b. Every
remaining positive component therefore has at least three loaded bodies.

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
   │     └─ Other contact ownership / boundary cases ...... C04 H
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
            │           ├─ S-S ........................... C15 H
            │           ├─ S-D ........................... C16 H
            │           └─ D-S ........................... C17 H
            ├─ Length five, four loaded bodies
            │  ├─ Unloaded transmitter S ................. C18 H
            │  └─ Unloaded transmitter D ................. C19 H
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

The [four-loaded diagonal five-cycle exclusion](DIAGONAL_FIVE_CYCLE_EXCLUSION.md)
uses this chosen certificate: generic normals make both D endpoint contacts
relative side interiors, whereas the nearer-endpoint theorem forbids side
support. All four-loaded five-cycles are therefore excluded in this route.

## What is left, concretely

There are two open physical families. Every closed family in the main
ledger now has a reviewed hand deduction, with its imported dependencies
stated in the linked proof:

| Family | Next result needed |
| --- | --- |
| C05: branching mixed components | Classify or exclude the connected cyclic graphs that are not whole simple cycles, including bridge attachments, with at least three loaded bodies. |
| C20: larger mixed simple cycles | Exclude the [279 enumerated graph/transmitter cases](CYCLE_CASES.md), refining physical contact ownership where needed. |

The recently proved two-row, block, cap, channel, and corner-moment lemmas
are tools for these obligations. A proof for a special core does **not**
close a leaf unless every configuration in that leaf has been reduced to
that core.

## Closed ring classification and the remaining mixed families

**C04 is now closed across every ownership pattern.** The fixed support
alphabet retains its 25 local symbols and 34 historical proper-contact
schemes as coverage data. The [complete capacity theorem](SEVEN_RING_COMPLETE_CAPACITY.md)
selects compatible normals before classifying the physical graph. Its
[outer-corner theorem](LOADED_OUTER_CORNER_CLEARANCE.md) bounds the extra
U4/U5 corners by squared radius 33/20. The
[enlarged core assembly](SEVEN_RING_OUTER_CORE_ASSEMBLY.md) includes those
corners and every radial, SS, SV/VS, and VV case. The old caps and the
[new outer caps](OUTER_SIDE_CAPACITY_MARGIN.md) then place every vertex
of all three inner squares below squared radius 83/50, contradicting
the three-square minimum 425/256. No enumeration of continuous ring
realizations is required. The normal choices are joint with the selected
planar certificate used in the remaining mixed-component families.

**C05, branching mixed graphs.** A precise finite envelope consists of
`m<=10` labeled vertices, an edge mask in `{0,1}^{m choose 2}`, and a loaded
subset of size `3..min(7,m-1)`. Keep connected graphs containing a cycle
and at least one vertex of degree at least three. Contacts retain their
vertex/side incidence and physical force witnesses. This includes cyclic
blocks joined by bridges. The degree-two S/D reduction applies only to
vertices of degree two in the **whole positive graph**.
The [reviewed skeleton reductions](BRANCHING_COMPONENT_SKELETON_DRAFT.md)
give degree and parallel-path restrictions. The subclass with every branch
vertex loaded (`b=0`) now has a fixed
[catalog of 45,666 stable cases](BRANCHING_LOADED_SKELETON_INVENTORY.md),
independently reproduced by Python and C++ enumerators. Each row records
the circular loaded order, path types, multiplicities, and body count.
The [combined exact graph certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md)
exclude 42,532 records and leave 3,134; this is an optional raw-code drilldown within the
fixed master families. Each angular rejection prints at most seven integer
inequalities summing to a contradiction.

The subclass with exactly one unloaded retained branch vertex (`b=1`)
now has a second fixed [catalog of 524,870 cases](BRANCHING_ONE_UNLOADED_INVENTORY.md),
independently enumerated in two different orders. Its
[proof decoder](BRANCHING_ONE_UNLOADED_FILTERS.md) excludes 385,071 and
leaves 139,799; the six cases with only two loaded vertices have a
[complete hand capacity exclusion](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md).
The code itself is the stable ID, and an exact list of remaining IDs can
be exported from regenerated catalogs. At least two unloaded retained
vertices (`b>=2`) remain outside both catalogs. Neither partial
classification closes C05.

The fixed master ledger covers all remaining branching graphs with
`3<=k<=7` and `0<=b<=10-k`: exactly 30 open pairs `(k,b)`.
The eight k=2 branching families are already hand closed. Every skeleton has at most
ten retained vertices and the fixed seven-symbol edge alphabet. There is
no unbounded sequence of strata. The research priority is now to prove
restrictions across this entire remaining family, rather than build
successively larger catalogs. The
[two-neighbor branch theorem](TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md)
already applies to every b: such branch vertices form an independent set,
cannot repeat a neighbor pair, and obey `k+b+2r<=10`. In particular there
is at most one in the entire selected component, and none when `k+b>=9`.
The stronger [outer-center exposure theorem](OUTER_CENTER_EXPOSURE_AND_WIDTH_TWO_UNIQUENESS.md)
allows at most one distinct endpoint pair among all actual SS paths and
effective width-two connections in the whole graph. These are universal
restrictions, not a plan to prove separate theorems for each successive
loaded count. The remaining goal is a structural or completion-capacity
argument covering the mixed family together.

**C20 is already enumerated.** [CYCLE_CASES.md](CYCLE_CASES.md) lists all
279 stable case IDs and their canonical words. Independent enumerations and
a Burnside count check the complete [manifest](cycle_cases.json). The live
bar above and the inventory give the current closed/open counts, with a
proof link for every exclusion. The latest exclusions use
[seven-loaded path adjacency](SEVEN_LOADED_LONG_PATHS.md) and
[shared-endpoint angular budgets](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md),
with [width-two path uncrossing](TRANSMISSION_PATH_UNCROSSING.md) extending
them to separated runs. The
[single-side uncrossing theorem](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md)
then forces radial loaded order when at most one diagonal occurs and
excludes the [117-case batch](single_side_cycle_batch.json). The
[D-D uncrossing theorem](DIAGONAL_PATH_UNCROSSING.md) now proves radial
order for every whole mixed simple cycle. Its
[206-case angular budget](RADIAL_ORDER_CYCLE_BUDGET.md) is strengthened by
the [cap-angle budget](SHARP_TRANSMISSION_CYCLE_BUDGET.md), which closes
234 entries. The [SS/D](SS_DIAGONAL_SIX_CYCLE_EXCLUSION.md) and
[SS/S](SS_SIDE_SIX_CYCLE_EXCLUSION.md) six-cycle exclusions, the
[D-path forest theorem](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md), and the
[two-D/one-S exclusion](TWO_DIAGONAL_ONE_SIDE_SIX_CYCLE_EXCLUSION.md)
give 238 closures. The [stronger loaded-pair angle](STRONG_DIRECT_CYCLE_BUDGET.md)
adds eight more, raising the total to 246 and leaving exactly 33 open:
11 at length six, 15 at length seven, 7 at length eight, and none at
lengths nine or ten.
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

## Shared reductions across the fixed open families

The [three-interior-body theorem](THREE_INTERIOR_BODY_REDUCTION.md) gives a
single bounded central graph problem: at most three physical body vertices
can fail radial exposure, regardless of k or b. All D/SS endpoints are
exposed in the same drawing. The [two-terminal patch theorem](TWO_TERMINAL_UNLOADED_PATCH_REDUCTION.md)
then reduces every connected unloaded set with exactly two outside neighbors
to one S, one D, or two to four S bodies in two columns. This applies even
when the terminals were not exposed in the original graph. Regions with
three or more terminals remain a common unresolved target.

[Bundle consolidation](DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md) supplies a further
packing-and-stress normalization eliminating double-S bundles. Its explicitly
listed certificate properties survive; compatibility with any additional
selection hypothesis must be checked before use. These universal reductions
advance the proof without adding master entries or treating partial reductions
as closed families.
