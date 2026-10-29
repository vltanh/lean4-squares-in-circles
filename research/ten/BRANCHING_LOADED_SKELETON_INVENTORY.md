# Finite branching skeletons when every branch vertex is loaded

**Status:** independently reviewed finite inventory and exact bridge/angular
exclusion deductions (2026-10-29), with the
[audit record](BRANCHING_LOADED_SKELETON_AUDIT.md). The full C05 family remains
open. This is only the subclass `b=0`:
every unloaded body has degree two in the whole positive component.

**Current combined progress:** the later
[cap-angle and SS-bridge certificates](BRANCHING_SS_BRIDGE_FILTER.md)
exclude **40,336 of these 45,666 fixed cases; 5,330 remain**. The original
two-filter counts below are preserved to make the successive deductions
and their overlap auditable.

The raw catalog has **45,666 stable cases**. Two exact necessary-condition
filters prove **37,949 exclusions**, leaving **7,717 cases**. These are
case counts, not claims of geometric feasibility or a percentage of the
unrestricted proof. Components with an unloaded branching vertex (`b>0`)
are outside this catalog and remain unenumerated here.

## 1. What the fixed catalog contains

Suppress only unloaded degree-two bodies. The reviewed
[skeleton reductions](BRANCHING_COMPONENT_SKELETON_DRAFT.md) give a
loop-free multigraph on its loaded endpoints, now all retained vertices.
The two-loaded case is already excluded by the reviewed two-terminal
theorem, so the catalog takes `3<=k<=7`. Label the loaded vertices by their
circular radial order `0,...,k-1`.

For each unordered pair, the alphabet and internal-body cost are:

| Digit | Meaning | Cost | Number of skeleton edges |
| --- | --- | ---: | ---: |
| 0 | Absent | 0 | 0 |
| 1 | Direct loaded contact | 0 | 1 |
| 2 | One side transmitter S | 1 | 1 |
| 3 | Two parallel S paths | 2 | 2 |
| 4 | One diagonal transmitter D | 1 | 1 |
| 5 | One two-side path SS | 2 | 1 |
| 6 | Two parallel SS paths | 4 | 2 |

A digit 3 is not a digit 5: the first is a parallel bundle, the second a
serial path. Every assignment must satisfy:

1. The total cost is positive, and `k+cost<=10`.
2. The multigraph is connected, has at least k edges, has maximum degree
   at least three, and has every degree at most eight. Thus it is mixed,
   cyclic, and not a whole simple cycle after subdivision.
3. A direct edge joins radial neighbors. For `k=3`, at most one direct
   edge is present: two would give a loaded body touching all other
   loaded bodies, excluded by the loaded-star semicircle argument.
4. Two transmission chords with four alternating endpoints must both be
   digit 4. The [single-side uncrossing theorem](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md)
   and its width-two dependency apply here to the corresponding
   vertex-disjoint paths, whose internal bodies have whole-graph degree two.
   Their local junction proofs do not restrict the degrees of the loaded
   endpoints; the later whole-cycle radial-order conclusions are not used.

The direct-contact radial-neighbor rule is valid also at k=3, where every
pair is a neighbor pair. For k>=4 it follows from loaded pair separations
greater than 36 degrees and direct-contact separations less than 72 degrees.
No planarity of the body-pair graph is used.

Quotient these records by rotations and reflections of the circular
labels only. Arbitrary graph isomorphisms are not used: the loaded radial
order remains part of the record. Each orbit is represented by the
lexicographically smallest digit string under those `2k` permutations.

## 2. Coverage checks and stable IDs

[check_branching_loaded_skeletons.py](check_branching_loaded_skeletons.py)
generates transmission assignments within the body budget, then separately
chooses the permitted direct edges. An independent
[C++ enumerator](enumerate_branching_loaded_skeletons.cpp) recursively
assigns every pair one of the seven symbols. They agree on **every**
canonical code, not merely their counts:

| Loaded vertices k | Labeled records | Canonical cases | Angular exclusions | Bridge exclusions | Union excluded | Remaining |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 175 | 35 | 3 | 6 | 9 | 26 |
| 4 | 8,983 | 1,234 | 180 | 482 | 622 | 612 |
| 5 | 101,016 | 10,305 | 1,180 | 6,971 | 7,465 | 2,840 |
| 6 | 264,181 | 22,407 | 1,654 | 18,767 | 19,156 | 3,251 |
| 7 | 161,294 | 11,685 | 570 | 10,602 | 10,697 | 988 |
| Total | 535,649 | 45,666 | 3,587 | 36,828 | 37,949 | 7,717 |

The raw catalog is fixed; exclusions never delete its rows. Its compact
files contain one digit string per line:

- [k=3](branching_loaded_skeletons_k3.txt)
- [k=4](branching_loaded_skeletons_k4.txt)
- [k=5](branching_loaded_skeletons_k5.txt)
- [k=6](branching_loaded_skeletons_k6.txt)
- [k=7](branching_loaded_skeletons_k7.txt)

Read digits in lexicographic unordered-pair order:
`(0,1),(0,2),...,(0,k-1),(1,2),...,(k-2,k-1)`.
The stable ID `C05-B0-K06-01234` means line 1234 of the k=6 catalog.
The body's count is recovered as k plus the digit costs. Hashes, body-count
breakdowns, and the schema are in
[branching_loaded_skeleton_inventory.json](branching_loaded_skeleton_inventory.json).

## 3. Exact angular inequalities, without optimizing any packing

Give the actual loaded-center rays increasing real lifts
`theta_0<...<theta_(k-1)<theta_0+360`, measured in degrees. Pairwise
geometric bounds give:

| Relation | Strict angular bound |
| --- | --- |
| Every consecutive radial gap | Greater than 36 |
| Direct contact gap | Less than 72 |
| Either arc between S or double-S endpoints | Greater than 72 |
| Either arc between D endpoints | Greater than 90 |
| Either arc between SS or double-SS endpoints | Greater than 144 |

These are exact rational multiples of pi, not decimal approximations.
The loaded-center and touching bounds are in
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md).
The path bounds follow from the local pairwise argument in Section 2 of
[SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md):
center distances are at least 2, `1+sqrt(2)`, and 3, respectively.
That argument does not require the surrounding whole component to be a
simple cycle. Since a minor angle exceeds the bound, both circular arcs
exceed it.

For a direct radial-neighbor pair, its actual gap is the minor gap: the
complementary arc contains at least two other gaps, each greater than
36, so cannot be the direct pair's minor angle below 72.

Every bound becomes `theta_v-theta_u < b` with integer b. The deterministic
constraint ordering used by the certificate is:

1. `(i+1,i,-36)` for `i=0,...,k-2`, followed by `(0,k-1,324)`;
2. scan unordered pairs in digit order;
3. digit 1 adds `(i,j,72)` for `j=i+1`, or `(j,i,-288)` for the wrap pair;
4. each transmission adds `(j,i,-a)` and `(i,j,360-a)`, where a is 72,
   90, or 144 as above.

A triple `(u,v,b)` denotes that strict difference inequality.

## 4. The printed angular certificate is a sum of inequalities

The [angular certificate](branching_loaded_angle_rejections.tsv) assigns
3,587 stable IDs a list of zero-based indices in that case's constraint
list. Every list describes a simple directed cycle of length at most k.
Its integer bounds sum to a number at most zero. Adding its strict
inequalities gives

```text
0 = sum(theta_v-theta_u) < sum(b) <= 0,
```

an immediate contradiction. This is the complete mathematical rejection
rule. For example, bounds `[-144,72,72]` sum to zero: an SS endpoint pair
cannot simultaneously be connected by a two-edge direct-contact path.

There are 60 distinct multisets of witness bounds, all printed with their
integer sums and multiplicities in
[branching_loaded_angle_patterns.json](branching_loaded_angle_patterns.json).
The [checker](check_branching_loaded_angles.py) reconstructs every required
inequality from its catalog code, checks index membership and directed
cycle closure, and adds the original integer bounds. It does not trust
an optimization solver or a floating-point estimate.

For provenance only, witnesses were discovered by a strict difference-
constraint search: replace b with `(k+1)b-1` and find negative cycles.
The replacement is exact because a simple directed cycle has at most k
edges: its scaled sum is negative exactly when its integer original sum
is at most zero. The stored witnesses, not the search algorithm, are
what the checker verifies. Passing the angular test does not assert a
realizable packing or a physical stress.

## 5. Bridge cuts are checked by their graph structure

The [loaded bridge theorem](BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md) excludes
direct, S, and D bridges with loaded endpoints. For each catalog code, the
checker removes a candidate digit 1, 2, or 4 and constructs the component
of one endpoint. A rejection records a proper cut whose only crossing
skeleton edge is that single path. This is directly auditable from the
digit string; a selected case's cut is printed by the decoder.

There are 36,828 codes with at least one such bridge, including 2,466
already rejected by angular cycles. The two predicates therefore reject
`36,828+3,587-2,466=37,949` distinct codes. The remaining 7,717 still include
possible geometric impossibilities and require further proof. The bridge
theorem explicitly retains its selected-certificate and imported n=8
radius dependencies.

## 6. Reproduction and next steps

```sh
python3 research/ten/check_branching_loaded_skeletons.py --verify
python3 research/ten/check_branching_loaded_angles.py
python3 research/ten/check_branching_loaded_angles.py --case C05-B0-K03-00001
c++ -O2 -std=c++17 research/ten/enumerate_branching_loaded_skeletons.cpp -o /tmp/enumerate_b0
mkdir -p /tmp/b0-independent
/tmp/enumerate_b0 /tmp/b0-independent
```

The independent program prints counts and writes `(body_count,code)` rows;
sorting its codes lexicographically reproduces each compact catalog.
This is coverage validation, not Lean verification.

The counts in Sections 4--5 describe the original two-filter batch.
The current [combined graph certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md)
exclude 42,532 of these same 45,666 fixed records, leaving 3,134.
Pursue geometric exclusions of those remaining b=0 records, and
classify the b>0 skeletons separately. None of
these counts should be substituted for the main C05 family's status.
