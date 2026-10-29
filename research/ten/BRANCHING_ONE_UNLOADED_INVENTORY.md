# Finite branching catalog with one unloaded retained vertex

**Status:** independently reviewed necessary-condition enumeration for the
C05 `b=1` subclass (2026-10-29), with every record independently reproduced
in C++ and Python. There are **524,870 fixed canonical records**.
This is a finite covering catalog, not a geometric feasibility claim or
an exclusion of C05. Subclasses with `b>=2` are outside this inventory.

## 1. The selected graph and its labels

Choose the jointly compatible physical stress of
[PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md)
before classifying its positive components. Suppress only unloaded bodies
of degree two in the whole positive graph, as in the reviewed
[skeleton reductions](BRANCHING_COMPONENT_SKELETON_DRAFT.md).

In the present subclass there are k loaded retained vertices, `2<=k<=7`,
and exactly one unloaded retained vertex H. Label the loaded vertices
`0,...,k-1` in their radial circular order, and label H by k. The skeleton
has a planar disk embedding with the loaded vertices on its boundary in
this order and H in its interior. The graph is connected, cyclic, and
branching; its internal path bodies and all unstressed squares still
count toward the total of ten physical squares.

For each unordered pair use the seven-symbol alphabet:

| Digit | Relation | Internal-body cost | Number of multiedges |
| --- | --- | ---: | ---: |
| 0 | Absent | 0 | 0 |
| 1 | Direct | 0 | 1 |
| 2 | S | 1 | 1 |
| 3 | Double-S | 2 | 2 |
| 4 | D | 1 | 1 |
| 5 | SS | 2 | 1 |
| 6 | Double-SS | 4 | 2 |

An SS path is serial; a double-S bundle is parallel. Their identical
internal-body costs do not identify them. The earlier width, distance,
bundle, and strict-normal arguments prove that this alphabet covers
every possible pair of retained endpoints.

## 2. The fixed raw predicates

Keep exactly those assignments satisfying all the following conditions.

1. `k+1+sum(internal-body costs)<=10`.
2. The multigraph is connected, has at least `k+1` multiedges, and has
   every degree at most eight. Degrees count parallel copies.
3. H has degree at least three. It has at least three distinct neighbors,
   except that exactly two neighbors are permitted when its two symbols
   are direct and double-S. This is the complete necessary two-neighbor
   restriction from Section 4 of the skeleton reduction.
4. A direct loaded-loaded edge joins circular neighbors. At k=2 no such
   edge is permitted, and at k=3 at most one is permitted: otherwise a
   loaded body touches every other loaded body of the component, contrary
   to the loaded-star semicircle theorem.
5. No two present loaded-loaded edges have alternating endpoints.
6. A present loaded-loaded edge `(i,j)` cannot have a neighbor of H
   strictly in each of the two open boundary arcs between i and j.

Condition 5 follows from the selected planar disk embedding. For
condition 6, the edge `(i,j)` is an arc separating the disk into two
sides. H is not on that arc, so its side is fixed. An edge from H to a
boundary vertex in the opposite open arc would have to cross `(i,j)`.
Neighbors equal to i or j do not give this obstruction and are correctly
excluded from the open-arc test. This argument also works for a parallel
bundle by choosing any one of its arcs. It uses neither the radial
position of H nor a straight-line drawing of skeleton edges.

Only necessity is asserted. The last two tests are not being used as a
sufficiency theorem for stress or packing geometry. Other reviewed
geometric exclusions are deliberately left out of the raw rule so that
later progress can be measured against a stable denominator.

## 3. Quotient, stable IDs, and counts

Quotient only by the `2k` rotations and reflections of the loaded circular
labels, fixing H. Keep the lexicographically smallest digit string in
each orbit. Read its digits in lexicographic unordered-pair order on
`0,...,k`. Arbitrary graph isomorphisms are not used: they could change
the specified circular loaded order.

Stable IDs contain the canonical code itself:

```text
C05-B1-Kkk-code
```

Here kk is the two-digit loaded count, and leading zero digits of the
code are retained. For example `C05-B1-K02-013` has a direct edge from
loaded vertex 0 to H=2, and a double-S bundle from loaded vertex 1 to H.
It has five physical bodies. The six k=2 codes are
`013,213,313,413,513,613`.

| Loaded k | Retained unloaded | Labeled assignments | Canonical records |
| --- | ---: | ---: | ---: |
| 2 | 1 | 12 | 6 |
| 3 | 1 | 13,017 | 2,331 |
| 4 | 1 | 276,529 | 35,124 |
| 5 | 1 | 1,388,401 | 139,992 |
| 6 | 1 | 2,540,653 | 212,853 |
| 7 | 1 | 1,870,758 | 134,564 |
| Total | — | 6,089,370 | 524,870 |

The [compact manifest](branching_one_unloaded_inventory.json) records the
fixed rule version, alphabet, per-body counts, and SHA-256 hashes of the
generated code files. The 11 MB of reproducible raw rows need not be
committed: every case is defined by the fixed predicates, and its ID
already contains its entire combinatorial record.

## 4. Exhaustiveness and independent checks

The [C++ enumerator](enumerate_branching_one_unloaded.cpp) assigns every
possible symbol on H's incident pairs first, then assigns every symbol
on the loaded-loaded pairs. Each early pruning rule is one of the fixed
necessary predicates. Every surviving labeled assignment is therefore
visited, and dihedral canonicalization gives the prescribed quotient.

The independent
[Python enumerator](independent_branching_one_unloaded.py) assigns the
loaded-loaded pairs first and H's pairs last. It reproduced every code
and labeled count in all six strata, not just the final totals. A third
full Cartesian-product enumeration checked k=2 and k=3 independently.

The [validator and decoder](check_branching_one_unloaded.py) separately
checked every generated record against all predicates, its dihedral
canonicality, the sorted unique file order, the manifest hashes, and
the per-body counts. This is exact finite combinatorial verification;
no floating-point optimization or Lean verification is claimed.

## 5. Reproduce or inspect a case

Generate raw files in a scratch directory and verify them:

```sh
c++ -O2 -std=c++17 research/ten/enumerate_branching_one_unloaded.cpp -o /tmp/enumerate_b1
/tmp/enumerate_b1 /tmp/ten-b1
python3 research/ten/check_branching_one_unloaded.py --catalog-dir /tmp/ten-b1
python3 research/ten/independent_branching_one_unloaded.py --catalog-dir /tmp/ten-b1
```

The C++ generation took a few seconds in the research environment; the
full independent Python enumeration took several minutes. A case can be
decoded without generating any catalog file:

```sh
python3 research/ten/check_branching_one_unloaded.py --case C05-B1-K02-013
```

The complete [two-loaded exclusion](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md)
has a separate proof and review boundary. Further filter ledgers should
refer to these code-based IDs and leave the raw manifest unchanged.
Neither the size of this catalog nor a fraction of excluded rows is a
percentage of the unrestricted proof.
