# SS-bridge endpoint exclusions in the fixed branching catalog

**Status:** independently reviewed exact finite consequence of the
[SS-bridge endpoint theorem](BRANCHING_SS_BRIDGE_ENDPOINTS.md), including
all printed certificates and counts (2026-10-29). It contributes 30 new
exclusions in the fixed C05 `b=0` catalog, taking the union to 40,336 of
45,666 records, with 5,330 remaining. C05 as a whole remains open.

## 1. The graph predicate and its geometric premise

The endpoint theorem proves that either loaded endpoint of a single SS
graph bridge cannot also have a double-S or double-SS bundle to another
retained vertex. Its proof treats every endpoint contact, including
support-side endpoints, and all horizontal and vertical bundle directions.
It uses the selected-certificate strict-normal convention to obtain
positive side overlap, as the earlier bundle multiplicity theorem does.

In the seven-symbol catalog this has a precise finite form:

1. A digit-5 edge is the only edge across a proper vertex cut.
2. At least one endpoint of that edge belongs to a digit-3 or digit-6 edge.

The digit-5 edge is a single SS path, so the first condition makes it a
skeleton bridge. Digits 3 and 6 are respectively two parallel S paths
and two parallel SS paths. Every retained vertex is loaded in this
catalog, so the geometric theorem applies to the shared endpoint.

For example, `C05-B0-K03-00007` has code `035` in pair order
`(0,1),(0,2),(1,2)`. The SS edge `(1,2)` is the sole edge across the cut
`{1}`, while vertex 2 also belongs to the double-S bundle `(0,2)`.
The endpoint theorem excludes this record.

## 2. Explicit cut witnesses

[branching_ss_bridge_rejections.tsv](branching_ss_bridge_rejections.tsv)
contains four tab-separated fields per row:

```text
stable_case_ID   bridge_edge_index   bundle_edge_index   cut_bitmask
```

Edge indices are zero-based in the catalog's lexicographic unordered-pair
order. Vertex i belongs to the cut exactly when bit i of the mask is one.
The [checker](check_branching_ss_bridges.py) verifies the digit types,
shared endpoint, properness of the cut, and that the selected SS edge is
the unique present edge crossing it. Those checks are the complete graph
certificate; no geometric search or floating-point estimate is involved.

There are 354 certified records. The [builder](build_branching_ss_bridges.py)
finds them by deleting each candidate SS edge and constructing a connected
component. The checker separately reconstructs the full rejected-ID set
by depth-first bridge search; it does not import the builder. Representing
an unrelated parallel bundle by one adjacency does not alter whether a
single SS edge is a bridge. Every ID agrees between the two methods.
A separate auditor enumerated every proper cut mask without importing
either implementation and again obtained precisely the same 354 IDs,
30 new exclusions, and combined totals.

## 3. Exact progress counts

The immediately preceding ledger combined the
[cap-angle certificate](BRANCHING_LOADED_CAP_ANGLES.md) with the original
[loaded bridge exclusions](BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md), proving
40,306 records impossible. Of the 354 new cut witnesses, 324 were already
in that union. Thus this theorem supplies 30 further exclusions.

| Loaded k | SS-bridge witnesses | Newly excluded | Total union excluded | Remaining |
| --- | ---: | ---: | ---: | ---: |
| 3 | 2 | 1 | 16 | 19 |
| 4 | 59 | 13 | 853 | 381 |
| 5 | 222 | 15 | 8,534 | 1,771 |
| 6 | 71 | 1 | 20,007 | 2,400 |
| 7 | 0 | 0 | 10,926 | 759 |
| Total | 354 | 30 | 40,336 | 5,330 |

The exact totals and all 30 newly excluded stable IDs are printed in
[branching_ss_bridge_summary.json](branching_ss_bridge_summary.json).
The fixed raw catalog and earlier certificates are unchanged. These
counts do not enumerate the `b>0` subclass, prove feasibility of any
retained code, or give a percentage of the unrestricted proof.

## 4. Reproduction

```sh
python3 research/ten/build_branching_ss_bridges.py --check
python3 research/ten/check_branching_ss_bridges.py
python3 research/ten/check_branching_ss_bridges.py --case C05-B0-K03-00007
```

The prior certificates have their own exact checkers, and the fixed raw
catalog has independent Python/C++ coverage checks. No Lean verification
is claimed.
