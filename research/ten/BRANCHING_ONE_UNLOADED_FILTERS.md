# Exact progress in the one-unloaded-branch catalog

**Status:** independently reviewed finite proof ledger and decoder, with
all counts reproduced independently (2026-10-29). Of the fixed 524,870
C05 `b=1` records, **385,071 are excluded** and **139,799 remain**.
This includes the complete two-loaded stratum. C05 as a whole and the
subclasses with at least two unloaded retained vertices remain open.

The raw catalog, code-based stable IDs, and generation hashes are fixed
in [BRANCHING_ONE_UNLOADED_INVENTORY.md](BRANCHING_ONE_UNLOADED_INVENTORY.md).
Use the jointly selected generic planar physical stress before applying
that classification. All predicates below concern this one certificate.

## 1. The five proof predicates

The following previously reviewed results apply with their stated scope.

| Predicate | Finite witness | Mathematical source |
| --- | --- | --- |
| k=2 | The loaded count and the one unloaded retained vertex | [Complete k=2,b=1 exclusion](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md) |
| Loaded bridge | A proper cut with one crossing edge of type direct, S, or D, whose two endpoints are loaded | [Loaded bridge theorem](BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md) |
| SS bridge with double bundle | A proper cut with one SS edge, both endpoints loaded, and an incident double-S or double-SS bundle | [SS-bridge endpoint theorem](BRANCHING_SS_BRIDGE_ENDPOINTS.md) |
| D graph | Three D edges at one retained vertex, or a simple D cycle | [Diagonal path graph theorem](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md) |
| Loaded angle | A directed cycle of strict integer angle inequalities with nonpositive total bound | The local bounds and deduction below |

The bridge predicates deliberately require **both bridge endpoints to be
loaded**. They are not applied to a bridge incident to the unloaded
retained body H. An offending double bundle may, however, have H as its
other endpoint: the SS-bridge theorem permits that. The D-graph theorem
applies to all retained bodies, including H.

The loaded-bridge proof retains its explicitly imported stronger n=8
lower-radius window. This ledger uses the same window and does not claim
to derive that imported bracket independently.

## 2. Loaded-only angular inequalities remain valid

Ignore H when giving increasing angular lifts
`theta_0<...<theta_(k-1)<theta_0+360` to the loaded center rays. The local
loaded geometry gives every consecutive gap greater than 36 degrees and
every direct contact gap less than 72 degrees. The latter is the actual
neighbor gap: its complementary arc contains at least two other loaded
gaps when k>=3; k=2 direct loaded edges are absent by the raw rule.

For a nonempty skeleton path with two loaded endpoints, the cap-angle
theorem gives both endpoint arcs greater than 90 degrees for S, 108 for
D, and 162 for SS. It applies to arbitrary retained endpoint degrees.
Parallel bundles use the same endpoint separation. These statements are
the exact local inequalities proved in
[BRANCHING_LOADED_CAP_ANGLES.md](BRANCHING_LOADED_CAP_ANGLES.md).

Neither the order of a whole mixed cycle nor a radial position of H is
assumed. Edges incident to H supply no angular inequalities in this
ledger. The loaded-loaded relations alone may already contradict one
another.

Translate them into strict inequalities `theta_v-theta_u<b` with integer
b, using exactly the earlier cap-certificate ordering. If a directed
cycle of such inequalities has total bound at most zero, their sum is
`0<sum(b)<=0`, a contradiction. The decoder checks the actual inequality
membership, directed closure, distinct cycle vertices, and integer sum
of every angular witness it emits. Its integer negative-cycle search is
only a way to find those directly checkable witnesses.

## 3. A compact ledger and an on-demand proof decoder

The [classifier and checker](check_branching_one_unloaded_filters.py)
computes the status from the canonical code itself. It prints a proper
cut, incident D edges, D-cycle vertices, or the strict angular cycle
when such a witness is used. For the complete k=2 stratum it links the
hand capacity theorem. An `open` result means only that these predicates
do not exclude the record.

Thus there is no need to commit another half-million-row status file.
The compact [progress summary](branching_one_unloaded_progress.json)
records all counts, the evidence files, and the deterministic first
witness convention. Its disjoint first-witness totals are bookkeeping;
a record may satisfy several proof predicates.

| Loaded k | Raw records | Hand excluded | Remaining |
| --- | ---: | ---: | ---: |
| 2 | 6 | 6 | 0 |
| 3 | 2,331 | 266 | 2,065 |
| 4 | 35,124 | 15,024 | 20,100 |
| 5 | 139,992 | 92,042 | 47,950 |
| 6 | 212,853 | 163,597 | 49,256 |
| 7 | 134,564 | 114,136 | 20,428 |
| Total | 524,870 | 385,071 | 139,799 |

The published
[independent checker](independent_branching_one_unloaded_filters.py)
enumerates all proper cut masks, uses
union-find for the D graph, and reconstructs the angular system with
all-pairs integer closure in 18-degree units. Without importing the
classifier, it reproduced every baseline retained code and the 385,065
baseline exclusions. The complete k=2 theorem adds its six raw records,
giving the table above.

## 4. Reproduction

Generate the raw files in a scratch directory with the inventory's C++
command, then reconstruct the compact ledger:

```sh
python3 research/ten/check_branching_one_unloaded_filters.py --catalog-dir /tmp/ten-b1
python3 research/ten/independent_branching_one_unloaded_filters.py --catalog-dir /tmp/ten-b1 --compare-decoder
```

The script first checks the raw-file hashes against the fixed manifest.
A single case can be inspected without those files:

```sh
python3 research/ten/check_branching_one_unloaded_filters.py --case C05-B1-K02-013
```

Export the exact remaining-case list without adding its rows to the repository:

```sh
python3 research/ten/check_branching_one_unloaded_filters.py --catalog-dir /tmp/ten-b1 --open-cases /tmp/ten-b1-open.txt
```

The output contains one code-based stable ID per line, in loaded-count
and canonical-code order. Each ID can be passed back to `--case` or to
the raw inventory decoder to inspect the remaining configuration.

These counts describe a finite necessary-condition catalog. They do not
assert realizability of the retained records, count proof effort, close
C05, or constitute Lean verification.
