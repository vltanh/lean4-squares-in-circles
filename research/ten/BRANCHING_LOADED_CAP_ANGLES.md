# Stronger transmission angles in the fixed branching catalog

**Status:** independently reviewed exact consequence of the cap-angle
theorem and its finite integer certificate (2026-10-29).
The raw C05 `b=0` catalog remains fixed at 45,666 records. The new angular
certificate, together with the reviewed bridge exclusions, excludes
40,306 records and leaves 5,360. C05 and its `b>0` subclass remain open.

## 1. The stronger inequalities apply at branching endpoints

The [cap-angle theorem](TRANSMISSION_CAP_ANGLE_BOUND.md) requires only two
unit squares in the containing disk with a separating strip of width W.
It does not impose a degree condition, require a whole simple cycle, or
require those two squares to be loaded. The transmission-distance lemma
supplies that strip to each nonempty skeleton path in the
[fixed catalog](BRANCHING_LOADED_SKELETON_INVENTORY.md).

In the strictly subcritical case its exact conclusions are:

| Path symbol | Width | Both endpoint arcs exceed |
| --- | --- | --- |
| S or double-S | 1 | 90 degrees |
| D | sqrt(2) | 108 degrees |
| SS or double-SS | 2 | 162 degrees |

Every arc exceeds the minor-angle lower bound. The double symbols have
the same endpoint strip as either of their paths. Ordinary consecutive
loaded gaps still exceed 36 degrees, and direct contact gaps remain less
than 72 degrees, with precisely the scope proved in the earlier catalog.

Give the loaded-center rays increasing lifts
`theta_0<...<theta_(k-1)<theta_0+360`. Each inequality has the form
`theta_v-theta_u < b`, with b an integer. Keep the original deterministic
constraint order: k ordinary-gap constraints first, then unordered pairs
in lexicographic order. Direct constraints are unchanged. A transmission
pair `i<j` now contributes

```text
(j,i,-a), (i,j,360-a),
a=90 for S/double-S, 108 for D, 162 for SS/double-SS.
```

## 2. The certificate is a list of immediate integer contradictions

For every rejected stable ID,
[branching_loaded_cap_angle_rejections.tsv](branching_loaded_cap_angle_rejections.tsv)
prints zero-based indices in that case's new constraint list. The indices
form a directed simple cycle, and their integer bounds sum to at most
zero. Adding its inequalities gives `0<sum(bounds)<=0`. No geometric
optimization result is used.

For example, `C05-B0-K03-00010` has code `056`, meaning an SS path from
0 to 2 and a double-SS path from 1 to 2. Its witness is

```text
theta_0-theta_1 < -36,
theta_2-theta_0 < 198,
theta_1-theta_2 < -162.
```

The bounds sum to zero, so this case is impossible. The same reasoning
checks each stored cycle, whose length is at most seven. There are
14,264 angular witnesses and 116 distinct multisets of integer bounds.
All 3,587 earlier angular exclusions are included.

The [checker](check_branching_cap_angles.py) reconstructs the inequalities
directly from each digit string, checks witness membership, simplicity,
directed closure, and the integer sum. It does not import the search
routine. It also checks all printed counts and verifies the inclusion
of the previous angular exclusions.

The [builder](build_branching_cap_angles.py) discovers witnesses using
strict difference constraints scaled to integer weights `(k+1)b-1`.
On a simple cycle of length at most k, its scaled sum is negative exactly
when the original integer sum is nonpositive. The checked stored cycles
are the exclusion evidence; the discovery method need not be trusted.
Two independent all-pairs integer closures also reproduced exactly the
same 14,264 rejected IDs. The separate mathematical auditor reconstructed
the inequalities in 18-degree units without importing either script and
independently recomputed every bridge cut; all ID sets and counts matched.

## 3. Progress within this fixed subclass

Combine the stronger angular list with the unchanged
[loaded bridge theorem](BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md).
The exact counts in
[branching_loaded_cap_angle_summary.json](branching_loaded_cap_angle_summary.json)
are:

| Loaded k | Raw records | Angular exclusions | Bridge exclusions | Union excluded | Remaining |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 35 | 9 | 6 | 15 | 20 |
| 4 | 1,234 | 489 | 482 | 840 | 394 |
| 5 | 10,305 | 4,267 | 6,971 | 8,519 | 1,786 |
| 6 | 22,407 | 6,909 | 18,767 | 20,006 | 2,401 |
| 7 | 11,685 | 2,590 | 10,602 | 10,926 | 759 |
| Total | 45,666 | 14,264 | 36,828 | 40,306 | 5,360 |

The angle and bridge lists intersect in 10,786 records. Thus their union
contains `14,264+36,828-10,786=40,306` records. Relative to the earlier
37,949-record union this supplies **2,357 further exclusions**.

These counts measure a finite necessary-condition catalog, not geometric
feasibility or proof effort. Passing either filter does not construct a
packing or stress. The raw catalog, its stable IDs, the earlier exclusion
certificate, and its historical counts are unchanged. Unloaded retained
branching vertices (`b>0`) remain outside both ledgers.

## 4. Reproduction

```sh
python3 research/ten/build_branching_cap_angles.py --check
python3 research/ten/check_branching_cap_angles.py
python3 research/ten/check_branching_cap_angles.py --case C05-B0-K03-00010
```

The raw catalog has separate independent Python/C++ coverage checks in
the [audit record](BRANCHING_LOADED_SKELETON_AUDIT.md). None of these
computations is Lean verification.
