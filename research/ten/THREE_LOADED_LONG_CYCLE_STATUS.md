# Three-loaded larger cycles: ten signatures closed, three remain

This is a focused index of the unchanged C20 inventory, not a new
partition or an additional contribution to the main progress count.
There are exactly 13 graph/transmitter signatures with three loaded
bodies and whole-cycle length at least six. Their current progress is

`██████████░░░` **10/13 closed by hand; 3 open.**

The physical certificate is selected before classification using
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md).
The generic D-side-interior restrictions used by the newest exclusions
concern that selected certificate, not an arbitrary previously chosen
stress with a fixed positive graph.

| Stable ID | Canonical word | Current proof status |
| --- | --- | --- |
| C20-M06-L03-B01-T01 | `LLSLSS` | [HAND CLOSED](SS_SIDE_SIX_CYCLE_EXCLUSION.md) |
| C20-M06-L03-B01-T02 | `LLDLSS` | [HAND CLOSED](SS_DIAGONAL_SIX_CYCLE_EXCLUSION.md) |
| C20-M06-L03-B02-T01 | `LSLSLS` | OPEN |
| C20-M06-L03-B02-T02 | `LSLSLD` | OPEN |
| C20-M06-L03-B02-T03 | `LSLDLD` | [HAND CLOSED](TWO_DIAGONAL_ONE_SIDE_SIX_CYCLE_EXCLUSION.md) |
| C20-M06-L03-B02-T04 | `LDLDLD` | [HAND CLOSED](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md) |
| C20-M07-L03-B01-T01 | `LLSSLSS` | [HAND CLOSED](SHARP_TRANSMISSION_CYCLE_BUDGET.md) |
| C20-M07-L03-B02-T01 | `LSLSLSS` | OPEN |
| C20-M07-L03-B02-T02 | `LSLDLSS` | [HAND CLOSED](SHARP_TRANSMISSION_CYCLE_BUDGET.md) |
| C20-M07-L03-B02-T03 | `LDLDLSS` | [HAND CLOSED](SHARP_TRANSMISSION_CYCLE_BUDGET.md) |
| C20-M08-L03-B01-T01 | `LSLSSLSS` | [HAND CLOSED](THREE_LOADED_LONG_CYCLES.md) |
| C20-M08-L03-B01-T02 | `LDLSSLSS` | [HAND CLOSED](THREE_LOADED_LONG_CYCLES.md) |
| C20-M09-L03-B01-T01 | `LSSLSSLSS` | [HAND CLOSED](THREE_LOADED_LONG_CYCLES.md) |

## The three exact remaining patterns

| Word | Three loaded-to-loaded path widths | Remaining issue |
| --- | --- | --- |
| `LSLSLS` | `1,1,1` | Three S transmitters; no D frame propagation applies. Local support ownership and completion capacity remain open. |
| `LSLSLD` | `1,1,sqrt(2)` | The D endpoints have parallel frames and relative side-interior D contacts. A numerical six-body stress candidate survives those constraints; a capacity proof must retain the additional squares or further global restrictions. |
| `LSLSLSS` | `1,1,2` | One SS path and two S paths; the other two loaded bodies do not directly touch, so the reviewed SS/direct-edge six-cycle exclusions cannot simply be reused. |

The [numerical LSLSLD candidate](ONE_DIAGONAL_TWO_SIDE_COMPONENT_CANDIDATE.md)
is not an exact existence certificate or a ten-square packing. The
[conditional six-center cover](SIX_BODY_CENTER_COVER.md) gives a rational
completion obstruction for a whole specified neighborhood of that core,
with arbitrary square orientations; its hypotheses have not been derived
for every realization of LSLSLD.

All remaining entries retain continuous positions, orientations, support
ownership, and positive stress variables. Their presence in this finite
inventory is not a claim of geometric feasibility. The main status source
remains [cycle_progress.json](cycle_progress.json), and the complete 279-case
inventory is [CYCLE_CASES.md](CYCLE_CASES.md).
