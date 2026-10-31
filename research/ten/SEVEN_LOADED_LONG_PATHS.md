# Seven-loaded cycles: three long-path patterns are impossible

**Status:** exact hand proof, independently reviewed. This excludes three
entries of the fixed mixed-cycle inventory. It uses only the angular order
of loaded centers and the location of **direct loaded contacts** in that
order. Transmission paths are not assumed to follow the angular order.

Work in the radius window `79/40<=R<=3/sqrt(2)`. Consider a whole positive
component whose body-pair graph is a simple cycle and which has exactly
seven loaded bodies. The following patterns are impossible:

1. There is just one nonempty unloaded run, consisting of two side
   transmitters.
2. There are exactly two nonempty unloaded runs, one consisting of two
   side transmitters and the other of one side or diagonal transmitter,
   and the two runs share a loaded endpoint.

## 1. Direct loaded contacts form a subgraph of the angular seven-cycle

Sections 1 and 2 of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md) prove two
pairwise statements in the stated radius window:

```text
every pair of loaded center rays has minor separation > pi/5;
every touching pair of loaded center rays has minor separation < 2pi/5.
```

These pairwise statements hold regardless of whether the rest of the
positive component is loaded. They follow from the radial bounds
`5/4<|c|<25/16`, separation of unit-square centers by at least one, and
the circle-loaded contact-angle estimate.

List the seven loaded center rays in their circular angular order and
let H be the abstract seven-cycle joining successive rays. Each angular
gap is greater than `pi/5`; because the other six gaps together exceed
`6pi/5`, each gap is also strictly less than `4pi/5`:

```text
pi/5 < each successive gap < 4pi/5.                (1)
```

If two rays are not consecutive, each of the two arcs between them
contains at least two successive gaps, so both arcs exceed `2pi/5`.
Such a pair cannot correspond to touching loaded squares. Thus every
direct positive edge between two loaded bodies is an edge of H.

On the other hand, a path with two unloaded side transmitters separates
its loaded endpoint centers by at least three. Section 1 of
[FOUR_LOADED_THREE_LONG_PATHS.md](FOUR_LOADED_THREE_LONG_PATHS.md) proves
that such a pair has minor angular separation strictly greater than
`4pi/5`. By (1), its endpoints cannot be adjacent in H.

## 2. A single length-two run

Deleting the sole unloaded run from the given cycle leaves six direct
loaded-loaded edges forming a path on all seven loaded vertices. This
path is a subgraph of H. Any spanning six-edge path in a seven-cycle is
that seven-cycle with one edge removed. Therefore its two endpoints are
adjacent in H.

These are exactly the endpoints of the length-two transmission run.
Their forced adjacency contradicts Section 1, excluding the first
pattern.

## 3. Two runs with a shared loaded endpoint

Let V be the common loaded endpoint of the two nonempty runs. Deleting
both runs leaves V isolated, and the other six loaded bodies form a
five-edge direct-contact path P. All five edges of P belong to H.

Deleting V from H produces a path on the other six vertices, with exactly
five edges. P is a subgraph of that path with the same number of edges,
so they coincide. Consequently both endpoints of P are adjacent to V
in H.

The two transmission runs join V to those two endpoints. In particular,
the length-two run has radially adjacent endpoints, again contradicting
Section 1. This proves the second pattern for either type of its single
transmitter.

This graph argument does not identify the angular order with the original
mixed cycle order. The adjacency of the relevant transmission endpoints
is forced by the number and arrangement of the **direct** contacts, which
were already proved to lie in H.

## 4. Finite-inventory entries

The following three entries of [cycle_cases.json](cycle_cases.json) are
closed by this theorem:

| Stable ID | Canonical word | Pattern |
| --- | --- | --- |
| `C20-M09-L07-B01-T01` | `LLLLLLLSS` | One length-two run |
| `C20-M10-L07-B01-T01` | `LLLLLLSLSS` | Length-two and side runs sharing a loaded endpoint |
| `C20-M10-L07-B01-T02` | `LLLLLLDLSS` | Length-two and diagonal runs sharing a loaded endpoint |

Their status is recorded separately in [cycle_progress.json](cycle_progress.json).
When the two nonempty runs do not share a loaded endpoint, the direct
contacts leave two longer paths; the preceding argument does not force
either transmission pair to be radially adjacent. Those patterns remain
outside this theorem.
