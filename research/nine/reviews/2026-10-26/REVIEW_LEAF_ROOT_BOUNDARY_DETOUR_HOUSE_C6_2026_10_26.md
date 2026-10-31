# Independent scope review: two complete rooted-house load orbits

Date: October 26, 2026.

Reviewed source: `LEAF_ROOT_BOUNDARY_DETOUR_HOUSE_LOAD_EXCLUSIONS.md`.
Direct prerequisites checked: Theorem 4.1 and Lemma 2.1 of
`FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`, and the actual graph/load
cover in `FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md`.

**Verdict: accepted.** The source excludes the complete house-hub
load orbit `TDC` and house-lower load orbit `TA`, for each full
genuine S/D leaf alternative. All four listed labels are original
existing open gates in `DEEP_GATED_ROADMAP.md`; none is a newly
invented subdivision.

## 1. Exact inherited scope

Theorem 4.1 is a geometric implication about a square meeting the
central epsilon disk, an actual positive-reserve normal channel, and
a circle-touching common neighbor of its two endpoints. Its proof
imposes no degree or force-balance condition at either channel
endpoint or at the detour square. The far endpoint need not have a
positive circle load or even touch the circle. Each detour contact
may have zero stress, although the two applications here use original
positive edges.

The channel comes only from the unchanged true unloaded degree-two
internal square. Both its original forces and torque equation remain,
and they give the actual reserve `1` or `sqrt(2)` with its
original application means. A higher-degree root or far endpoint is
never treated as a transmitter.

Lemma 2.1 uses the genuine leaf edge alone. Its D domain contains the
origin, and its complete S domain includes the aligned interval and
both reflected tilted families. It therefore supplies the central-disk
premise for an arbitrary genuine leaf root, regardless of that root's
other positive degree or forces. The full radius interval gives the
same `epsilon=max(d-1,0)<1/60` used by the detour theorem.

## 2. House hub A, positive block loads TDC

The exact house edges are `AT,DT,AD,AB,BC,CD`, with additional
genuine leaf edge `AL`. Thus the original root A has degree four.
Since the block load set is exactly `T,D,C`, B is an unloaded
degree-two square with actual positive neighbors A,C. Its unchanged
equations give the channel `A--B--C`. Loaded D physically touches
both endpoints through the actual edges `AD` and `DC`.

The inherited theorem therefore applies with `(P,U,Q,Z)=(A,B,C,D)`.
Neither A's leaf force nor its roof force is deleted. T retains its
loaded degree-two equations. All physical masks and individual corner
weight endpoints at T,D,C are covered, because the detour theorem
needs only actual circle contact at D.

## 3. House lower B, positive block loads TA

The same block now has the additional genuine leaf edge `BL`, so
B has true degree three. The exact block load set `T,A` makes C
unloaded with its original two positive neighbors B,D. Thus the
actual channel is `B--C--D`. Loaded A touches both endpoints via
`BA` and `AD`.

The theorem applies with `(P,U,Q,Z)=(B,C,D,A)`. The far endpoint
D remains the original unloaded degree-three square with all of
`DT,DA,DC` present; it is not assigned a degree-two equation. Its
zero circle load does not violate any premise of the inherited
theorem. T and the genuine leaf also remain unchanged.

## 4. Original labels and exhaustive leaf joins

The following exact four labels were checked against their existing
roadmap entries and against the load words in the graph-cover source:

| Original gate | Actual complete domain excluded |
| --- | --- |
| `M6.B5L.HOUSE.HUB.LTDC.S` | Hub A, block loads TDC, full genuine S leaf |
| `M6.B5L.HOUSE.HUB.LTDC.D` | Hub A, block loads TDC, full genuine D leaf |
| `M6.B5L.HOUSE.LOWER.LTA.S` | Lower B, block loads TA, full genuine S leaf |
| `M6.B5L.HOUSE.LOWER.LTA.D` | Lower B, block loads TA, full genuine D leaf |

The previously excluded hub `TD` and lower `TC` load words are
different original orbits and are not counted again. Hub `TDCB`
has B loaded, so it does not meet this proof's channel premise and
is correctly not claimed. Each original reflected root placement is
transported with its entire graph, means, forces and masks; no extra
gate is created for that existing symmetry.

These contradictions already exclude the six physical core squares.
All three extra squares remain arbitrary members of the original
nine-square packing; a completion-capacity premise is unnecessary.
Other load orbits of the two rooted house types remain separate,
and neither an entire rooted type nor a coarse parent is closed by
this source alone. No new certificate, force deletion, selected mean,
normal change, Lean compilation or CI action occurs.
