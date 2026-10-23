# Exact construction and a family at the target radius

Set `Q = 9/2`, `R* = √Q = 3/√2`, and
`L = (√17 − 1)/2`. All squares in this note are axis-parallel unit squares;
the containing disk is centred at the origin. Boundary contact is allowed.

For a square with centre `(x,y)`, its farthest squared vertex distance is

`F(x,y) = (|x| + 1/2)² + (|y| + 1/2)²`.

Thus it lies in the disk exactly when `F(x,y) ≤ Q`. Two such squares have
disjoint interiors exactly when `|x−x'| ≥ 1` or `|y−y'| ≥ 1`.

## The rational witness

Take these ten centres:

| Group | Centres |
| --- | --- |
| Left | `(-1,-1), (-1,0), (-1,1)` |
| Centre | `(0,-3/2), (0,-1/2), (0,1/2), (0,3/2)` |
| Right | `(1,-1), (1,0), (1,1)` |

Within each column consecutive heights differ by one. Between columns the
x-coordinates differ by at least one. Hence every pair has disjoint interiors.
The four centres `(±1,±1)` have `F = 9/2`; the two side middles have `F = 5/2`;
the two central endpoints have `F = 17/4`; and the two central middles have
`F = 5/4`. These exhaust the ten squares and prove containment.

The four vertices `(±3/2,±3/2)` lie on the circle. Consequently this fixed
configuration cannot be contained in a smaller disk even after choosing a new
disk centre: opposite vertices are distance `3√2 = 2R*` apart. This establishes
attainment of the upper bound, not that every ten-square configuration needs it.

## Six-parameter family

Keep four anchor centres `(±1,±1)`. Choose real parameters

`1 ≤ u ≤ L`, `1 ≤ v ≤ L`,

`−L ≤ t₀`, `t₀+1 ≤ t₁`, `t₁+1 ≤ t₂`, `t₂+1 ≤ t₃`, `t₃ ≤ L`.

The remaining six centres are

`(-u,0), (v,0), (0,t₀), (0,t₁), (0,t₂), (0,t₃)`.

Every choice gives a packing at radius `R*`:

1. Anchors in the same side column have vertical gap two; anchors on opposite
   sides have horizontal gap two.
2. A side middle is separated from the two anchors on its own side by vertical
   gap one, and from opposite anchors by horizontal gap at least two. The two
   side middles have horizontal gap at least two.
3. Every central square is separated from each anchor and each side middle by
   horizontal gap at least one. The four central squares are separated by
   their ordered height gaps.
4. The anchors satisfy `F = Q`. The side middles and central squares satisfy
   `F ≤ (L+1/2)² + 1/4 = 17/4 + 1/4 = Q`.

The rational witness is `u=v=1` and `t=(-3/2,-1/2,1/2,3/2)`. Since
`2L−3 = √17−4 > 0`, the four heights have positive slack beyond their three
required unit gaps. Together with the two independent side slides, these are
six continuous parameters with a nonempty interior in parameter space.

For example `u=21/20`, `v=11/10`, and the same four rational heights still
pack at `Q`, and their centres have five distinct x-coordinates. This example
falls outside the [three-column theorem](THREE_COLUMN_THEOREM.md).

This is a sufficient family of radius-`R*` packings. It is not a necessary
description of all such packings, nor an assertion of unrestricted optimality.
Any eventual equality theorem must account for at least these degrees of
freedom, up to ambient isometry and relabelling.
