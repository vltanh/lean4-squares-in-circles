# A bridge between retained loaded endpoints must be a two-side path

**Status:** independently reviewed exact hand argument (2026-10-29), with
the [audit record](BRANCHING_LOADED_SKELETON_AUDIT.md). This supplies
additional necessary restrictions for the b=0 skeleton catalog. It does
not exclude every branching component.

Use the selected physical stress of a hypothetical strictly subcritical
ten-square packing. Work in

```text
5/2+sqrt(2)<R^2<9/2.
```

The lower window and its pinned n=8 arithmetic dependency are explicitly
justified in Section 1 of
[MIXED_FIVE_FOUR_LOADED.md](MIXED_FIVE_FOUR_LOADED.md). The stronger lower
bound is needed only for the diagonal-path exclusion below. Direct and
single-side exclusions already hold for `R>=79/40`.

Suppress only unloaded vertices of whole-graph degree two, as in
[BRANCHING_COMPONENT_SKELETON_DRAFT.md](BRANCHING_COMPONENT_SKELETON_DRAFT.md).
Suppose a skeleton bridge has two **loaded** retained endpoints. A bridge
cannot have parallel copies. Its type is therefore direct, S, D, or SS.

**Theorem.** Its type must be SS. In particular the other three types
cannot occur as graph bridges in the b=0 subclass, where every retained
vertex is loaded.

## 1. Direct bridges are excluded by the reviewed bridge cover

A direct skeleton bridge is also a bridge in the original positive graph.
Section 2 of [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md)
proves that every positive bridge has a geometrically circle-clear
endpoint. A loaded body cannot be circle-clear. Thus a direct bridge
cannot join two loaded endpoints.

## 2. A nonempty bridge path lies on one radial line

Let the nonempty path have width `W in {1,sqrt(2),2}`. Every original edge
on that path is a bridge: deleting any of them separates the same two
retained sides, because the skeleton edge is a bridge and internal path
bodies have degree two.

Each bridge force line passes through zero by the sum of origin torques
over either cut component. Transmission equations keep every contact on
this same line, and the two loaded-endpoint contact points differ by
`W d`, with d a unit vector pointing along the path.

Every point x of a loaded square satisfies

```text
|x|>=R-sqrt(2)>0,                                    (1)
```

by comparing x with any circle vertex in that unit square. Thus neither
endpoint contact is zero.

The two endpoint contacts must lie on **opposite** rays of the radial
line. If both were on its positive ray, let their radial coordinates be
`t,t+W`, with `t>=R-sqrt(2)`. The outer endpoint square is supported
beyond the line at coordinate `t+W`, so its directional width of at least
one would give a point with projection at least

```text
t+W+1 >= R-sqrt(2)+2 > R,
```

contrary to disk containment. Both-negative contacts are excluded by
reflection. We may therefore denote their positive radii by r,s, with

```text
W=r+s,       r,s>=R-sqrt(2).                          (2)
```

For a single side transmitter, `W=1`. But the reviewed bounds
`R>=79/40` and `sqrt(2)<57/40` give

```text
r+s>=2(R-sqrt(2))>11/10>1,
```

contradicting (2). This excludes an S bridge.

## 3. A diagonal bridge would force two overly distant side supports

For D, the internal square's two contacts are opposite vertices, and
its force direction is diagonal, strictly inside their normal cones.
Each loaded endpoint contact is off zero by (1).

The selected-certificate convention excludes an off-origin point-only
vertex/vertex bridge: its chosen normal is nonradial, while every bridge
force line is radial. This is the explicitly pinned convention in
Section 1 of [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md).
Furthermore, a diagonal transmitter's exposed support is a singleton
vertex, so the pair intersection cannot be a positive-length segment.
Consequently each loaded endpoint contact lies in a relative side
interior of that endpoint square.

Put one radial support point at `(r,0)`, with its endpoint square lying
beyond the line `x=r`. Its side frame is fixed by this normal, so it has
the form

```text
[r,r+1] x [y-1/2,y+1/2],       |y|<1/2.
```

Since `r>0`, its farthest vertices lie on the outer side `x=r+1`.
The body is loaded and contained in the radius-R disk, so

```text
R^2=(r+1)^2+(|y|+1/2)^2 < (r+1)^2+1.
```

In particular

```text
r>sqrt(R^2-1)-1>1/sqrt(2),                            (3)
```

where the final strict inequality is equivalent to
`R^2>5/2+sqrt(2)`. The other endpoint obeys the same bound by reflection.
Equations (2)--(3) would give `W=r+s>sqrt(2)`, contradicting the D width.

Only the width-two SS bridge remains. This proof does not assert its
existence or sufficient completion capacity. It also does not apply to
edges having an unloaded retained endpoint; those belong to the still
unclassified b>0 part of C05.
