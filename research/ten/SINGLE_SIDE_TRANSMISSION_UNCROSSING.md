# Single side transmitters force radial order when at most one diagonal occurs

**Status:** independently reviewed exact hand proof, including the local
junction argument, radial-order theorem, angular budgets, and all finite-case IDs.

Work with a hypothetical ten-square packing in
`79/40<=R<3/sqrt(2)`, its physical positive stress, and whole components
whose body-pair graph is a mixed simple cycle. There are at most seven
loaded bodies, by the center-radius reduction. This note proves two
structural assertions:

1. Two vertex-disjoint nonempty transmission paths cannot have alternating
   loaded endpoints if at least one path consists of a single side
   transmitter S.
2. If the whole mixed cycle has at most one diagonal transmitter D, its
   successive loaded bodies occur in their radial circular order, up to
   reversal.

The second assertion, combined with exact angular budgets, excludes the
117 cases in [single_side_cycle_batch.json](single_side_cycle_batch.json).
Of these, 27 have already received separate hand exclusions; the new
argument closes 90 further fixed-inventory entries.

## 1. A single S path cannot participate in a transverse junction

Let P be a single-S transmission path and Q another nonempty transmission
path, with disjoint vertex sets. If Q is SS, the independently reviewed
[width-two uncrossing theorem](TRANSMISSION_PATH_UNCROSSING.md) already
excludes alternating loaded endpoints. Otherwise Q is a single S or D.

Use exactly the proper-arc and finite-junction construction in that theorem,
Section 2. Alternating loaded endpoints would force a transverse junction
at which the two path connections pair opposite quarters of a solid
axis-parallel two-by-two block. Since both paths have only one internal
body, each contributes one loaded endpoint and one transmitter at the
junction. Thus exactly two adjacent quarter-squares are loaded.

Rotate coordinates so the loaded squares are the two lower quarters. As
in Section 4 of the width-two theorem, the block center and radius satisfy

```text
p=(0,v),       R^2=1+(v-1)^2,       -7/8<v<0.
```

In fact

```text
v < -7/10.                                           (1)
```

Indeed `R^2-1>=4641/1600>289/100=(17/10)^2`, so
`1-v=sqrt(R^2-1)>17/10`.

Reflect horizontally to make P's loaded endpoint the lower-left square
and its S transmitter the upper-right one. The actual S-force direction
from their contact p is either rightward or upward.

If rightward, P's other loaded endpoint starts at `q=(1,v)` and lies
wholly in `X>=1`. The corner-extension obstruction in Section 1 of the
width-two theorem applies: `1+v>0` and `R^2=1+(v-1)^2`. This square
cannot be contained in the disk.

If upward, its other loaded endpoint contains `q=(0,v+1)`. From (1) and
`v>-7/8`,

```text
0 < |q|=v+1 < 3/10.
```

Every point of a unit square containing q has norm at most
`|q|+sqrt(2)`, since the square's diameter is `sqrt(2)`. But

```text
|q|+sqrt(2) < 3/10+17/12=103/60<79/40<=R.
```

Such a square is strictly circle-clear, contradicting its positive
circle load. Both S-force directions are excluded. Hence alternating
loaded endpoints are impossible.

Together with the width-two theorem this shows that **any alternating
pair of transmission paths must consist of two single D paths**. The
possibility of such D-D crossings is deliberately retained.

## 2. At most one D forces the loaded order to be radial

Contract each nonempty unloaded run of the whole simple cycle to one edge.
This gives a cycle through its k loaded bodies, `3<=k<=7`. For `k=3` its
edge set is already the radial three-cycle. Suppose `k>=4`.

Direct contacts between loaded bodies join radial neighbors, by Sections
1 and 2 of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). Draw the
contracted cycle abstractly as straight chords between k points on a
circle in that radial order. This drawing is a combinatorial device;
no force or contact path has been replaced in the physical packing.

If a Hamiltonian cycle on circularly ordered points is not the boundary
cycle, two of its edges have alternating endpoints. One elementary proof
is to choose a diagonal edge: its endpoints divide the remaining vertices
into two nonempty boundary arcs. The rest of the Hamiltonian cycle is a
path between those endpoints and must visit both arcs. An edge on that
path must therefore cross the chosen diagonal, since the endpoints cannot
be revisited internally.

Neither edge in a crossing pair is a boundary edge, so neither can be a
direct loaded contact. Thus they represent two vertex-disjoint nonempty
transmission paths in the original whole cycle. If there is at most one
D transmitter, at least one of the two paths is S or SS, contradicting
Section 1 or the width-two uncrossing theorem. Therefore the contracted
cycle must be the radial boundary cycle.

This proves radial order from the reviewed physical junction analysis.
It does not assume planarity of the original body-pair graph, and it makes
no claim when two or more D transmitters are present.

## 3. The global angular budget

Let t be the number of SS runs, s the number of single S runs, and d the
number of single D runs. Let m be the total number of bodies in the whole
component. Then

```text
m=k+2t+s+d,            t+s+d<=k,            d<=1.       (2)
```

Use the exact reference half-angles established in
[SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md):

```text
c=asin(8/25), v=asin(16/25),
a=asin(24/25), b=asin(328/425).
```

Every ordinary loaded-center gap exceeds `2c`, and a transmission gap
exceeds `2a`, `2v`, or `2b` for SS, S, or D, respectively. These bounds
apply to the actual radial gaps because Section 2 has proved that every
contracted edge is a radial neighbor pair. They remain valid if a gap
exceeds pi, since the gap is at least its minor angle.

Summing the k gaps around the circle gives the necessary condition

```text
Omega := t a+s v+d b+(k-t-s-d)c < pi.                  (3)
```

The same reviewed note proves

```text
a>2pi/5, v>pi/5, c>pi/10, b>pi/4,
v+b>pi/2,               a+b+3c>pi.                    (4)
```

It also follows directly that `v>2c`: since `2c<pi/2`,
`sin(2c)=(16/25)cos(c)<16/25=sin(v)`.

## 4. Exact finite batches excluded by the budget

The coarse bounds in (4) give

```text
Omega > (k+3t+s+3d/2)pi/10
       = (m+t+d/2)pi/10.                              (5)
```

Consequently (3) fails in all of the following cases:

* `m=10`;
* `m=9` with `t>=1`;
* `m=8` with `t>=2`.

Two additional cases use the sharper identities in (4).

If `m=9`, `d=1`, and `t=0`, equation (2) gives `k+s=8`.
Since `k<=7`, at least one S run is present. Thus

```text
Omega=(v+b)+(s-1)v+(k-s-1)c
 > pi/2 + [2(s-1)+(k-s-1)]pi/10
 = pi/2 + (k+s-3)pi/10
 = pi.
```

All multiplicities in this decomposition are nonnegative: they count
actual S runs and direct loaded contacts. This excludes every remaining
nine-body case with exactly one D.

If `m=8`, `t=d=1`, equation (2) gives `k+s=5`. Therefore

```text
Omega=a+b+s v+(k-s-2)c
      =a+b+3c+s(v-2c)
      >pi.
```

This uses the exact triple-angle inequality `a+b+3c>pi`, not a numerical
angle estimate. Together these arguments exclude precisely the following
finite selection from the fixed inventory:

```text
d<=1, and either
  m=10; or
  m=9 with (t>=1 or d=1); or
  m=8 with (t>=2 or (t>=1 and d=1)).                    (6)
```

In the last line, `t>=2` was handled by the coarse argument; its only
remaining possibility is `t=d=1`. No condition is imposed on how many
direct contacts lie between the transmission runs.

## 5. Explicit inventory and review boundary

The exact covered IDs, canonical words, loaded counts, and transmitter-run
counts are printed in
[single_side_cycle_batch.json](single_side_cycle_batch.json). They are
selected by the integer conditions (6) from the fixed 279-case inventory:

| Component length | Covered transmitter cases |
| --- | ---: |
| 8 | 9 |
| 9 | 38 |
| 10 | 70 |
| Total | 117 |

The selection contains 27 of the 28 previously hand-closed cases. The
remaining earlier case is the shared-endpoint D-D seven-loaded pattern,
which has two diagonal transmitters and lies outside this theorem.
Thus the reviewed hand results give 118 closed cases altogether, leaving
161 cases in the fixed overclassification. The 90 additional hand exclusions
are recorded in [cycle_progress.json](cycle_progress.json).
