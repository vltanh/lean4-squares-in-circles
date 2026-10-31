# Unfinished completion work after the strict side-source reduction

**Status: exploratory continuation, not a proof or case closure.** The
necessary-form argument in
[STRICT_SIDE_SOURCE_RATIONAL_REDUCTION.md](STRICT_SIDE_SOURCE_RATIONAL_REDUCTION.md)
is complete. The computational enclosures described here are unfinished.

## What is now exact

In the both-unique-D-endpoint LSLSLD branch, both S supports are strict
inner corners. The source circle-feature table has five rows: E_A with
unique upper-left circle vertex; its E_B reflection; and V_V with unique
upper-left, unique upper-right, or both upper circle vertices.

For E_A the circle geometry and contact relation express all four centers
A,B,C,D and R^2 rationally in the two S half-angle parameters x,y.
The two remaining necessary equalities are the endpoint torque equation E=0
and source-force alignment G=0, with nonzero denominators retained.
Both S-transmitter slides still range over their whole intervals.

## Floating interval prototypes

[explore_strict_diagonal_interval.py](explore_strict_diagonal_interval.py)
tries a three-dimensional parameterization by squared radius, D-endpoint
position fraction and D-height fraction. Its interval arithmetic uses
ordinary floating-point endpoints without outward rounding. It is
**not an exact certificate**. The scan is limited by a node budget and
retains unresolved cells; it does not establish a root count or exclusion.
The source support/circle rows are necessary equation families, not claims
of physical realizability. A node-budget stop can leave coarse cells.

[explore_strict_side_source_bivariate.py](explore_strict_side_source_bivariate.py)
uses the exact two-angle formulas with the same non-rigorous floating
interval helper. It is a more focused experiment. Its default run visited
131013 nodes, accepted 119 target-box leaves near the previously known
numerical E_A candidate, and left 1789 unresolved leaves at depth 32.
The target rectangle is approximately

```text
0.2637<=x<=0.2639,       0.2413<=y<=0.2416.
```

Accepting that rectangle means only that the scan stops there; no root
existence, uniqueness or capacity is certified. The whole scan remains
exploratory because its endpoints are not rounded outward and its
unresolved cells have not been excluded or covered by capacity regions.

## A genuine boundary obstacle for a future exact enclosure

Unresolved cells include the known root neighborhood and a degenerate
boundary near x=y=sqrt(2)-1. At that boundary p=q=r=s=1/sqrt(2), the
source contact length is zero and the D contact height is an endpoint
rather than a relative side-interior point. It is outside the strict
physical family, but the cleared necessary equations vanish there.
Deleting a neighborhood merely because the boundary point is invalid
would lose possible strict realizations approaching it.

One exact description of this formal boundary is

```text
K=2+sqrt(2),       Y=1+3/sqrt(2),
d=0,       T=Y-K^2/(4Y),
u=v=K/2,       H_A=H_B=T/2,
R^2=K^2/4+T^2/4,       -h=T/2.
```

These are identities for a limiting necessary-equation solution, not an
assertion of a selected physical stress or a ten-square packing. A future
proof must isolate and exclude the boundary root with valid strictness
arguments, or give a completion bound on a neighborhood that includes it.

## Capacity route still requiring proof

A prospective sufficient condition is to use only A,B,C,D as a four-square
core and cover the remaining possible center domain by at most five
regions of diameter below one. Then at most five further squares can fit,
including the two S transmitters, and total capacity is at most nine.
The [finite center-cover criterion](FINITE_CENTER_COVER_CAPACITY.md) supplies
the inference once a uniform exact cover is established.

No such four-core certificate is provided here. In particular the full
transmitter slides cannot be discarded from an argument that needs them
to seal a cavity. The V_V source rows and radial D endpoints also remain
open. None of these numerical or algebraic explorations changes a master
status.
