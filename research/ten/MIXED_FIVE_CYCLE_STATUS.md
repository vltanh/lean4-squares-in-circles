# Remaining patterns in a three-loaded positive five-cycle

This is an index of proved reductions and the exact remaining cases for a
whole positive component

```text
A-U-C-V-B-A,
```

with precisely A,B,C circle-loaded and U,V unloaded degree-two bodies.
The cycle pattern itself follows from
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). Each
transmitter is side type S of width one, or diagonal type D of width
`sqrt(2)`. The radius and physical-stress conventions are those of the
linked manuscripts. **This five-cycle has not yet been excluded.**

The generic reductions exclude parallel outgoing transmission directions,
coincident C contacts, and two directions both normal to C's sides:

- [Parallel directions](PARALLEL_MIXED_FIVE_CYCLE.md).
- [Coincident contacts, equal transmitter types](COMMON_CORNER_SIDE_TRANSMISSIONS.md).
- [Coincident contacts, mixed types](COMMON_CORNER_MIXED_TRANSMISSIONS.md).
- [Two side-normal directions](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).

In the stated radius window, a circle-loaded square has either one or two
circle vertices. Three circle vertices would make the disk center the
square center and its radius `1/sqrt(2)`, outside the window. Thus the
following two central-square branches are exhaustive for this component
pattern.

## C has one circle vertex

Both C contacts cannot be vertices, by
[the distinct-vertex exclusion](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).
The side-normal theorem then gives the following exact form, after
reflecting or exchanging C's own axes:

```text
c_C=(a,b),              b>a>0,
R^2=(a+1/2)^2+(b+1/2)^2,
P=(a-1/2,b-1/2),
Q=(a-1/2+d,b-1/2),      0<d<1.
```

U starts at P in direction `(-p,-q)` with `p>q>0`, `p^2+q^2=1`.
V starts at Q vertically downward. With `rho=q/p`, force and torque
balance give

```text
(b-a)/(a+1/2) = d(1-rho)/(1-d).
```

Exactly these transmitter choices remain:

| U at P | V at Q | Further proved restriction |
| --- | --- | --- |
| S | S | No completion exclusion yet |
| S | D | If A's contact is a vertex, an incident edge must point strictly right in C's frame |
| D | S | V contacts a vertex of B, and B is not parallel to C |

The missing D-D row is excluded by
[DIAGONAL_MIXED_FIVE_CYCLE.md](DIAGONAL_MIXED_FIVE_CYCLE.md).
The extra S-D restriction is proved in
[SIDE_DIAGONAL_LEFT_ENDPOINT.md](SIDE_DIAGONAL_LEFT_ENDPOINT.md);
the contact in a side of A remains untreated by that argument.
The D-S restriction is proved in
[DIAGONAL_SIDE_ENDPOINT_REDUCTION.md](DIAGONAL_SIDE_ENDPOINT_REDUCTION.md).
It does not exclude a rotated, vertex-supported B.

## C has two circle vertices

In a suitable frame

```text
C=[L,L+1] x [-1/2,1/2],
L=sqrt(R^2-1/4)-1.
```

Both contacts must lie on the left side, including its two corners.
Their origin torques force one contact above zero and the other below
zero; the zero-torque midpoint alternative has parallel directions and
is excluded. At least one contact is a corner, since two side-interior
contacts would also have parallel directions.

**This central-body branch is now closed.** The S-S exclusion is
[RADIAL_SIDE_MIXED_FIVE_CYCLE.md](RADIAL_SIDE_MIXED_FIVE_CYCLE.md),
the S-D exclusion is
[RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md),
and the complete D-D exclusion is
[RADIAL_SIDE_DD_EXCLUSION.md](RADIAL_SIDE_DD_EXCLUSION.md), using the
restrictions in [RADIAL_SIDE_DOUBLE_DIAGONAL.md](RADIAL_SIDE_DOUBLE_DIAGONAL.md).
The last argument covers its unequal-angle, smaller-radius case by
endpoint clearance, physical torque balance, and a strict separating axis.

These proofs use the slightly stronger bound `R^2>5/2+sqrt(2)`, explicitly
derived from the pinned n=8 lower theorem and its coarse stationary bracket.
Its generated interval-data dependency remains stated; no independent
hand derivation of that imported bracket is claimed.

## Four loaded bodies

For a whole five-cycle with four loaded bodies and one unloaded degree-two
body, [MIXED_FIVE_FOUR_LOADED.md](MIXED_FIVE_FOUR_LOADED.md) excludes a
side transmitter throughout the same radius window. Only the diagonal
transmitter remains. This is a different component type from the
three-loaded/two-transmitter patterns above.

## Exact remaining five-cycle obligations

| Roadmap ID | Remaining family | Status |
| --- | --- | --- |
| C15 | Unique-circle C; vertex transmitter S, side transmitter S | OPEN |
| C16 | Unique-circle C; vertex transmitter S, side transmitter D | OPEN |
| C17 | Unique-circle C; vertex transmitter D, side transmitter S | OPEN |
| C19 | Four loaded bodies; the sole unloaded transmitter D | OPEN |

For each row, either exclude the physical component or prove that its
completion has capacity at most nine. These are the only remaining
five-cycle families after the ordered reductions in
[CASE_ROADMAP.md](CASE_ROADMAP.md). They still permit continuous coordinates
and varying endpoint contact ownership. Closing them does not by itself
settle larger mixed cycles, branching components, or other loaded-ring
ownership patterns.
