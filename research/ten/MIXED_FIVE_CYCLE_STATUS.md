# Completed positive five-cycle exclusions

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
linked manuscripts. **This three-loaded five-cycle is now excluded.**

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

All four ordered transmitter choices are now excluded:

| U at P | V at Q | Reviewed hand exclusion |
| --- | --- | --- |
| D | D | [Diagonal pair](DIAGONAL_MIXED_FIVE_CYCLE.md) |
| D | S | [D-S proof](DIAGONAL_SIDE_EXCLUSION.md) |
| S | D | [S-D proof](SIDE_DIAGONAL_EXCLUSION.md) |
| S | S | [S-S proof](SIDE_SIDE_EXCLUSION.md) |

The final S-S proof first uses the
[vertex exclusion](SIDE_SIDE_VERTEX_EXCLUSION.md), then a joint contact
projection bound and convex endpoint estimates to place every vertex of A
strictly inside the containing circle, contradicting A's positive load.
Its exact final squared-radius margin is `369/40000` at the lower radius.

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
side transmitter throughout the same radius window. The
[diagonal exclusion](DIAGONAL_FIVE_CYCLE_EXCLUSION.md) now closes the
other transmitter type for the generic certificate selected before
classifying the positive graph. Its normal choice forces side-interior
endpoint contacts, whereas the nearer-endpoint theorem forbids side support.
This is a different component type from the three-loaded patterns above.

## Five-cycle completion status

| Roadmap ID | Family | Status |
| --- | --- | --- |
| C19 | Four loaded bodies; the sole unloaded transmitter D | [HAND CLOSED for the selected certificate](DIAGONAL_FIVE_CYCLE_EXCLUSION.md) |

No whole five-cycle family remains open in the selected-certificate
classification of [CASE_ROADMAP.md](CASE_ROADMAP.md). The unrestricted
problem still has larger mixed cycles, branching components, and other
loaded-ring ownership patterns. Equality and Lean integration remain
separate obligations.
