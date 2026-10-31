# What the universal branching reductions do not yet imply

**Status:** exact obstruction and research-scope note; root and independent
full reviews passed on 2026-10-30. These examples identify missing premises
in possible next arguments. They do not give a ten-square counterexample
or invalidate the reviewed exclusions.

The current universal inputs give at most three interior body vertices,
at most one width-two endpoint pair, and a parallel classification of
unloaded two-terminal regions. Minimum-active-body consolidation can
add further restrictions. Pure graph topology and radial exposure alone
still do not force every remaining component to be a tree or a cycle.

## 1. An abstract outerplanar obstruction with three loaded ears

Take unloaded vertices U0,U1,U2 and loaded vertices L0,L1,L2. Put an
edge between each pair of U vertices, and join L_i to U_i and U_(i+1),
with indices modulo three. The graph has a disk embedding with all six
vertices on its boundary in the order

```text
U0,L0,U1,L1,U2,L2.
```

The three U--U edges are the sides of an inner triangle. Every unloaded
vertex has four distinct neighbors; every loaded vertex has degree two.
Assigning all edges the direct symbol uses no transmitters, bundles,
D paths, or width-two relations. There are no interior graph vertices.

No deletion of two vertices isolates a wholly unloaded component:

* If two U vertices are deleted, the remaining U vertex is attached to
  two remaining loaded vertices; the possible isolated third loaded
  vertex is itself loaded.
* If one U and one L are deleted, the remaining two U vertices stay
  adjacent, and at least one remaining loaded vertex attaches to them.
* If two L vertices are deleted, the U triangle stays connected and
  attaches to the remaining loaded vertex.

Thus even a reduction forbidding every unloaded two-terminal branching
region would not remove this abstract graph. It is a single mixed
component, not an entirely loaded ring.

No square packing, force assignment, or realizability claim is made for
this example. In particular its direct edges would still have to satisfy
all unit-square contact, circle-load, force, and torque equations. The
example shows only that those physical equations remain necessary after
the topological reductions.

## 2. Exposed unloaded branches need not have parallel forces

There is a concrete eight-square configuration showing that radial
exposure by itself does not force parallel forces on an unloaded body.
Use four parallel central squares with centers

```text
(1/2,1/2), (1/2,-1/2), (-1/2,1/2), (-1/2,-1/2),
```

and four parallel outer squares with centers

```text
(3/2,0), (-3/2,0), (0,3/2), (0,-3/2).
```

All squares are interior-disjoint and lie in the centered disk of
squared radius 17/4. The outer squares' two farthest vertices lie on
that circle, and all central squares are circle-clear. Each central
center has norm exactly `1/sqrt(2)`, so the reviewed radial-exposure
theorem applies to all four of them.

Give every positive contact below magnitude one, using the gradient
sign convention: its vector on a square points outward toward its
neighbor. For the central square with center
`(epsilon/2,eta/2)`, where `epsilon,eta` are each +1 or -1, the four
contact points and its vectors are

| Contact point | Vector on that central square |
| --- | --- |
| `(epsilon,eta/4)` | `(epsilon,0)` |
| `(epsilon/4,eta)` | `(0,eta)` |
| `(0,eta/2)` | `(-epsilon,0)` |
| `(epsilon/2,0)` | `(0,-eta)` |

The first two contacts are with the corresponding outer squares; the
last two are with adjacent central squares. These assignments agree
with equal and opposite forces on each shared pair. All application
points belong to positive-length shared sides.

The four vectors sum to zero. About the central square's own center,
the first two torques are respectively `epsilon*eta/4` and
`-epsilon*eta/4`, and the other two are zero. Thus every central body
is unloaded and satisfies both force and torque balance, with four
nonparallel force directions and four distinct neighbors.

For an outer square, the two contact forces are inward, have total
magnitude two, and act at transverse heights +1/4 and -1/4 relative
to its radial axis. Assign circle coefficient 1/4 to each of its two
circle vertices, with a circle vector defined as `2*lambda*w`.
For example, at the right outer square the two circle vertices are
`(2,+1/2)` and `(2,-1/2)`, and these coefficients give total circle
vector `(2,0)`. It cancels the two contact vectors. Their torques
cancel as well, while each circle vector is radial. Rotation gives
the other three outer equilibria. Scaling every coefficient and contact
magnitude by one half makes the total circle coefficient equal one.

All positive contacts are SS. There is no positive point-only VV
contact, so the strict/nonradial/nondiagonal requirements are satisfied
vacuously. The physical incidence embedding has no crossing positive
opposite pairs at any four-square point. Hence the normal-order planar
properties used by the universal reductions are present too.

This is not a counterexample to the minimum-active-body program.
The same packing also carries a smaller two-loaded stress along the
horizontal four-body chain consisting of the left and right outer
squares and the two lower central squares. Its force line is y=0;
the side-endpoint contact at the origin is allowed because the two
lower central squares share a full side. The other four squares may
remain unstressed. The reviewed two-loaded completion theorem prevents
this packing from extending to a hypothetical subcritical ten-square
packing.

Consequently a proposed theorem eliminating all exposed unloaded
branches must use an additional premise, such as the carefully specified
minimum-active-body normalization or the ten-square completion geometry.
It cannot follow from radial exposure and physical equilibrium alone.
