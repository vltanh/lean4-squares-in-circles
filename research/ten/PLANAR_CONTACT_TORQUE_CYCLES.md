# Planar contact junctions and directed torque cycles

These are conditional structural lemmas for the physical positive-stress
certificate described in
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md). They do not
classify cyclic components or prove that a cycle encloses the origin.

The packing consists of pairwise interior-disjoint unit squares. Contact
forces act at actual shared boundary points, point into the receiving
square, and are perpendicular to a supporting line of that square at the
application point. Circle forces are positive multiples of the inward
radial vector. Each body balances force and torque.

## 1. A planar incidence graph retaining the physical forces

First aggregate forces between a body pair as in the physical-stress
construction, so each positive pair uses one actual shared point. Create
a junction for each distinct application point `p`. At this junction,
retain the list of all original pair forces and their supporting normals.
For each incident body `S`, let `F(S,p)` be the sum of its forces at `p`.

Each summand belongs to the inward normal cone of `S` at `p`. That cone
is a ray at a side-interior point and a quadrant at a vertex. It is
pointed, so a sum involving a positive force cannot be zero. Furthermore,
the aggregate still belongs to the same normal cone. Thus it is itself
a physical supporting force at `p`. Aggregation preserves every body's
total force and torque. At each junction,

```text
sum_(S incident to p) F(S,p) = 0.                  (1)
```

Form a bipartite graph with one vertex at each body center and one vertex
at each junction, joining a body center to every junction on its body.
Embed each incidence edge as that straight segment. Except at its
boundary endpoint, the segment lies in the square's open interior.
Segments belonging to different bodies therefore cannot cross in their
interiors. Two distinct such segments within one square meet only at
its center: each ray from an interior point meets a convex body's boundary
in only one point. The resulting incidence graph is planar.

Every junction has degree at most four. Near a boundary point a square
occupies an open angular sector of angle at least `pi/2`; the sectors of
incident square interiors are disjoint. Their angles sum to at most
`2pi`.

This construction does not assert that the original body-pair graph is
planar. Several bodies can meet at one point, and replacing a junction by
all pair edges can introduce crossings. The original pair forces remain
available as labels at the junction; no separation witness is discarded.
Nor are incidence edges mechanical bars: their embedded direction need
not agree with the force direction.
An aggregate can be radial even when the original point-contact normals
were selected to be nonradial. Properties tied to that original normal
selection, such as its body-pair bridge exclusion, must not be transferred
automatically to the new incidence graph.

## 2. Torques form a circulation

Use the scalar planar cross product and define

```text
tau(S,p) = p × F(S,p).
```

Every body's torque balance about the origin gives

```text
sum_p tau(S,p)=0,                                  (2)
```

because every circle force is radial and has zero torque about the
origin. Taking the cross product of (1) with `p` gives the same zero sum
at every junction.

Delete zero-torque incidences. Orient a remaining incidence from its
junction to its body if `tau>0`, and from its body to its junction if
`tau<0`; give it weight `|tau|`. Equations (1)–(2) say that incoming and
outgoing weights balance at every graph vertex. Hence every nonempty
remaining graph contains a directed simple cycle, and its weighted edges
can be decomposed into directed cycles by the elementary finite-flow
algorithm: follow positive outgoing edges until a vertex repeats, subtract
the least weight on the resulting cycle, and repeat.

Each simple cycle is a Jordan curve in the planar incidence embedding.
It alternates body-center vertices and physical contact junctions. The
cycle need not be a cycle in a graph of center-to-center contact segments.

## 3. An origin-free component has nonzero torque

Consider a nonzero positive component. Suppose no body of this component
contains the origin, even on its boundary. Then some incidence torque
is nonzero; consequently the component contains a directed torque cycle.

Suppose instead that every incidence torque is zero. Every junction point
is then nonzero, and each aggregate force is radial:

```text
p = r e,    r>0, |e|=1,
F(S,p)=k(S,p)e,    k(S,p) != 0.                    (3)
```

Choose a body `S` of minimum distance from the origin in the component.
We first show that it cannot receive an outward force, meaning `k(S,p)>0`.
Such a force is an inward normal of `S`, so the whole square satisfies
`e dot z>=r`; in particular `distance(0,S)>=r`.

Junction balance supplies another incident body `T` with `k(T,p)<0`.
This body supports the line `e dot z=r` from the inner side. The segment

```text
p−t e,    0<=t<=1,
```

lies in `T`. To check this, write the square in its own axes. At the
support point, each nonzero coordinate of `e` points toward its outward
side; subtracting `t` times that coordinate changes it inward by at most
one, the square's side length. If `r<=1`, this segment contains the
origin, contrary to the hypothesis. If `r>1`, it gives

```text
distance(0,T) <= r−1 < r <= distance(0,S),
```

contradicting the choice of `S`. Therefore all contact forces on `S`
are radially inward.

The compact convex square `S` has a strict separating direction from the
origin: there is a vector `a` with `a dot z>0` for every `z in S`.
Each of its nonzero radially inward contact forces has strictly negative
dot product with `a`; the same holds for every positive circle force.
There is at least one such force because the component is nonzero.
Their sum therefore cannot vanish. This contradicts force balance and
proves the lemma.

The strict origin-free hypothesis is deliberate. When a body contains
the origin, the separating direction in the last paragraph does not
exist, and a purely radial stress is not excluded by this argument.

## 4. The remaining topological issue

The lemmas establish a planar physical support and, for an origin-free
component, a directed torque cycle. They do **not** establish that the
cycle's bounded region contains the origin. Circle-load balance only
places zero in the convex hull of the loaded circle points; it does not
by itself place zero inside a particular contact cycle or inside the
convex hull of the corresponding body centers. An origin-enclosure
argument, or a classification of cycles that do not enclose it, remains
necessary before using these cycles to restrict the three- or four-inner-
center cases.
