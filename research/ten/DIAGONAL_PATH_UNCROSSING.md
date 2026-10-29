# Diagonal transmission paths cannot cross in a whole simple cycle

**Status:** exact hand theorem; two independent full mathematical reviews
passed on 2026-10-29, including the support-face cases, physical junction
argument, and radial-order corollary.

Work with a hypothetical ten-square packing in the radius window
`79/40<=R<3/sqrt(2)` and its physical positive-stress graph. Suppose a
whole positive component is a mixed simple cycle. Then **no two
vertex-disjoint nonempty transmission paths have alternating loaded
endpoints**. In particular, its contracted cycle follows the radial
circular order of the loaded bodies, regardless of the number of diagonal
transmitters.

The previously reviewed [width-two](TRANSMISSION_PATH_UNCROSSING.md) and
[single-side](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md) uncrossing theorems
already cover every alternating pair except two single diagonal paths.
This note excludes that last case. It uses degree two at a loaded
endpoint, so it makes no corresponding assertion for branching components.

## 1. The only remaining transverse junction

Assume two single-D paths have alternating loaded endpoints. The proper
center/contact arcs, finite-intersection argument, and local perturbation
argument in Section 2 of
[TRANSMISSION_PATH_UNCROSSING.md](TRANSMISSION_PATH_UNCROSSING.md) give a
transverse junction of four squares. The paths pair opposite quarters of
a solid square of side two. Each path contributes one loaded endpoint
and one unloaded diagonal transmitter, so the two loaded quarters are
adjacent.

Rotate coordinates so that the loaded squares are the lower quarters.
The geometry in Section 4 of that theorem gives

```text
p=(0,v),       R^2=1+(v-1)^2,       -7/8<v<0.
```

Name the four squares

```text
A=[-1,0] x [v-1,v],      B=[0,1] x [v-1,v],
V=[-1,0] x [v,v+1],      U=[0,1] x [v,v+1].
```

Here A and B are loaded; U and V are diagonal transmitters. The two
crossing positive contacts are A--U and B--V at p. The only geometric
circle vertex of A is

```text
w=(-1,v-1).
```

Indeed its two center coordinates are strictly negative, so this corner
is its unique farthest vertex. Since A is loaded, its total inward circle
force is `-lambda*w` for some `lambda>0`.

The diagonal transmission through U runs from p to `(1,v+1)`. Its inward
force on A at p is therefore `-a(1,1)` for some `a>0`.

## 2. Force balance leaves one scalar and one supporting face

A has degree two in the whole positive graph. Let q be the actual contact
point for its other positive edge, and let G be that edge's inward force
on A divided by lambda. With `t=a/lambda>0`, force balance gives

```text
G=(t-1,t+v-1).                                      (1)
```

This vector is nonzero because v is negative. The contact q lies on the
support face of A exposed by the inward normal G. Equivalently, the
linear functional `G dot x` takes its minimum on A at q. The torque
of the circle force about zero is zero; torque balance on A gives

```text
q cross G=-t v.                                     (2)
```

The possibilities are exhaustive and elementary:

* If `0<t<1`, both components of G are negative. Its support point is
  `q=p=(0,v)`. Equation (2) becomes `-v(t-1)=-tv`, forcing `v=0`,
  a contradiction.
* If `t=1`, then `G=(0,v)`. Its support face is the top side, so
  `q=(x,v)` with `-1<=x<=0`. Equation (2) is `xv=-v`; since `v!=0`,
  it forces `q=(-1,v)`.
* If `1<t<1-v`, the components of G have signs positive and negative.
  Its unique support point is `q=(-1,v)`. Substitution in (2) gives
  `1-t-tv=-tv`, or `t=1`, a contradiction.
* If `t=1-v`, then `G=(-v,0)` with `-v>0`. The support face is the
  left side, so `q=(-1,y)` with `v-1<=y<=v`. Equation (2) gives
  `vy=v(v-1)`, hence `q=w`.
* If `t>1-v`, both components of G are positive and the support point
  is directly `q=w`.

The last two possibilities are impossible: two packing squares cannot
share a point of the containing circle. The precise circle-point lemma
is recorded in Section 1 of
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md).

The only remaining possibility is consequently

```text
t=1,       q=(-1,v),       G=(0,v).                  (3)
```

This keeps every side-normal boundary case; no strict-normal selection
or perturbation of the force certificate has been used.

## 3. The forced other neighbor cannot fit in the disk

Let H be A's other positive neighbor. By (3), the force into H at q is
vertical upward. Thus H contains q and lies wholly in `y>=v`.
The square V occupies the northeast quadrant at q, since

```text
V=q+[0,1] x [0,1].
```

H is distinct from V: U and V already each have their two diagonal-path
neighbors, and the two transmission paths are vertex-disjoint. More
directly, a vertical upward force on V at its lower-left vertex would
contradict V's required diagonal transmission force.

The local interior sector of H at q has angle at least `pi/2`.
It lies in the upper half-plane and is disjoint from V's open northeast
quadrant. Therefore it must be exactly the northwest quadrant. A side
interior would have angle pi and cannot fit; q must be a vertex, with
incident edges pointing left and up. Since H is a unit square, it is
exactly

```text
H=[-2,-1] x [v,v+1].
```

But its vertex `(-2,v)` has squared-radius excess

```text
4+v^2-R^2
 =4+v^2-[1+(v-1)^2]
 =2(1+v)>0,
```

because `v>-7/8>-1`. This contradicts containment in the radius-R disk.
The transverse D-D junction is impossible.

## 4. Unrestricted radial order for mixed simple cycles

Every nonempty transmission path has type S, D, or SS, by the width
restriction in [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).
The two prior uncrossing theorems and the preceding argument now exclude
alternating endpoints for every vertex-disjoint pair of such paths in a
whole mixed simple-cycle component.

Contract the unloaded runs. The resulting cycle has `3<=k<=7` loaded
vertices. Direct loaded contacts join radial neighbors. If its abstract
chord drawing on the circle in loaded radial order were not the boundary
cycle, it would have a pair of edges with alternating endpoints. Neither
would be a direct loaded contact, so the pair would correspond to two
vertex-disjoint transmission paths, which is impossible. This is exactly
the combinatorial argument in Section 2 of
[SINGLE_SIDE_TRANSMISSION_UNCROSSING.md](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md),
now without its restriction on the number of D transmitters. For `k=3`,
the contracted cycle is already the radial three-cycle.

Thus every contracted mixed simple cycle follows the circular radial
order, up to reversal. In particular the reviewed global angular budget

```text
t a+s b_S+d b_D+(k-t-s-d)c < pi
```

applies with no restriction on d. Here t,s,d count the SS, S, and D runs,
and the half-angle constants are

```text
a=asin(24/25), b_S=asin(16/25),
b_D=asin(328/425), c=asin(8/25).
```

This statement does not assert that every remaining angular-budget case
is realizable, and it does not exclude branching positive components.
Its finite-case consequences are to be tracked separately after review.
