# Large blocks need completion geometry: a uniform long-ear obstruction and an exact seven-body diagnostic

Date: October 30, 2026 UTC. Author: block_ears.

**Status: new complete elementary derivations, awaiting independent review.**
This source does not close an original coarse or fine row. It gives a
radius-free graph restriction on actual unloaded transmitter paths, an
exact counterexample to a proposed graph-only extraction, and a direct
physical capacity check of that counterexample. In particular it does
not exhibit nine squares below the target radius.

Throughout, a unit square is a closed Euclidean square of side one;
distinct actual squares have disjoint open interiors. A physical stress
uses the actual positive pair forces, their unchanged shared application
means, and nonnegative multipliers at the actual containing-circle corners.
The sign convention is that the contact forces at a body use its outward
normals and its circle contribution is `2 sum lambda_z z`.

## 1. A radius-free prohibition on short returns around a long unloaded ear

Let

    A -- U_1 -- ... -- U_k -- B

be an actual positive path with distinct endpoints. Every displayed
internal square is **genuinely unloaded and of true positive degree two**
in the full original component. No outside positive edge has been
deleted to obtain this degree. Other physical contacts and all other
actual squares remain.

At every internal body its two nonzero forces cancel. Consistently
orienting the path from A to B makes all its signed unit normals equal
to one unit vector d. For any actual unit S let

    h_S(d) = (|d.u_S| + |d.v_S|)/2 >= 1/2,

where u_S,v_S are its actual orthonormal side axes. Summing the original
tight support equalities gives, with no lost internal widths,

    d.(c_B-c_A)
      = h_A(d) + h_B(d) + 2 sum_j h_(U_j)(d)
      >= k+1.                                             (1)

Now suppose there is **any physical contact walk**

    A = T_0, T_1, ..., T_l = B

of l edges. The walk need not be positive, need not lie in the selected
graph, and need not be disjoint from the first path. At a physical
contact point p between consecutive units, their centers are each at
distance at most `1/sqrt(2)` from p. Thus

    |c_(T_(i+1))-c_(T_i)| <= sqrt(2).

The triangle inequality and (1) imply the uniform necessary condition

    k+1 <= l sqrt(2).                                    (2)

**Consequences.**

* The two physical neighbors of an actual unloaded true-degree-two
  square cannot physically touch: k=l=1 would give `2<=sqrt(2)`.
* If k=2, the endpoints cannot physically touch or share any physical
  neighbor: l<=2 would give `3<=2sqrt(2)`, contradicted by `9>8`.
  In particular, a two-internal-unit unloaded ear cannot be added
  between vertices already joined by a physical path of length at
  most two.
* Every actual cycle containing two consecutive unloaded
  true-degree-two squares has length at least six. Its return route
  must use at least three edges, and therefore at least two additional
  actual squares.

These statements use force balance only at the true internal degree-two
bodies. They impose no degree, load, frame, circle mask, or torque
premise at A or B. They do not remove any completing squares. They hold
at every containing radius and for the complete physical contact graph.

The existing four-square axial theorem at the target radius strengthens
(1) quantitatively, but is not needed for the strict short-return
obstruction (2).

## 2. A large biconnected stressed block need not have such a long ear

The following exact configuration is a diagnostic for structural
extraction. It has seven actual squares, a connected biconnected
positive body-pair graph, four positive circle loads, and full force
and torque balance. Nevertheless no positive path has two consecutive
unloaded true-degree-two internal vertices.

Take seven aligned unit squares with centers

| Body | Actual center |
| --- | --- |
| A | `(-1,1/2)` |
| B | `(-1,-1/2)` |
| C | `(1,-1/2)` |
| D | `(1,1/2)` |
| U | `(0,1)` |
| M | `(0,0)` |
| L | `(0,-1)` |

Every pair is interior-disjoint: the absolute difference of at least
one center coordinate is at least one. Their containing squared radius
is exactly

    r^2 = 13/4 < Q := 1105/256.

The four outer corners

    z_A=(-3/2,1), z_B=(-3/2,-1),
    z_C=(3/2,-1), z_D=(3/2,1)

have squared norm 13/4. Every other corner has squared norm at most
13/4; in particular the far U/L corners have squared norm 5/2 and
all M corners have squared norm 1/2.

Give each of these four circle atoms multiplier `lambda=1/4`, and
give every other circle coefficient zero. Thus the circle multipliers
are nonnegative and normalized to sum one. The complete positive pair
list is the following. An edge X-to-Y has force `mu*n` at X, the
opposite force at Y, and the same actual application p at both.

| Directed pair | mu | n | Actual p |
| --- | --- | --- | --- |
| A to U | `5/8` | `(1,0)` | `(-1/2,3/4)` |
| U to D | `5/8` | `(1,0)` | `(1/2,3/4)` |
| A to M | `1/8` | `(1,0)` | `(-1/2,1/4)` |
| M to D | `1/8` | `(1,0)` | `(1/2,1/4)` |
| B to L | `3/4` | `(1,0)` | `(-1/2,-2/3)` |
| L to C | `3/4` | `(1,0)` | `(1/2,-2/3)` |
| A to B | `1/2` | `(0,-1)` | `(-1,0)` |
| D to C | `1/2` | `(0,-1)` | `(1,0)` |

Every point lies in the relative interior of the original shared side
segment. These are legitimate complete side means, equivalently
nonnegative combinations of the actual two endpoint atoms. All positive
pair multipliers are strictly positive. Other physical contacts, such
as U--M and M--L, have zero multiplier and remain occupied.

### 2.1. Exact full balance

At A the full contact force is `(3/4,-1/2)`, which cancels
`2 lambda z_A=(-3/4,1/2)`. Its contact origin moment is

    -(5/8)(3/4) -(1/8)(1/4) +(1/2) = 0.

At B the full contact force is `(3/4,1/2)`, which cancels
`2 lambda z_B=(-3/4,-1/2)`. Its contact origin moment is

    (3/4)(2/3) -(1/2) = 0.

Reflection in the vertical axis proves the complete D and C equations
with their unchanged actual weights and means. At each of U,M,L, the
two contact forces are opposite, equal, and applied on one common
horizontal line, so both force and origin torque vanish. Every circle
atom has zero origin torque. Force balance plus zero origin torque
also gives zero torque about each actual body center.

This verifies the entire physical equilibrium certificate directly,
without a minimization claim or a numerical stress solver.

### 2.2. Exact block and degree statements

The positive graph is the six-cycle

    A -- U -- D -- C -- L -- B -- A

together with the open ear `A--M--D`. A cycle is biconnected; adding
an open ear between two distinct cycle vertices preserves connectivity
after deleting any single vertex. Hence this is one seven-vertex
biconnected block, of the coarse graph type `C1.7.b0`.

The true positive degrees are

    deg(A)=deg(D)=3,
    deg(B)=deg(C)=deg(U)=deg(M)=deg(L)=2.

Exactly A,B,C,D have positive circle load. Each unloaded degree-two
square U,M,L has two loaded neighbors. Therefore there cannot be a
positive path with two consecutive unloaded true-degree-two vertices.

The graph is planar in the actual shared-side geometry, and all four
loaded bodies have direct physical access to the circle. No free
point-contact normal or incompatible planarization is used.

**What this disproves:** biconnectivity of order at least five, positivity,
planarity, true-degree data and full torque balance do not by themselves
force a long unloaded transmitter ear or the sharp radius Q. A proof
using the actual nine-body completion hypothesis can still establish
either conclusion under additional premises. The example is below
the research lower window `79/40`, so it is not a counterexample to a
theorem that explicitly uses that lower window.

## 3. Its two missing units cannot be ignored: in fact not even one fits

The same fixed seven actual squares cannot be supplemented by any eighth
unit square in the disk of squared radius Q, even with a completely
independent orientation. This elementary capacity check makes the
diagnostic's completion boundary explicit.

For any unit square in that disk, the farthest-corner formula gives

    |c|^2 + |c| + 1/2 <= Q,
    |c| <= sqrt(1041)/16 - 1/2 < 91/60.                 (3)

The strict comparison follows from

    (121/60)^2 - 1041/256 = 31/57600 > 0.

Any two actual centers have distance at least one, because the open
radius-one-half disks inside their squares are disjoint. If an extra
center c=(x,y) existed, its separation from M would give `|c|>=1`.
By the reflection symmetries of the seven occupied centers, take
`x,y>=0` without changing the separation problem.

If `x<=3/4`, then `|c|>=1` gives

    y>=sqrt(7)/4>1/2.

Together with (3), this implies `|y-1|<31/60`. Its distance to the
actual center U=(0,1) is therefore bounded by

    |c-U|^2 < 9/16 + (31/60)^2
             = 1 - 307/1800 < 1,                      (4)

a contradiction.

If `x>3/4`, then (3) gives `|x-1|<31/60` and

    y^2 < (91/60)^2 - 9/16 = 16/9 - 1/25 < 16/9.

Hence `0<=y<4/3`, so `|y-1/2|<5/6`. Its distance to the actual
center D=(1,1/2) satisfies

    |c-D|^2 < (31/60)^2 + (5/6)^2
             = 1 - 139/3600 < 1,                      (5)

again impossible. The two closed/open x alternatives cover the whole
quadrant, and the reflections cover the disk.

This proves the claimed physical capacity, retaining arbitrary frame
and all weak-contact possibilities of an alleged completion square.
It uses neither the stress equations nor a special orientation for
that square.

## 4. Implication for the large-block research plan

The long-ear theorem is a valid reusable implication for every component
size. It can remove long ears with short physical returns immediately.
Its converse is false as a bare graph/stress statement: the exact
seven-body diagnostic has a large block and no such ear.

Any global proof therefore needs to treat both of these structures:

1. A genuine long unloaded ear, retaining the near-diameter corridor and
   all actual completion units.
2. A large block with no adjacent unloaded degree-two bodies, retaining
   its branching vertices and completion geometry.

Section 3 illustrates a small center-cover proof in the second class,
but only at its stated fixed seven-unit geometry. It does not cover
all positions with that graph, all `C1.7.b0` loads, or the two-block
families `C2.35.b0` and `C2.55.b0`. Those whole obligations remain open.

No original checklist, count, source, normal selection, Lean file or
remote branch is changed by this manuscript. No Lean compilation,
CI, angle mesh, numerical pose search or packing certificate is used.
