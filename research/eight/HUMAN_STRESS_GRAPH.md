# Leaves and cycles in a minimum-contact packing

Status: analytic restrictions on the **actual contact graph** of an
unrestricted radius minimizer. Every nontrivial actual-contact component
contains a cycle. This does not assert that a chosen positive-stress graph
contains a cycle, and it does not identify the five-corner scaffold.

All squares have side length one, the containing disk is centered at zero,
and open square interiors are pairwise disjoint. An **actual contact** means
that the two closed squares meet. Among all packings attaining the minimum
radius, choose one with as few actual contacting pairs as possible. Such a
choice exists: a radius minimizer exists by
`BALANCED_SEPARATOR_REDUCTION.md`, section 1, and the number of contacting
pairs takes values in a finite set of integers.

The arguments below require

    sqrt(5/2) < R < 2.                                      (0.1)

This is the relevant range for an eight-square counterexample to the sharp
conjecture. The lower inequality follows already from area:
`8 <= pi R^2` and `pi < 22/7` give `R^2 > 28/11 > 5/2`.
The candidate construction supplies an upper bound below 2. More generally,
the lemmas apply to any number of squares whose minimum radius satisfies
(0.1).

Use the constants

    rho   = sqrt(R^2-1/4),
    r     = rho-1/2,
    b     = rho-1,
    kappa = rho-3/2.

Their relevant signs are

    3/2 < rho < 2,   r > 1,   b > 1/2,
    0 < kappa < 1/2.                                      (0.2)

## 1. A square with one contact is radial and parallel to its neighbor

**Leaf theorem.** Suppose square S has exactly one actual contact, with
square T. Then there is a unit vector n, normal to a side of both squares,
such that, writing `m=Jn` for its counterclockwise quarter turn,

    center(S) = r n,
    center(T) = kappa n + t m,     |t| < 1/2.              (1.1)

In particular T contains the disk center in its open interior. The two
outer vertices of S lie on the circle, and its inward side is on the line
`n dot x=b`.

### 1.1. The leaf center must maximize support in any chosen contact normal

Choose a unit separating normal n directed from T toward S. For a square U,
let `h_U(n)` denote the support of its centered square, and let

    H_U(n) = n dot center(U) + h_U(n)

denote its full support. Since S and T meet and are separated in direction
n, their touching projections satisfy

    H_T(n) = n dot center(S) - h_S(n).                     (1.2)

Hold the frame of S fixed. Its admissible centers form the compact convex
region K_R from `BALANCED_SEPARATOR_REDUCTION.md`, section 2. If its present
center did not maximize `n dot p` on K_R, move it a sufficiently small
positive distance along the segment toward a maximizing center. It remains
in K_R and makes (1.2) a strict separating inequality. Every other square
has positive distance from S, so all those separations survive a small
enough motion. The sole actual contact disappears, contradicting the
minimum contact count.

Consequently the center of S is the unique supporting center for n in its
fixed-frame K_R. Uniqueness follows from the exact support calculation in
that note, since `R>1/sqrt(2)` and `n` is nonzero.

### 1.2. A small frame rotation forces a side of S to be normal to n

Let `beta in [0,pi/4]` be the angle between n and the nearest side normal of
S, and write `c=cos(beta)`, `s=sin(beta)`. The exact support formula gives
the greatest possible inward projection of S, with this frame and with
normal n, as

    M(beta) = max_{p in K_R} n dot p - h_S(n)

            = (rho-1)c - s/2,      if c >= 2 rho s,
            = R-c-s,              if c <= 2 rho s.         (1.3)

The two expressions agree at `c=2 rho s`. In their respective open
branches their derivatives are

    -(rho-1)s-c/2 < 0,
    s-c < 0       for beta < pi/4.

Thus M is strictly decreasing on the whole interval `[0,pi/4]`. The zero
derivative of the second expression at its final endpoint does not affect
strict monotonicity.

If `beta>0`, rotate the frame a small amount toward a normal parallel to n,
and place the square at its supporting center for n in the new frame.
This placement varies continuously: the support-center expressions in
`BALANCED_SEPARATOR_REDUCTION.md`, section 2, are continuous within each
branch and coincide at the branch boundary. Equivalently, uniqueness of
the maximizer on continuously rotating compact center regions gives the
same continuity. This observation also covers the tie between the two
nearest side normals at `beta=pi/4`.

Equation (1.3) strictly increases the inward projection, making separation
from T strict. Containment is preserved, and all other positive distances
survive a sufficiently small change. This again removes the sole contact.
Therefore `beta=0`: n is a side normal of S. Its unique supporting center
is then

    center(S) = (rho-1/2)n = r n.

Its inward side lies on `n dot x=r-1/2=b`, and its two outward vertices
have squared norm `rho^2+1/4=R^2`. In particular (1.2) becomes

    H_T(n)=b.                                             (1.4)

### 1.3. Rotating the entire leaf about the disk center locks T's frame

For small real delta, rotate S about the disk center. If
`n_delta=Rot(delta)n`, the new center is `r n_delta`, its frame consists of
the directions `n_delta,Jn_delta`, and its inward side remains at signed
distance b from zero. This is an exactly disk-preserving motion.

If `H_T(n_delta)<b`, the moving square is strictly separated from T by
its inward side. All its other positive square-to-square distances survive
for sufficiently small delta. Minimum contact count therefore implies
that n is a local minimum of the full support of the fixed square T:

    H_T(n_delta) >= H_T(n)=b
    for all sufficiently small positive and negative delta.             (1.5)

Suppose n were not a side normal of T. Then throughout a neighborhood of
delta=0, the same vertex z of T uniquely realizes its support. In that
neighborhood

    H_T(n_delta)=n_delta dot z,
    d^2/d(delta)^2 H_T(n_delta)|_{delta=0} = -b < 0.

A twice differentiable function with a local minimum cannot have this
negative second derivative. Thus n is also a side normal of T.

Write `center(T)=a n+t m`. For sufficiently small delta, so that
`cos(delta)>0`, its full support is

    H_T(n_delta)
      = (a+1/2)cos(delta) + t sin(delta) + |sin(delta)|/2.

By (1.4), `a+1/2=b`, so `a=kappa`. The right and left derivatives in
(1.5) force respectively `t+1/2 >= 0` and `t-1/2 <= 0`. Hence
`|t| <= 1/2`.

The endpoints are impossible. If `t=1/2`, then for all sufficiently small
negative delta the two sine terms cancel and

    H_T(n_delta)=b cos(delta)<b.

If `t=-1/2`, the same contradiction occurs for positive delta. We used
`b>0` here. Consequently `|t|<1/2`.

Finally `0<kappa<1/2` by (0.2). In T's own frame both coordinates of its
center have absolute value strictly below 1/2. Thus zero lies in the open
interior of T. This proves the leaf theorem.

## 2. There are at most two actual leaves, with a common central neighbor

**Leaf-count corollary.** If any actual leaf exists, there is a unique
square C containing zero in its open interior, and every actual leaf is
adjacent to C. There are at most two such leaves. If there are two, their
outward normals from C are perpendicular.

Indeed, the leaf theorem makes the neighbor of each leaf contain zero in
its open interior. Two different squares cannot both do so, since their
open interiors are disjoint. Thus all leaves have the same neighbor C.

Each leaf has an outward normal n among the four signed side normals of C,
and satisfies

    center(C) dot n = kappa > 0,
    center(leaf) = r n.                                   (2.1)

Two leaves cannot use the same n: their frames and centers would make them
the identical unit square. They cannot use opposite normals, because
(2.1) would give both a number and its negative equal to positive kappa.
Among four signed orthogonal normals one may therefore use at most two,
and if two are used they are perpendicular.

Also, C is not itself a leaf. Every radial leaf has all its points in the
half-plane `n dot x>=b>0`, so it does not contain zero. The leaf theorem
has placed zero strictly inside C.

This is a conditional analytic central-square theorem: an actual leaf
forces a central square. It does not establish the existence of a central
square in an arbitrary leaf-free packing.

## 3. Every nontrivial actual-contact component contains a cycle

**Cycle theorem.** The actual contact graph of the chosen minimum-contact
radius minimizer has no tree component containing two or more vertices.

Suppose such a component were a tree. Every finite tree with at least two
vertices has at least two leaves. By section 2, the component has exactly
two leaves, both adjacent to the same square C, and C is not a leaf. A
finite tree with exactly two leaves is a path: for example, the identity

    number of leaves = 2 + sum_{degree(v)>=3}(degree(v)-2)

excludes all vertices of degree at least three. Since both endpoints are
adjacent to C, this path consists of exactly three vertices, namely the
two leaves and C.

Write their two outward normals as `n_1,n_2`. They are perpendicular by
section 2. The central square C lies strictly inside the containing disk.
To check this without any circle-contact assumption, a unit square that
contains zero in its open interior has center coordinates of absolute
value below 1/2 in its own frame, so every vertex has squared norm less
than 2. Our radius satisfies `R^2>5/2`.

Translate C by

    -epsilon(n_1+n_2),      epsilon>0.

Its full support toward either leaf decreases by epsilon. Each of its
two former contacts therefore becomes a strict separation. Strict disk
containment survives for sufficiently small epsilon. All other squares
have positive distance from C, because its actual degree in the supposed
tree component is exactly two; those distances also survive a small
translation. No other square moves.

The contact count has decreased, a contradiction. This proves the cycle
theorem.

The argument does **not** assert that a central square with one leaf must
have actual degree at least three. A central square with one leaf and a
different nonleaf neighbor is outside the three-vertex tree configuration
used in the proof.

## 4. Edge counts and what this says about stress graphs

Let N be the number of squares and let z be the number of isolated
vertices in the actual contact graph. Each nonisolated connected component
is connected and contains a cycle, so it has at least as many edges as
vertices. Summing over its components gives

    number of actual contacting pairs >= N-z.             (4.1)

In particular an eight-square minimum-contact minimizer has at least
`8-z` actual contacts.

There is at least one nontrivial component. Here is a direct proof that a
radius minimizer with `R>1/sqrt(2)` cannot have every pair of closed squares
disjoint. If it did, shrink all square centers toward zero by a common
factor `t<1`, leaving their unit frames unchanged. The largest squared
vertex norm of a square with original center p and frame `(e,f)` becomes

    t^2 |p|^2 + t(|p dot e|+|p dot f|) + 1/2.             (4.2)

For nonzero p this is strictly smaller than its value at t=1, and for
zero p it equals `1/2<R^2`. The finite collection therefore fits a
strictly smaller disk after any sufficiently small such shrink. Every
pair originally had positive distance, so all pairs remain disjoint
after a sufficiently small shrink. This contradicts minimal radius.
Together with section 3, it proves the existence of at least one actual
contact cycle.

Positive stresses from `HUMAN_ROTATIONAL_STRESS.md` are supported on actual
contacts, but actual contacts may carry zero stress. A vertex of degree
one in a positive-stress graph need not be an actual leaf: its additional
zero-stress contacts can obstruct the motions used above. Consequently we
cannot replace "actual contact" by "positive stress" in the cycle theorem.

A precise consequence is available. Every nontrivial tree component of a
chosen positive-stress graph must be incident to at least one additional
actual contact carrying zero chosen stress. That contact may join two
vertices already in the tree or may join the tree to another positive-
stress component. Otherwise the tree would itself be a nontrivial entire
component of the actual contact graph, contradicting section 3.

## 5. Remaining graph step toward the sharp inequality

These theorems produce a cycle without assuming the candidate geometry.
They do not force the cycle to contain the twin strictly interior
degree-two squares analyzed in `HUMAN_CYCLE_ANALYSIS.md`, section 9. That
result would lock all four frames of the resulting shared-neighbor
configuration, providing a useful part of the candidate scaffold.

What remains is an analytic restriction on the cyclic actual-contact
components strong enough to identify that shared-neighbor configuration,
or to derive the five-corner projected obstruction without identifying
it. Equation (4.1) alone does not supply that restriction, and neither the
leaf theorem nor rotational stationarity permits discarding zero-stress
actual contacts.
