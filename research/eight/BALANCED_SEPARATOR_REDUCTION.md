# Eliminating centers by balanced separator forces

Status: analytic theorems for arbitrary orientations and chosen separating
axes, with a necessary stress structure for a radius minimizer. No marker
certificate, numerical classification, or assumed candidate graph is used.
These results do not yet supply the sharp eight-square inequality.

## 1. A radius minimizer exists

Represent square i by its center p_i and an oriented orthonormal frame
`(e_i,f_i)`, with `f_i` the counterclockwise quarter turn of `e_i`. Its four
vertices are

    p_i + (epsilon e_i + eta f_i)/2,    epsilon,eta in {-1,1}.

Containment in a closed disk centered at zero is equivalent to containment of
these four vertices, by convexity. Pairwise disjoint open interiors are also
a closed condition: the separating-axis theorem expresses each pair's
condition as a finite disjunction of non-strict projection inequalities on
the two axes of each square.

Take a sequence of eight-square packings whose radii tend to the infimum.
There is an elementary finite upper bound, for instance the eight squares of
a 3-by-3 unit grid with its middle square removed. Discarding finitely many
terms bounds every radius by some M. Every center has norm at most M, since
it is the average of its four vertices. Every edge vector lies on the compact
unit circle. A subsequence of all centers and frames therefore converges.
The closed containment and separation conditions survive the limit.

Consequently the infimum R8 is attained. In particular it is legitimate to
study an actual minimizing packing. This does not authorize arbitrary
deformations of that packing; each deformation must still preserve all
containment and disjointness constraints.

## 2. The exact center region and its support function

For a fixed square frame, use local coordinates `(a,b)` for its center. It
fits a disk of radius R exactly when

    (|a|+1/2)^2 + (|b|+1/2)^2 <= R^2.                 (2.1)

Assume `R >= 1/sqrt(2)` and let K_R denote this compact convex region. It is
the intersection of the four disks imposed by the four vertices, rather
than a polygonal outer approximation.

Let F be a force vector, and let

    u = max(|F dot e|, |F dot f|),
    v = min(|F dot e|, |F dot f|),
    rho = sqrt(R^2-1/4).

Thus `u >= v >= 0`. Its exact support on K_R is

    H_R(F) = (rho-1/2) u,                         if u >= 2 rho v,

    H_R(F) = R sqrt(u^2+v^2) - (u+v)/2,          if u <= 2 rho v.    (2.2)

The expressions agree on the common boundary; both give zero for F=0.
The frame dependence of H_R is understood when several differently oriented
squares are present.

### Proof

Sign changes and exchanging coordinates preserve K_R. They reduce the
support calculation to maximizing `u a+v b` with `a,b >= 0`. Put
`X=a+1/2`, `Y=b+1/2`. The problem becomes

    maximize u X+v Y-(u+v)/2,
    subject to X,Y >= 1/2 and X^2+Y^2 <= R^2.

If the unrestricted circle support point

    (X,Y) = R(u,v)/sqrt(u^2+v^2)

has `Y >= 1/2`, it is feasible, since `X >= Y`. Cauchy--Schwarz gives the
second formula. Its feasibility condition is exactly `u <= 2 rho v`.

Otherwise the maximum is at `Y=1/2`, `X=rho`. To see this directly, maximize
over Y the concave function

    u sqrt(R^2-Y^2)+v Y,    1/2 <= Y <= rho.

Its derivative is `v-u Y/sqrt(R^2-Y^2)`. Under `u >= 2 rho v` it is
nonpositive at `Y=1/2` and decreases thereafter. This gives the first
formula. The zero-force case is immediate. The degenerate radius
`R=1/sqrt(2)` has K_R={0} and satisfies the same formulas by inspection.

Thus every force estimate below is an exact whole-domain support calculation.
The branch boundary is a geometric force-cone boundary, not a numerical cut.

### Equality geometry

For nonzero F and `R>1/sqrt(2)`, the maximizing center is unique. In the
second branch its signed local magnitudes are

    a = R u/sqrt(u^2+v^2)-1/2,
    b = R v/sqrt(u^2+v^2)-1/2.

In the first branch they are `a=rho-1/2`, `b=0`, with coordinate order and
signs restored. The first assertion follows from the equality case of
Cauchy--Schwarz; the second from the strictly decreasing derivative above,
apart from its possible zero at the single endpoint.

The second-branch center has a farthest vertex on the circle. In the strict
first branch its two outer vertices lie on the circle. A force-free square
is not constrained by this equality argument, which is essential when the
packing has sliders.

## 3. A separator choice and the forces it induces

Fix all eight frames. For each unordered pair `i<j`, select a unit vector

    n_ij in {+/-e_i, +/-f_i, +/-e_j, +/-f_j}

and impose the directed separating inequality

    n_ij dot (p_j-p_i) >= w_ij,
    w_ij = h_i(n_ij)+h_j(n_ij),                  (3.1)

where the support of the centered unit square is

    h_i(n) = (|n dot e_i|+|n dot f_i|)/2.

For the permitted axes, `w_ij=(1+|cos d|+|sin d|)/2`, where d is the
relative angle of the two frames, up to the harmless quarter turns and sign
changes. In particular `w_ij >= 1`.

This is one branch of the separating-axis disjunction. Every packing belongs
to at least one such branch, but the frames and axes are not being chosen to
match the candidate.

Give the pair inequalities nonnegative weights lambda_ij and define

    F_i = sum_{j<i} lambda_ji n_ji - sum_{j>i} lambda_ij n_ij,
    B   = sum_{i<j} lambda_ij w_ij.                (3.2)

These forces balance globally: `sum_i F_i=0`. Multiplying (3.1) by their
weights and summing cancels the relative centers:

    B <= sum_i F_i dot p_i <= sum_i H_R^i(F_i).   (3.3)

The superscript denotes the support function (2.2) in square i's frame.
Therefore any nonnegative weight choice for which

    B > sum_i H_R^i(F_i)                          (3.4)

excludes every set of centers in the disk for these frames and axes. This is
a rigorous exclusion over the entire center domain, not a local equilibrium
test or a sample of placements.

## 4. The support criterion is also sufficient

For fixed R, frames, and selected axes, the following are equivalent:

1. Centers exist satisfying all containments and all selected separators.
2. For every nonnegative weight vector lambda, inequality (3.3) holds.

Necessity was proved above. Here is a direct convex proof of sufficiency,
including why only nonnegative weights are needed.

Let `K=product_i K_R^i` be the compact convex product of center regions. Let
L take the centers to the vector with coordinates
`n_ij dot (p_j-p_i)`, and write w for the vector of widths. Then

    M = L(K)-w

is compact and convex. The selected constraints are feasible exactly when M
meets the nonnegative orthant C.

Suppose they do not meet. Choose closest points m in M and c in C, and put
`lambda=c-m`. Closest points exist: M is compact, and when minimizing the
distance to it one may restrict C to a sufficiently large compact ball.
Their distance is positive. The elementary first variation of squared
distance along segments in M and C gives

    lambda dot (x-m) <= 0       for every x in M,
    lambda dot (y-c) >= 0       for every y in C.

Taking `y=c+t e_k` proves each coordinate of lambda is nonnegative. Taking
`y=0` and `y=2c` gives `lambda dot c=0`. Consequently

    sup_{x in M} lambda dot x
        <= lambda dot m
         = -|lambda|^2 < 0.

But the left-hand side is exactly

    sum_i H_R^i(F_i) - sum_{i<j} lambda_ij w_ij.

Thus infeasibility produces a strict violation of (3.3), contradicting
condition 2. This proves equivalence without a constraint qualification or
an appeal to an unverified optimization solver.

This removes all sixteen center variables from a fixed orientation and
separator problem. It does not remove the seven relative orientation
variables, select the separating axes, or assert that finitely many sampled
weight vectors suffice.

## 5. A minimizing packing has a nonzero balanced stress

Take an actual radius-minimizing packing, whose existence was proved in
section 1. Select one valid separator for every pair. If the two closed
squares are disjoint, select a separator with strict positive margin; such
an axis exists by applying the separating-axis criterion to the Minkowski
difference of the two polygons. If they touch, a zero-margin separator may
be necessary.

For completeness, the strict assertion follows from the same polygon
geometry as the ordinary separating-axis theorem. The Minkowski sum of the
two centered squares is a convex polygon with outward facet normals among
their four axis directions. Closed-square disjointness places the center
displacement strictly outside that polygon, and hence strictly beyond at
least one of its facet inequalities. A boundary displacement corresponds
to closed-square contact.

For these fixed frames and selected axes the minimum radius is still R8:
the chosen packing is feasible, and any smaller feasible solution would be
a smaller eight-square packing. Take radii `R_k<R8` increasing to R8. They
can be chosen above `1/sqrt(2)`, because a disk of radius `1/sqrt(2)` holds
only one centered unit square and cannot hold two disjoint interiors.

By section 4 each infeasible R_k has weights violating (3.3). Normalize them
by `sum lambda_ij=1` and take a convergent subsequence in that compact
simplex. Continuity of (2.2) gives, at the limiting weights,

    B >= sum_i H_R8^i(F_i).

Feasibility at R8 gives the reverse inequality. Hence there is a nonzero
nonnegative stress satisfying

    B = sum_i F_i dot p_i = sum_i H_R8^i(F_i).    (5.1)

Since each width is at least 1 and the weights sum to 1, B is positive. The
stress is therefore meaningful; it cannot have every F_i zero.

Equality of sums of nonnegative slacks proves both complementary conditions:

* If `lambda_ij>0`, its selected separating inequality is an equality. With
  the separator selection above, the two closed squares actually touch.
* If `F_i` is nonzero, p_i is the unique supporting center in section 2, so
  square i has circle contact with the stated support geometry.

This stress statement needs no assumption that every square touches either
the circle or every neighboring square. Zero weights and zero forces are
allowed.

## 6. Consequences for the contact structure

Make a graph from the edges with positive lambda. The following deductions
are exact necessary conditions for a minimizing packing.

### A square without circle contact cannot be a leaf

If none of square i's vertices reaches the circle, p_i is an interior point
of its center region. A nonzero linear functional cannot maximize at an
interior point, so `F_i=0`. A vertex incident to exactly one positive stress
edge would have a nonzero force, which is impossible.

If such a square has exactly two positive stress edges, their two force
vectors must be equal and opposite. Their normals are therefore parallel
and their weights equal. Thus a two-contact square away from the circle can
transmit a force along a straight projection chain; it cannot turn that
force through a nonzero angle with only two contacts.

### Every nontrivial stress component has at least two nonzero forces

Within a connected component the forces sum to zero. They cannot all vanish:
summing its tight separating inequalities would otherwise give

    0 < sum_edges lambda_ij w_ij = sum_vertices F_i dot p_i = 0.

There cannot be exactly one nonzero force because their sum is zero. Thus
every component containing a positive edge has at least two squares with
nonzero forces, and therefore at least two circle-contact squares.

These statements supply a valid replacement for the false assumption that
all orbital squares can independently be pushed to the circle. The actual
conclusion concerns the support-bearing part of a minimizer and permits
sliding squares and straight internal chains.

## 7. How this advances the sharp proof, and what is missing

The center optimization is now a closed analytic calculation. To exclude a
remaining geometric orientation/separator case below R*, it suffices to
exhibit nonnegative weights with the strict inequality (3.4). To handle
equality, use the support centers and tight separators in (5.1). The weights
may depend on orientations; freezing the candidate weights is not justified.

A successful global proof still needs a geometric restriction on the
orientation/separator patterns and a family of weights or another argument
that covers every survivor. The stress theorem is a necessary structure,
not a proof that the candidate's five-corner cycle is the only possibility.
No unrestricted sharp radius bound is claimed here.

