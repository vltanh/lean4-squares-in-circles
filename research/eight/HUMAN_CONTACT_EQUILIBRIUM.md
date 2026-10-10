# Equilibrium forces at actual square contacts

**Status.** This note proves a normal-multiplier theorem whose contact
forces act at actual common points of the two squares. It strengthens the
necessary conditions in `HUMAN_ROTATIONAL_STRESS.md`; it does not invalidate
or omit the normal-owner derivative proved there. The extra step is an
elementary strict-direction lemma at a parallel edge contact. A useful
consequence is that every bridge of the positive-stress graph transmits a
force along a line through the disk center. In the explicit range
`sqrt(2)+1/2<R<2`, the final theorem excludes every nontrivial component
whose forces are all radial. Every positive-stress component then has a
nonzero moment circulation and contains a cycle.

All statements below apply to a radius-minimizing packing. No candidate
contact graph, numerical optimization, or interval certificate is assumed.

## 1. Contact faces and infinitesimal velocities

Let square `i` have center `p_i`, angle `theta_i`, and vertices `x_i,alpha`.
Write `J(x,y)=(-y,x)`. For an infinitesimal center displacement `a_i` and
angular velocity `omega_i`, the velocity at the material point initially
located at `z` is

```text
V_i(z) = a_i + omega_i J(z-p_i).                         (1)
```

For each pair of touching closed squares `i<j`, select one unit separating
axis `n_ij`, directed from `i` toward `j`. Such an axis is a signed side
normal of at least one of the two squares. The two support faces in this
direction lie on the same line. Let

```text
K_ij = square_i intersection square_j.
```

This is precisely the intersection of those two support faces. It is
either a point or a closed segment. Record its one or two endpoints. For
each recorded point `z`, impose the linear infinitesimal inequality

```text
L_ij(z) := n_ij dot (V_j(z)-V_i(z)) >= 0.                (2)
```

The function `L_ij` is affine on the common support line. Thus its values
at the recorded endpoints control its values everywhere in `K_ij`.

For every vertex on the containing circle `|x_i,alpha|^2=q`, impose

```text
C_i,alpha := 2 x_i,alpha dot V_i(x_i,alpha)-tau <= 0,    (3)
```

where `tau` denotes the proposed change of squared radius.

The chosen contact axes in (2) are data at the initial packing. The
argument below allows an axis to rotate with either owner when both
squares have a side normal in that direction. It does not treat the axis
as a fixed axis during a finite motion.

## 2. Strict contact velocities give an actual feasible motion

**Strict-direction lemma.** If all inequalities (2) are strict and all
active circle inequalities (3) are strict, then the motion

```text
p_i(t) = p_i+t a_i,
theta_i(t) = theta_i+t omega_i,
q(t) = q+t tau
```

is a packing in the disk of squared radius `q(t)` for all sufficiently
small positive `t`.

The circle assertion follows from the strict derivatives at active
vertices and continuity at the remaining vertices. Pairs of disjoint
closed squares have positive distance, so remain disjoint for sufficiently
small motion. It remains to prove the assertion at each touching pair.

Fix its direction `n=n_ij` and omit pair subscripts. If square `i` owns the
axis, let `n(t)` rotate with its angle. The smooth vertex inequalities for
this separating branch are

```text
g_alpha,beta(t)
    = n(t) dot (x_i,alpha(t)-x_j,beta(t)) <= 0.           (4)
```

At an active vertex pair, differentiating gives

```text
g'_alpha,beta(0)
 = omega_i Jn dot (x_i,alpha-x_j,beta)
   +n dot (V_i(x_i,alpha)-V_j(x_j,beta))
 = n dot (V_i(x_j,beta)-V_j(x_j,beta))
 = -L(x_j,beta).                                       (5)
```

The middle equality uses `Jn dot d = -n dot Jd`. In particular it retains
the normal-owner derivative. The same computation when square `j` owns
the axis gives

```text
g'_alpha,beta(0) = -L(x_i,alpha).                       (6)
```

If the square frames are not parallel, the nonowner support face is a
single vertex `z`. Since the closed squares touch, that vertex lies on the
owner support edge and is their common contact point. All active
derivatives in (5) or (6) therefore equal `-L(z)<0`. The corresponding
smooth branch becomes strictly separated.

If both support faces are edges, identify their common line with the real
line, and denote their transverse intervals by `I_i,I_j`. They have
nonempty intersection. For every affine function `L` on this line,

```text
min_(I_i intersection I_j) L
    = max(min_(I_i) L, min_(I_j) L).                    (7)
```

For an increasing affine function, both sides are its value at the larger
of the two left endpoints. For a decreasing function, both sides are its
value at the smaller of the two right endpoints. The constant case is
immediate. This also proves (7) when the intersection is a single point.

The left side of (7) is strictly positive by hypothesis. Consequently at
least one entire face has strictly positive `L`. If this is `I_j`, choose
owner `i` and use (5); if it is `I_i`, choose owner `j` and use (6). In
either case every active vertex inequality for that branch has strictly
negative derivative. Every inactive vertex inequality remains strict by
continuity. This proves a separating branch for all sufficiently small
positive `t`.

There are finitely many pairs and vertices. Taking the smallest of their
positive time thresholds proves the strict-direction lemma simultaneously
for the whole packing.

The owner's choice may depend on the infinitesimal direction. This causes
no difficulty: the lemma needs the existence of a feasible finite motion
for each proposed strict direction, not one smooth branch for all
directions at once.

## 3. Normal multipliers from finite separation

Assume now that the packing minimizes `q`. Collect all linear forms
`C_i,alpha` from (3) and `-L_ij(z)` from (2), so every constraint is written
as a nonpositive form. There is a direction making all of them strictly
negative. Namely, take

```text
a_i=p_i,   omega_i=0,
tau=M=1+2 max_(i,alpha) |x_i,alpha dot p_i|.
```

For the circle forms this is immediate. For a contact form it gives

```text
-L_ij(z) = n_ij dot (p_i-p_j)
         = -h_i(n_ij)-h_j(n_ij) <= -1,                 (8)
```

where `h_i` is the centered square's support function. Each unit square
has half-width at least `1/2` in every unit direction.

There is therefore no direction satisfying all these nonpositive linear
inequalities and `tau<0`. Otherwise adding a sufficiently small positive
multiple of the strict direction above would preserve `tau<0` and make
all constraints strict. Section 2 would produce a packing of smaller
squared radius.

The finite Farkas alternative now supplies nonnegative coefficients

```text
mu_i,alpha >= 0,        for active circle vertices,
lambda_ij,z >= 0,      for the recorded actual contact points,
```

such that the following linear form vanishes identically in every
`a_i,omega_i,tau`:

```text
tau + sum_(i,alpha) mu_i,alpha C_i,alpha
    - sum_(i<j,z) lambda_ij,z L_ij(z) = 0.              (9)
```

For completeness, the alternative used here needs no smoothness of the
linear forms. Form the cone of their coefficient vectors. A finitely
generated cone is closed: each conic combination can be reduced to a
linearly independent subset of generators, and along a convergent
sequence one may select a fixed such subset and pass to its nonnegative
coefficient limits. If the negative objective vector were outside the
cone, its vector toward its nearest point in the cone, with the sign
reversed, would have nonpositive inner product with every generator and
strictly negative objective value. This is exactly the direction just
excluded. Hence the negative objective vector lies in the cone, which is
(9).

The coefficient of the objective is one. No abnormal zero-objective
multiplier remains possible.

## 4. Forces and moments at actual common points

Taking the `tau` coefficient in (9) gives

```text
sum_(i,alpha) mu_i,alpha = 1.                          (10)
```

Each positive circle coefficient belongs to an actual vertex on the
circle. For a contact point `z` of the pair `i<j`, put a force
`-lambda_ij,z n_ij` on square `i`, and the opposite force
`+lambda_ij,z n_ij` on square `j`. Let `F_i` be the sum of these contact
forces on square `i`. The translation coefficients in (9) say

```text
F_i = 2 sum_alpha mu_i,alpha x_i,alpha.                 (11)
```

Thus the contact resultant is balanced by the inward circle reactions
`-2 mu_i,alpha x_i,alpha`. Taking the angular coefficient gives

```text
sum_(contacts on i) (z-p_i) cross f_i,z
    = 2 sum_alpha mu_i,alpha
        (x_i,alpha-p_i) cross x_i,alpha.               (12)
```

Here `a cross b=a_x b_y-a_y b_x`. Adding `p_i cross` the force equation
(11) to (12) yields the particularly simple moment identity

```text
sum_(contacts on i) z cross f_i,z = 0.                 (13)
```

Every circle reaction has zero moment about the origin, which explains
the right side. Equations (11)--(13) are physical force and moment
equilibrium, with all contact forces applied at actual common points.

For one pair, set

```text
Lambda_ij = sum_z lambda_ij,z.
```

When `Lambda_ij>0`, its forces can be combined at the single point

```text
z_ij = (sum_z lambda_ij,z z)/Lambda_ij in K_ij.          (14)
```

The combined forces have the same resultant and moment as the endpoint
forces. Henceforth the **positive-stress graph** has one edge for each
pair with `Lambda_ij>0`, and uses the contact point (14). The actual
contact graph may have additional edges of weight zero.

The usual center-support consequences continue to hold. For example, if
`m_i=sum_alpha mu_i,alpha`, comparison with any other feasible center
`p_i'` in the same frame gives

```text
F_i dot (p_i'-p_i) <= -m_i |p_i'-p_i|^2.               (15)
```

This follows by expanding the active vertex containment inequalities
and summing with the `mu` weights. For `q>1/2` the feasible center region
has nonempty interior, so (15) proves `F_i=0` if and only if `m_i=0`.
For a packing of at least two squares the minimum has `q>1/2`, as shown
in `HUMAN_ROTATIONAL_STRESS.md`. In particular (10) and global force
balance ensure that the stress has nonzero edges and at least two
squares with nonzero force.

## 5. Every stress bridge is a radial contact

**Bridge theorem.** Suppose an edge of the positive-stress graph is a
bridge. Its combined force line passes through the disk center, and the
perpendicular foot of the disk center on its separating line lies in the
actual contact set of the two squares.

Delete the bridge and sum (13) over the vertices of either resulting
component. Each internal contact contributes opposite forces at the same
point, so its moments cancel. The only remaining edge contributes

```text
Lambda_ij z_ij cross n_ij = 0.
```

The edge weight is positive, hence

```text
z_ij cross n_ij = 0,
z_ij = (z_ij dot n_ij) n_ij in K_ij.                   (16)
```

This proves both assertions. It is the combined force point (14) that
is radial; separate endpoint coefficients need not each be radial.

Equivalently, the edge moments `Lambda_ij z_ij cross n_ij` form a
circulation on the positive-stress graph. They vanish on all bridges.
Consequently, if the perpendicular foot from the origin lies outside a
pair's actual contact segment, that pair can carry positive stress only
on an edge belonging to a cycle.

## 6. A stress tree must meet the disk center

**Tree corollary.** Every nontrivial tree component of the positive-stress
graph contains a square that contains the disk center. More generally,
the same conclusion holds for a nontrivial stress component all of whose
combined contact force lines pass through the disk center.

Suppose, to the contrary, that no square in such a component contains
the origin. Their distances to the origin are then strictly positive.
At a radial contact, write its common point as `z=d n` with `d>0`,
choosing the sign of `n` so that `n` points from the origin toward `z`.
Call the square in the half-plane `n dot x>=d` the outer square, and
the other one the inner square. The outer square has distance exactly
`d` from the origin, attained at `z`.

The inner square has distance strictly less than `d`. Indeed, choose
an interior point `x` of it, so `n dot x<d`. The segment points
`z+t(x-z)` lie in that square, and

```text
|z+t(x-z)|^2
    = d^2+2td n dot (x-z)+t^2 |x-z|^2 < d^2
```

for sufficiently small positive `t`. Thus every radial stress edge is
directed from a square of smaller distance to a square of larger
distance. The force on its inner square is `-Lambda n` and the force on
its outer square is `+Lambda n`.

Choose a square `S` of smallest distance `delta>0` in the component.
It must be the inner square on every incident edge. Let `y` be its
nearest point to the origin and put `m=y/delta`. The nearest-point
inequality for a convex set says

```text
m dot x >= delta   for every x in S.                   (17)
```

For any incident contact point `z=d n` this gives
`m dot n>=delta/d>0`. All contact forces on `S` therefore have strictly
negative projection on `m`, and at least one such force is present.
In contrast, its circle resultant in (11) has nonnegative projection
on `m`, since its coefficients are nonnegative and all circle-contact
vertices belong to `S`. This contradicts (11).

This proves the general assertion. In a tree every edge is a bridge,
so section 5 gives its hypothesis automatically.

If the origin lies in exactly one square, every positive-stress tree
component must contain that square; there can therefore be at most one
such component. A stress component containing no square through the
origin necessarily has a cycle with a nonzero contact-moment circulation.

## 7. Below radius two, every radial contact meets a central square

The distance argument has a stronger form when `R<2`.

**Radial-contact lemma.** Suppose two packed unit squares touch at a
point `z=d n`, where `n` is a unit separating normal and `d>0`, with
the inner square in `n dot x<=d` and the outer square in
`n dot x>=d`. If `R<2`, the inner square contains the origin.
Consequently every positive-stress bridge is incident to a square
containing the origin. If its separating line passes through the
origin, both endpoints contain the origin.

Write `rho=sqrt(R^2-1/4)`. The contact point `z` is the nearest point
of the outer square to the origin, so that square has distance `d`.
Its inscribed disk of radius `1/2`, centered at its center `p`, gives

```text
d <= |p|-1/2.
```

The universal center bound from `HUMAN_CYCLE_ANALYSIS.md`, section 7,
gives `|p|<=rho-1/2`. Therefore

```text
d <= rho-1 < 1.                                        (18)
```

Suppose the inner square omitted the origin. In one of its signed
frame directions `e`, its center coordinate is a number `a>1/2`.
Every point of that square then has positive `e` coordinate. In
particular `z dot e>0`, so `n dot e=(z dot e)/d>0`.
Because `z` supports the inner square in direction `n`, it must have
the farthest possible `e` coordinate:

```text
z dot e = a+1/2 > 1.
```

This contradicts `|z|=d<1`, proving the lemma. If the radial contact
point is zero instead, both touching squares contain zero by definition.
Section 5 now proves the bridge assertion.

One further consequence needs no graph classification. In a component
whose combined force lines are all radial, every square that does not
contain the origin is the outer square on every incident edge. Its
contact points all equal its unique nearest point to the origin, and
its incident forces are positive multiples of that same outward unit
normal. Its force resultant is therefore nonzero, so (11) and (15)
make it a circle-contact square. No radial edge can join two squares
that both omit the origin.

## 8. Above sqrt(2)+1/2, every stress component has a cycle

**Nonradial-component theorem.** Assume

```text
sqrt(2)+1/2 < R < 2.                                   (19)
```

Every nontrivial component of the physical positive-stress graph has a
nonzero contact-moment circulation. In particular it contains a cycle,
and no such component is a tree.

We prove that a nontrivial component cannot have all its combined force
lines through the origin. Throughout this proof call a square
**central** if it contains the origin as a point of its closed square.
This permits the origin to lie in its interior, on an edge, or at a
corner. Put

```text
rho = sqrt(R^2-1/4),
a = R-sqrt(2),
b = rho-1.
```

The radius assumptions imply

```text
a>1/2,        1/sqrt(2)<b<1.                            (20)
```

For the stronger lower bound on `b`, observe that
`R^2>9/4+sqrt(2)>7/4+sqrt(2)` and square the positive quantities.

### 8.1. All noncentral squares have one of two radial forms

Suppose a component has only radial combined contact forces. Section 7
makes every noncentral vertex the outer endpoint of each incident edge.
All its effective contact points are therefore its unique nearest point
`d n` to the origin, and all incident forces on it are positive
multiples of the same unit vector `n`. Its nonzero resultant supports
its center in direction `n`.

The support-center proof of the stress-leaf theorem in
`HUMAN_STRESS_TREE_ENDS.md`, section 2, consequently applies even if
this vertex has more than one incident edge. That proof needs only a
parallel outward resultant, a radial inward contact, and the exact
support center; graph degree one is not otherwise used. It gives exactly
two possibilities:

* **Side-normal form:** `n` is a side normal of the noncentral square,
  its center is `(rho-1/2)n`, and its inward contact point is `b n`.
* **Diagonal form:** `n` is a diagonal direction of the noncentral
  square, its center is `(R-1/sqrt(2))n`, and its inward contact point
  is `a n`.

For clarity, the underlying two-branch calculation is short. In signed
and ordered square axes write `n=c e+s f`, `c>=s>=0`. If
`c>=2 rho s`, the supporting center is `(rho-1/2)e`. For `s>0` its
inward vertex has coordinates `(b,-1/2)`, which cannot be radial in the
direction `(c,s)`; hence `s=0`. In the other branch the supporting
center is `Rn-(e+f)/2`, and its inward vertex `Rn-(e+f)` is radial only
when `c=s=1/sqrt(2)`. This proves the two alternatives directly.

In the diagonal form, the contact direction `n` is not a side normal
of the noncentral square. Our selected contact axis must therefore be
a side normal of each of its stress neighbors.

### 8.2. Every outward contact gives a strict projection at its central square

Let a central square C have center `p`, and consider an incident
noncentral square. Let `n` point from C toward it. Their common radial
contact point is `z=d n`, with `d=a` or `d=b` as above. The force on
C from this edge is `-Lambda n`.

We claim

```text
p dot n > 0.                                          (21)
```

If `n` is a side normal of C, its support face has normal coordinate
`p dot n+1/2=d`. Thus `p dot n=d-1/2>0` by (20).

If `n` is not a side normal of C, the noncentral square cannot have the
diagonal form, by the owner restriction in section 8.1. It has the
side-normal form, so `d=b`. The support face of C is a single vertex
`z=p+v`, where the centered vertex satisfies `|v|^2=1/2`. Consequently

```text
p dot n = (b^2+|p|^2-1/2)/(2b) > 0,                   (22)
```

again by (20). This proves (21) for every such contact, without any
assumption that zero lies strictly inside C.

### 8.3. A central square cannot receive positive forces from other central squares

Every central unit square is strictly inside the containing disk: any
point of it is at most its diameter `sqrt(2)` from its point zero,
and `R>sqrt(2)`. Its circle coefficients therefore vanish, and

```text
F_C=0.                                                (23)
```

If zero lies in its open interior, no other packed square can contain
zero, even on its boundary, because interior points of that other square
arbitrarily near zero would lie inside C. So this case has no central
neighbors.

Suppose instead that zero lies on the boundary of C. Let
`m_1,...,m_k`, with `k=1` or `2`, be the inward unit normals of its
side or sides through zero. They are orthogonal when there are two.
For each of them the coordinate interval of C is

```text
0 <= m_j dot x <= 1.
```

At any outward radial contact `z=d n` with a noncentral square,
section 7 gives `0<d<1`. We must have

```text
m_j dot n = 0   for every j.                           (24)
```

A negative value would put `z` outside C. A positive value, since `z`
supports C in direction `n`, would force `m_j dot z=1`, and hence
`d=|z|>=1`. Both are impossible. Thus every force on C from a
noncentral square has zero projection on
`m=m_1+...+m_k`.

On the other hand, a radial contact between two central squares has
effective contact point zero: their separating line passes through
zero, and its only point parallel to its normal is zero itself. The
force on C at that point lies in its inward normal cone. If zero is
in the relative interior of an edge, this force is a positive multiple
of `m_1`. If zero is a corner, it is a nonzero nonnegative combination
of `m_1,m_2`. In either case its projection on `m` is strictly positive.

Projecting (23) onto `m` therefore rules out every positive contact
weight from another central square. This argument applies to each
central square separately; it does not assume that the component has
only one central vertex.

### 8.4. Force balance gives the contradiction

Section 7 says every edge of an all-radial nontrivial component meets
a central square, so such a component has at least one central vertex
C. By section 8.3, C has no incident positive edge to another central
square. Since it belongs to a nontrivial connected component, it has
at least one incident positive edge to a noncentral square.

For all such edges, (21) gives

```text
p dot F_C = -sum_(noncentral neighbors) Lambda (p dot n) < 0.
```

This contradicts (23), proving that an all-radial component cannot
exist in the range (19).

Finally, section 5 shows that the combined edge moments form a
circulation. If every edge moment vanished, all combined force lines
would be radial, which has just been excluded. Every nontrivial
component therefore has a nonzero moment circulation, and hence a
cycle. This proves the theorem.

## 9. What remains for the sharp eight-square bound

The strict-direction lemma permits genuine contact-force arguments at
parallel square contacts. The bridge theorem and tree corollary restrict
the positive-stress graph independently of the actual-contact
minimality lemmas in `HUMAN_CYCLE_ANALYSIS.md` and `HUMAN_STRESS_GRAPH.md`.
In particular zero-weight actual contacts are still allowed, so conclusions
about the two graphs must remain distinct.

Section 8 excludes every positive-stress tree, including one through
squares containing the origin, under the explicit radius hypothesis
`sqrt(2)+1/2<R<2`. Applying that lower radius hypothesis to the unknown
eight-square minimum through the earlier bound `R_8^2>19/5` would still
use the computational certificate in `GLOBAL_LOWER_BOUND.md`. The theorem
here is entirely analytic under its displayed hypothesis; it does not
replace that earlier lower bound by a pen-and-paper proof.

A cycle carrying a nonzero contact moment is now a rigorous starting
point in this radius range. The remaining task is to show that its
geometry forces the two-angle candidate scaffold, or yields an equally
strong projected obstruction. The graph theorem alone does not produce
the five-corner chain or identify the sharp radius. No unrestricted sharp
optimality claim is made here.
