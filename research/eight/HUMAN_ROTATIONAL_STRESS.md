# Normal contact multipliers and exact angle stationarity

**Status.** This is an analytical necessary-condition theorem for a packing
that minimizes the containing radius. It adds angle stationarity to the
center-force reduction in `BALANCED_SEPARATOR_REDUCTION.md`. Normal
multiplier existence is proved below by an explicit strict direction and a
finite-dimensional separation argument; no rank assumption, numerical solver,
or presumed candidate contact graph is used.

The selected separating normal rotates with its owner square. Its derivative
is retained in every angle equation. The result is not presented as a
physical contact-moment formula with that derivative silently omitted.

## 1. A smooth branch using actual vertex inequalities

Use squared radius `q` as the objective. Square `i` has center `p_i`, angle
`theta_i`, and frame

```text
e_i=(cos(theta_i),sin(theta_i)),   f_i=J e_i,
J(x,y)=(-y,x).
```

Let `A={(-1,-1),(-1,1),(1,-1),(1,1)}` be the four vertex signs. For
`alpha=(epsilon,eta) in A`, define

```text
v_i,alpha = (epsilon e_i+eta f_i)/2,
x_i,alpha = p_i+v_i,alpha.
```

At a minimizing packing, choose one valid directed separating axis for each
pair `i<j`. Record its **owner**

```text
k_ij in {i,j}
```

and which of the four signed axes of that owner it uses. In nearby
configurations keep that choice: `n_ij` rotates with `theta_(k_ij)`, so

```text
partial n_ij / partial theta_k
    = 1_(k=k_ij) J n_ij.                                (1)
```

The corresponding branch consists of the following smooth inequalities:

```text
c_i,alpha = |x_i,alpha|^2-q <= 0,                       (2)

g_ij,alpha,beta
    = n_ij dot (x_i,alpha-x_j,beta) <= 0,
      for every alpha,beta in A and every i<j.           (3)
```

For a pair, all sixteen inequalities (3) say that every vertex of square `i`
has projection at most that of every vertex of square `j`. By convexity this
separates the whole squares. Conversely, a valid chosen separating axis
satisfies all sixteen. Thus every configuration feasible for the branch is
a packing, and the given packing minimizes `q` on this branch as well.

The vertex formulation avoids absolute values of angle functions. It is
smooth even when two square frames are parallel or the maximizing support
vertex changes. Its finite list consists of the actual square vertices,
not a discretization of positions or orientations.

For later contact conclusions, make the following choice whenever possible:
if the two closed squares are disjoint, select an axis with a strictly
positive projection gap. Such an axis exists by the polygon separating-axis
argument recorded in section 5 of `BALANCED_SEPARATOR_REDUCTION.md`. Then
all sixteen inequalities for that pair are strict. Pairs whose closed
squares touch may require a zero projection gap.

## 2. An explicit direction makes every active constraint strict

All quantities in this section are evaluated at the minimizing packing.
Consider the infinitesimal variation

```text
delta p_i = p_i,
delta theta_i = 0,
delta q = M,
```

where, for example,

```text
M = 1+2 max_(i,alpha) |x_i,alpha dot p_i|.
```

For containment its directional derivative is

```text
D c_i,alpha = 2 x_i,alpha dot p_i-M < 0.                 (4)
```

For every separator constraint its derivative is

```text
D g_ij,alpha,beta = n_ij dot (p_i-p_j) <= -1.            (5)
```

To justify the last bound, a valid selected separation implies

```text
n_ij dot (p_j-p_i)
    >= h_i(n_ij)+h_j(n_ij) >= 1,
```

where `h_i(n)=(|n dot e_i|+|n dot f_i|)/2` is the half-width of the square.
Every unit direction has half-width at least `1/2` in each unit square. The
angles are fixed in this variation, so there is no derivative of the normal
or the vertex offsets in (5).

In particular every active constraint has strictly negative derivative in
this explicit direction. This establishes the needed constraint
qualification directly, including at parallel contacts and multiple-vertex
circle contacts.

## 3. Normal multiplier existence, proved by finite separation

For clarity, we supply the finite-dimensional argument rather than assuming
that an optimizer returns valid multipliers.

Let `z` collect all centers, angles, and `q`; let `b` be the coordinate vector
such that `b dot delta z=delta q`. At the minimizing point let `a_r` be the
gradient of active constraint `r` from (2) or (3). Section 2 gives a vector
`d_0` with

```text
a_r dot d_0 < 0       for every active r.                (6)
```

There is no vector `d` satisfying

```text
a_r dot d <= 0       for every active r,
b dot d < 0.                                           (7)
```

Indeed, for sufficiently small positive `epsilon`, the vector
`d+epsilon d_0` would have strictly negative derivative for every active
constraint, while still decreasing `q`. Smoothness then makes all active
constraints strict along `z+t(d+epsilon d_0)` for sufficiently small positive
`t`. Every inactive constraint remains strict by continuity. This gives a
feasible packing with smaller `q`, a contradiction.

It follows that `-b` lies in the cone generated by the active gradients:

```text
b+sum_r t_r a_r=0,       t_r>=0.                         (8)
```

Here is a direct proof of that last implication. A cone generated by finitely
many vectors is closed. To see this, any conic combination can be reduced to
a linearly independent subset of its generators: if its positive-coefficient
support is dependent, subtract a multiple of a linear dependence until one
positive coefficient becomes zero, and repeat. Along a convergent sequence
of conic combinations one may therefore pass to a subsequence using one
fixed linearly independent subset. Its coefficients converge, by continuity
of the inverse on the span, and their limits remain nonnegative.

If `-b` were outside that closed convex cone, take its closest point `u` in
the cone and put `d=-b-u`. Projection onto a convex cone gives

```text
d dot a_r <= 0       for all generators a_r,
d dot u = 0,
d dot (-b)=|d|^2 > 0.
```

For completeness, the projection inequality is
`d dot (v-u)<=0` for every point `v` of the cone. Taking `v=0,2u` proves
`d dot u=0`, and then taking any generator gives the first inequality.
Thus `d` would satisfy (7), a contradiction. This proves (8), the required
finite Farkas alternative.

Write the multipliers in (8) as

```text
mu_i,alpha >= 0        for containment constraints,
lambda_ij,alpha,beta >= 0   for separator constraints,
```

and set inactive-constraint multipliers to zero. We have proved stationarity
of the Lagrangian

```text
q + sum_(i,alpha) mu_i,alpha c_i,alpha
  + sum_(i<j,alpha,beta) lambda_ij,alpha,beta g_ij,alpha,beta,
```

together with complementary slackness. The coefficient of the objective is
exactly one. There is no abnormal zero-objective-multiplier exception.

## 4. Normalization, contact activity, and center forces

Taking the derivative with respect to `q` gives the normalization

```text
sum_(i,alpha) mu_i,alpha = 1.                            (9)
```

Complementary slackness gives

```text
mu_i,alpha > 0  ==>  |x_i,alpha|^2=q,

lambda_ij,alpha,beta > 0
    ==> n_ij dot (x_i,alpha-x_j,beta)=0.                 (10)
```

Collapse the vertex-pair weights for a pair into

```text
Lambda_ij = sum_(alpha,beta) lambda_ij,alpha,beta,
```

and define the balanced center forces as in the earlier reduction:

```text
F_i = sum_(j<i) Lambda_ji n_ji
      -sum_(j>i) Lambda_ij n_ij.
```

The center derivative of the Lagrangian yields

```text
F_i = 2 sum_alpha mu_i,alpha x_i,alpha.                  (11)
```

For a positive `Lambda_ij`, at least one of the corresponding vertex-pair
constraints is active. In a feasible branch, equality of such a pair of
vertex projections forces equality of the extremal projections as well:
the selected center separation is exactly the sum of the two half-widths.
By the strict-separator selection in section 1, the two closed squares then
actually touch. No positive multiplier is assigned to a pair with separated
closed squares.

Since the forces sum to zero, (9) and (11) also give

```text
sum_(i,alpha) mu_i,alpha x_i,alpha = 0,
sum_(i,alpha) mu_i,alpha = 1.                            (12)
```

Thus the disk center is a convex combination of the circle-contact vertices
that carry positive multipliers. This conclusion concerns actual vertices
and does not require every square to touch the circle.

## 5. The full angle equation, including the normal-owner derivative

The vertex derivative is

```text
partial v_i,alpha / partial theta_i = J v_i,alpha.
```

For a selected pair and vertex pair, the derivative of (3) with respect to
the angle of square `k` is exactly

```text
partial g_ij,alpha,beta / partial theta_k
  = 1_(k=k_ij) (J n_ij) dot (x_i,alpha-x_j,beta)
    +1_(k=i) n_ij dot J v_i,alpha
    -1_(k=j) n_ij dot J v_j,beta.                       (13)
```

Therefore every square `k` satisfies

```text
0 = 2 sum_alpha mu_k,alpha x_k,alpha dot J v_k,alpha

    +sum_(i<j,alpha,beta) lambda_ij,alpha,beta *
      [ 1_(k=k_ij) (J n_ij) dot (x_i,alpha-x_j,beta)
       +1_(k=i) n_ij dot J v_i,alpha
       -1_(k=j) n_ij dot J v_j,beta ].                  (14)
```

The first term is the angle derivative of the active circle constraints.
The remaining three terms account respectively for rotation of the selected
normal, rotation of the source vertex, and rotation of the target vertex.
Formula (14) is valid at parallel square frames, since the smooth vertex
inequalities were used throughout.

It would be incorrect to discard the normal-owner term merely because its
constraint is active. Activity says
`n_ij dot (x_i,alpha-x_j,beta)=0`; it does not say
`(J n_ij) dot (x_i,alpha-x_j,beta)=0`. Two active support vertices may have
the same normal projection and different tangential positions. This occurs,
for example, when one square's edge supports a vertex of the other square.

A physical interpretation in terms of forces applied at common contact
points would require a separate reduction of the vertex-pair multipliers.
Equation (14) is the exact algebraic stationarity statement without that
additional claim.

### Rotation consistency check

Under a common infinitesimal rotation, take
`delta p_i=J p_i` and `delta theta_i=1` for every square. Then every vertex
has derivative `J x_i,alpha` and every selected normal has derivative
`J n_ij`. Each circle constraint has derivative zero, while each separator
constraint has derivative

```text
(J n_ij) dot (x_i,alpha-x_j,beta)
  +n_ij dot J(x_i,alpha-x_j,beta) = 0.
```

This agrees with rotation invariance and with the center and angle equations
above. Omitting the normal-owner term would remove the first term of this
identity and would not in general preserve that invariance.

## 6. Compatibility with the exact center-support reduction

Let `m_i=sum_alpha mu_i,alpha`. For fixed frames, let `p_i'` be any other
center at which square `i` fits in the same disk. If `mu_i,alpha>0`, expanding
the squared containment difference gives

```text
2 x_i,alpha dot (p_i'-p_i)+|p_i'-p_i|^2 <= 0.
```

Multiplying by the corresponding weights and summing, then using (11), yields

```text
F_i dot (p_i'-p_i) <= -m_i |p_i'-p_i|^2.                (15)
```

In particular `p_i` supports the force `F_i` on the exact center region.
This recovers the support equality used in `BALANCED_SEPARATOR_REDUCTION.md`
and gives uniqueness whenever `m_i>0`.

For a packing of at least two unit squares, its minimum squared radius is
strictly greater than `1/2`: at radius `1/sqrt(2)` the only possible unit-square
center is the origin, so two open squares would overlap. At any larger
radius, the admissible center region has nonempty interior. Consequently
(15) implies

```text
F_i=0  iff  m_i=0.                                     (16)
```

The reverse implication follows directly from (11). For the forward one, if
`F_i=0` and `m_i>0`, equation (15) would force every admissible center to equal
`p_i`, contradicting the nonempty interior of the center region.

Thus a force-free square carries no positive circle multiplier, even if it
happens to touch the circle. Conversely, every square with a nonzero force
has a circle-contact vertex with positive multiplier. Zero weights and the
sliding squares seen in the candidate family remain fully allowed.

Since the masses `m_i` sum to one, at least one force is nonzero. Global
balance then requires at least two nonzero forces, and at least two squares
carrying positive circle multipliers. In particular the contact weights
`Lambda_ij` cannot all vanish.

## 7. Scope for the eight-square proof

These results apply to an actual minimizing eight-square packing, whose
existence was proved in `BALANCED_SEPARATOR_REDUCTION.md`, and to whichever
separating-axis branch it occupies. The branch is not selected to imitate
the candidate.

They supply positive boundary-vertex weights summing to one, actual contact
weights, exact center-force balance, and the complete angle equations (14).
Together with the corner and disk-cap capacity lemmas, they give additional
necessary conditions for the remaining orientation and contact patterns.

The missing task is still to show that these conditions force the projected
five-corner chain, or imply a sharp radius obstruction for all alternatives.
No such implication, global classification, or unrestricted sharp lower bound
is asserted here. No Lean proof has been attempted.
