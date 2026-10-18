# Orientation-free dual bound for any fixed directed separator graph

**Theorem.** Fix any finite collection of unit squares
inside a disk of radius R centered at zero.
For selected ordered pairs `i -> j`, suppose
a **fixed world unit normal** `n_ij` is a genuine
separating direction:

    n_ij dot(p_j-p_i) >= h_i(n_ij)+h_j(n_ij).       (1)

The normal may depend on the pair, but is held
fixed when evaluating the following dual.
Assign arbitrary nonnegative scalar weights
`lambda_ij`, not all zero. Put

    v_i=sum_(j -> i) lambda_ji*n_ji
          -sum_(i -> j) lambda_ij*n_ij.           (2)

For a vector v and a frame angle theta write
`h_theta(v)=(|v dot e_theta|+|v dot f_theta|)/2`.
Define the **finite orientation minimum**

    m_i=min_(theta mod pi/2)
       [h_theta(v_i)
        +sum_(edges incident to i)
          lambda_edge*h_theta(n_edge)].           (3)

If the constraints (1) admit a packing, then
`D=sum_i |v_i|>0` and

    R >= (sum_i m_i)/D.                             (4)

Every m_i is computable *exactly* by checking at
most `degree(i)+1` candidate frame angles:
the directions of the nonzero vectors
`v_i` and incident `n_edge`, modulo pi/2.
There is no unverified continuum angle search
left in (3). The edge normals and multipliers
remain arbitrary exact real data.

This bound is valid for **all orientations
of all packed squares**, without assuming
a common frame or identifying actual contacts
with positive stress edges. Its conclusion
is conditional on the specifically chosen
separating-direction inequalities (1):
an arbitrary nonoverlapping pair may select
a different axis, and a global classification
of these choices is not provided here.

## 1. Weighted separator sum

Multiplying (1) by lambda_ij and summing
over all selected edges gives

    sum_i v_i dot p_i >=
        sum_(edges i,j) lambda_ij*
          [h_i(n_ij)+h_j(n_ij)].                   (5)

This identity for v_i is just the
collection of coefficients of every
center p_i: an edge directed i to j
contributes minus lambda*n to i
and plus lambda*n to j. No force
or torque equilibrium is being assumed.

## 2. Disk support closes the center variables

For any vector v_i, circle containment
of the **entire** unit square implies

    v_i dot p_i+h_i(v_i) <= R*|v_i|.               (6)

Indeed the left side is exactly the
greatest projection of its points on v_i,
whereas every point of the disk has
projection at most R|v_i|. This also
holds when v_i=0, with both sides zero.

Combining (5) and the sum of (6) yields

    R*sum_i |v_i| >= sum_i [
      h_i(v_i)+sum_(edges incident to i)
                       lambda_edge*h_i(n_edge)].   (7)

The right side is at least `sum_i m_i`
by definition (3), regardless of the
actual frame angles. Thus (4) follows
provided the denominator D is positive.

If D were zero, every v_i would vanish.
But the right side of (5) is strictly
positive whenever some lambda_edge>0,
because a unit square has
`h_i(n)>=1/2` for every unit n.
Its left side would be zero, a
contradiction. Hence D>0 for any
feasible packing. This also justifies
division in (4).

## 3. The continuum orientation minimum is a finite calculation

For a fixed i, every term in (3)
is a nonnegative multiple of a
centered square support function
in a fixed vector direction.
HUMAN_FINITE_ORIENTATION_DUAL.md
proves that such a weighted sum is
strictly concave between the finitely
many orientations where the square's
side normal aligns with one of the
fixed vectors carrying a positive
weight. Its minimum is at one of
those orientations.

Here there are at most degree(i)+1
such nonzero vectors: v_i and one
normal for each incident weighted edge.
Evaluate the support expression
at each of those angles and take
the least value. This is precisely
m_i. No differentiability assumption
at square-alignment kinks is needed.

## 4. A useful exact dual construction principle

A candidate lower-bound certificate
for an oriented separator pattern
can therefore consist of:

1. A finite set of **fixed directed**
   separating normals n_ij and their
   geometric justification.
2. Explicit nonnegative edge weights
   lambda_ij and the resulting v_i.
3. At every square i, a finite list of
   the at most degree(i)+1 values of
   its weighted support sum, showing
   which is smallest.
4. One final scalar inequality
   `sum_i m_i >= R_target*sum_i |v_i|`.

Those four elementary ingredients,
if actually established, would prove
`R>=R_target` for every packing
using that separator pattern, with
unrestricted square rotations.
They may be checked by hand with
suitable trigonometric identities
or exact algebraic bounds.

An obstruction is that a *frozen*
choice of normals and weights may
be subsharp, and an arbitrary
eight-square packing has not been
proved to use any single prescribed
separator pattern. Optimizing
the weights or claiming the best
branch is achieved at the candidate
without verifying these continuous
and discrete conditions would be
invalid. In particular this theorem
does not establish the unrestricted
n=8 sharp radius R8=R_hat.
