# Finite orientation reduction for weighted square support widths

**Theorem (arbitrary finitely many fixed normals).**
Fix nonzero vectors `n_1,...,n_m` in the plane and
nonnegative real weights `lambda_1,...,lambda_m`,
with at least one positive weight. Consider a
unit square of free frame angle theta and
its *centered* support function

    h_theta(n)=
      (|n dot e_theta|+|n dot f_theta|)/2,
    e_theta=(cos theta,sin theta),
    f_theta=(-sin theta,cos theta).

Then the function

    W(theta)=sum_(j=1)^m lambda_j*h_theta(n_j)      (1)

achieves its global minimum **at a frame angle
where at least one square side normal is
parallel to one of the vectors n_j with
positive weight**.

More precisely, the minimizing angles modulo
the square's quarter-turn symmetry belong
to the finite set

    theta congruent arg(n_j) mod (pi/2),
    for j with lambda_j>0.                           (2)

On every open interval between consecutive
distinct angles in this finite set, W is
smooth and strictly concave. A minimizer
on that interval cannot be interior.

The theorem applies equally to weights
depending on external parameters, provided
the normals are held **fixed while optimizing
the square's orientation**. It is not a
theorem about simultaneous changes of
contact normals with a rotating square.

## Hand proof

For any fixed nonzero vector n with
polar representation `n=|n|(cos phi,sin phi)`,
the support width is exactly

    h_theta(n)=|n|/2 *
      (|cos(phi-theta)|+|sin(phi-theta)|).          (3)

The only possible nonsmooth orientations
of (3) occur when one of the two
trigonometric arguments vanishes.
Modulo pi/2 these are exactly
`theta=phi`.

On any open interval missing these
angles, each sine and cosine has
constant sign. Removing the absolute
values therefore expresses h_theta(n)
as a fixed linear combination of
`cos(theta)` and `sin(theta)`, so

    d^2/dtheta^2 h_theta(n)=-h_theta(n).            (4)

After summing with the nonnegative
weights in (1), we obtain

    W''(theta)=-W(theta)<0                          (5)

throughout any interval missing all
breakpoints. The strict sign holds
because at least one weighted support
function is positive for every angle.

A strictly concave function on a
closed interval takes its minimum
at one of its endpoints. Thus the
minimum over each interval between
consecutive breakpoints is attained
at a breakpoint. The support width
and W are continuous at breakpoints,
and they are periodic with period
pi/2. Finitely many closed intervals
cover one full period, proving that
a global minimum exists and is attained
at one of the finite angles (2). QED.

## Exact comparison formula at breakpoints

For an arbitrary test angle `phi_k`
from (2), the score is the explicit
finite quantity

    W(phi_k)=1/2 sum_j lambda_j*|n_j|*
       (|cos(phi_j-phi_k)|+|sin(phi_j-phi_k)|).     (6)

Hence, once the fixed directions
and weights are known, global
orientation minimization reduces
exactly to comparing at most m
numbers of the elementary form (6).
There is no continuous angle
optimization left.

For a fixed linear stress or separator
dual, circle-support reactions may
also produce weighted support terms:
one simply includes their fixed
radial directions among the n_j.
This is precisely the mechanism used
in HUMAN_ANCHORED_END_RIGIDITY.md
to reduce its entire orientation
circle to the four actual directions
of the three relevant normals.

## Scope limits important for n=8

A packing may have multiple separating
axes available for a contacting pair.
If the selected axis is owned by the
square currently being rotated,
its world direction moves with
theta. Formula (1) then does **not**
retain fixed normals and this
theorem does not apply without
separately justifying that reduction.

Even with fixed normals, the
radius objective of a square is the
maximum of **Euclidean norms of its
four vertices**, not a fixed linear
combination of support widths.
A direction-dependent circle support
lower bound may be optimized by (1),
but it need not capture the full disk
containment constraint away from
its equality angle.

Consequently this theorem is a
complete analytic **inner subproblem**
for support-force duals. It does not
establish a global contact graph,
the two aligned end squares, the six
directed separators, or R8>=Rhat.
