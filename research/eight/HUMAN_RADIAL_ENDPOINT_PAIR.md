# Exact radial endpoint elimination for one outer-square pair

## Theorem (pair-only existential equivalence)

Fix a disk squared radius q such that
`q>=3`, two different center directions `u_i,u_j`,
and two unit-square side frames `(e_i,f_i)`, `(e_j,f_j)`.
Restrict each square center to its assigned positive ray with
norm **at least one**. For the fixed frames, let `m_i,m_j`
be the largest allowed center norms under disk containment.

Then the following statements are equivalent:

1. There exist radii `1<=r_i<=m_i` and
   `1<=r_j<=m_j` for which the two squares have disjoint
   open interiors.
2. At least one of the four endpoint pairs

       (r_i,r_j) in {(1,1),(1,m_j),(m_i,1),(m_i,m_j)}

   gives two contained squares with disjoint open interiors.

This is an exact analytical reduction over the **entire** radial
rectangle. It does not assume actual contact and retains arbitrary
frame orientations. It is not a claim that a packing of seven squares
can be radially moved to independent pair-optimal endpoints:
different pairs may demand incompatible endpoints.

## 1. Exact allowed radial intervals

For a square centered at `r*u`, with `|u|=1` and frame
`(e,f)`, put

    L(u,e,f)=|u dot e|+|u dot f|,    1<=L<=sqrt(2).

The farthest squared vertex norm is exactly

    r^2+L*r+1/2.

The allowed positive radius interval is `0<=r<=m`,
where `m>0` is the unique positive root of

    m^2+L*m+1/2=q.

Since `q>=3>3/2+sqrt(2)`, every orientation permits
`m>1`; hence the outer-center interval `[1,m]` is
nonempty. Circle containment holds for each endpoint.

## 2. Preserve one signed separating axis

For the two squares of center displacement

    d=r_j*u_j-r_i*u_i,

the separating-axis theorem gives disjoint open interiors if
and only if at least one of the **eight signed directions**

    n in {+e_i,-e_i,+f_i,-f_i,+e_j,-e_j,+f_j,-f_j}

satisfies

    n dot d >= h_i(n)+h_j(n),                          (1)

where the centered square support function is

    h_i(n)=(|n dot e_i|+|n dot f_i|)/2.

For any *fixed* signed axis n, the left side of (1) minus
its right side is an **affine function** of (r_i,r_j):

    G_n(r_i,r_j)=r_j*(n dot u_j)-r_i*(n dot u_i)
                 -h_i(n)-h_j(n).                       (2)

An affine function on a closed rectangle attains its
maximum at a corner. More explicitly, each radius can
independently be chosen at the endpoint that maximizes
its own coefficient. Thus if `G_n>=0` at some interior
radius pair, then `G_n>=0` at one of the four endpoint
pairs. All endpoints satisfy circle containment by
section 1, and (1) at that endpoint witnesses disjoint
open interiors. This proves (1) implies (2) in the
theorem. The reverse implication is immediate.

Notice that **the chosen signed axis remains the same**
in this argument. There is no need to differentiate
the nondifferentiable maximum of all SAT margins or
to decide which separating branch dominates at an
interior point. Boundary contacts are covered by
the non-strict inequality (1).

## 3. Explicit signed-support forms for the seven-outer ring

Rotate the first center direction to zero and let
the second be `delta` counterclockwise, `0<delta<pi`.
Choose square frames with relative center-ray tilts
`alpha,beta in [-pi/4,pi/4]`.
The absolute first-axis angles are then
`alpha` and `delta+beta`.
Let `gamma=delta+beta-alpha` and

    H=(1+|cos(gamma)|+|sin(gamma)|)/2.

The four **unsigned** axis margins in the
separating-axis theorem are precisely

    |r_j*cos(delta-alpha)-r_i*cos(alpha)|-H,
    |r_j*sin(delta-alpha)+r_i*sin(alpha)|-H,
    |r_j*cos(beta)-r_i*cos(delta+beta)|-H,
    |-r_j*sin(beta)+r_i*sin(delta+beta)|-H.             (3)

The pair is interior-disjoint precisely when at least
one margin in (3) is nonnegative. In a fixed angular and
frame state, the existential question over two radial
variables therefore reduces to checking (3) at the
four corners `(1,1),(1,m_j),(m_i,1),(m_i,m_j)`.
This is a finite disjunction of 16 unsigned, or 32
signed, elementary trigonometric inequalities in
`delta,alpha,beta`, with no center-radius variables.

## 4. Relation to a genuine global certificate

Suppose one wants to prove a necessary directed
pair-angle inequality for **all** disjoint outer squares
at a fixed q. The endpoint theorem permits testing
that inequality over only the four radius corners,
for every allowed angular/frame state. It cannot be
used to *construct* a new seven-square packing from
the independently chosen pair endpoints.

The known radialization obstruction concerns exactly
that invalid simultaneous operation; it does not
invalidate the pairwise existential equivalence here.
The remaining mathematical work is to establish
sharp whole-domain inequalities across the 16
branches and combine them over the odd seven-cycle
or to use a different global structural theorem.
Neither (1)--(3) implies R8>=Rhat by itself.
