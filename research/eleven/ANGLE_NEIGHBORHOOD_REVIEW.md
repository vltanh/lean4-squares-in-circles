# Independent review of the quantitative group-angle terminal

Review outcome: **PASS**. The theorem provides an explicit lower bound for
the prescribed fourteen-halfspace contact class when the two half-angle
parameters are within `1/2000` of the exact candidate parameters. It allows
arbitrary centers within that class. It does not prove that arbitrary
packings satisfy those halfspaces or have the three prescribed orientation
groups, and it does not establish global optimality.

Direct replay of `check_angle_neighborhood.py` passed the root enclosure,
four positive stress solves, all second-derivative bounds, and the strict
Taylor comparison. The following mathematical and source details were
independently checked.

## Weak dual and unloaded squares

The signs in the completed-square identity agree with the nonnegative disk
and separator slacks. The objective coefficient is exactly one because the
q row of `J^T w=e_q+(s/40)e_k` gives `sum(lambda)=1`. The dual consequently
has the displayed constant `1/2`, with no dependence on unprescribed center
coordinates.

Only labels 1, 4, and 8 have zero disk totals. Their force balances are
preserved identically throughout the angle rectangle by the stated weight
profile. In particular, the balance at square 8 is exactly

    B*ex = mu78*u_alpha - mu89*v_beta.

Resolving the vertical coordinate gives
`mu89=mu78*sin(alpha)/cos(beta)`, and then the horizontal coordinate gives
`mu78=B*cos(beta)/cos(beta-alpha)`. The implemented two formulas follow.
At labels 1 and 4, the equalities `mu01=mu14=mu45` and `mu34=mu48` cancel
the vertical and horizontal forces separately. These equalities are exact
consequences of the center rows at the root, not consequences of overlapping
intervals. The omitted square-1 horizontal row is identically zero.

The region checks give `0<alpha<beta<pi/2` and
`cos(beta-alpha)>9/10`. Therefore the modified weights remain nonnegative.
The other weights and all positive disk totals retain the certified strict
positive lower bounds. No unbalanced zero-disk-weight center is omitted
from a square completion.

## Exact value, signed slope, and interval Hessian

The reconstructed Jacobian differentiates the active slacks with centers
held fixed. It uses the same ten corners and fourteen signed owner axes as
the established stress. Their support formulas are valid throughout the
ordered angle region. Outward rational elimination encloses the exact
solutions of the four perturbed linear systems and proves invertibility
through its nonzero pivots.

At the root, the adjusted profile equals the exact solved weights. Every
positively weighted constraint is tight and the center derivatives vanish,
so each dual equals `qc`. Differentiating its minimized quadratic gives
`grad D=-(s/40)e_k`: derivatives of the varying weights multiply zero slacks,
and the remaining angular term is the negative prescribed Jacobian row.
This checks the sign as well as the fact that the other angular derivative
is exactly zero. Neither equality is inferred from an interval containing
zero.

The two-variable derivative class correctly applies the product Hessian
rule and the reciprocal rule
`2 f_i f_j/f^3-f_ij/f^2`. Its scalar interval operations round outward to
the denominator-`10^30` grid. Treating the exact stress constants as
independent enclosing intervals can enlarge the Hessian enclosure but
cannot invalidate it. The evaluated rectangle contains the exact root and
every segment to a point at maximum coordinate displacement at most
`1/2000`. All four Hessian entries for all four duals are bounded in absolute
value by 20.

Selecting a maximum-displacement coordinate and the opposite signed stress
gives the positive linear term `d/40`. The integral Taylor remainder is
bounded below by

    -(20/2)(|delta_ta|+|delta_tb|)^2 >= -40*d^2.

Thus `q>=qc+(1/40-40*d)*d`, strictly above `qc` for
`0<d<=1/2000`. At zero displacement the previously established fixed-frame
equality theorem supplies the physical slider family. The explicit theorem
and manuscript retain all contact-class assumptions needed for that final
step.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `check_angle_neighborhood.py` | `810bebab0fb72b3af171383176e90f9068359ed126f0cb7d9f6b9ea71ae9773d` |
| `QUANTITATIVE_GROUP_ANGLE_NEIGHBORHOOD.md` | `8bf2e460e2ed602630eff874cc2a5c276319c54feb0631735a017f4c454df7bf` |

The checker imports the previously reviewed root, contact-family, and
fixed-frame interval-solver certificates. This review adds no claim that
those supporting computations have been checked by a Lean kernel.
