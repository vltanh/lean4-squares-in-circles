# Universal support inequalities for each original square center

This family is valid for one physical unit square whose four corners lie
in the closed disk of squared radius Q=1105/256. It applies separately to
all nine originals of every exact mask. It assumes no chain, angle sign,
pair choice, interval enclosure or registered-original path. Strict disk
containment implies this closed containment premise and is retained by
the caller.

## The physical center lies strictly inside radius91/60

Let c be the original center and let u,v be its orthonormal unit side
vectors. The original corners are c+(epsilon*u+tau*v)/2, independently
for epsilon,tau in {-1,1}. Set r=||c||. Expanding and maximizing the four
corner norms gives

    max_corner ||corner||² = r² + 1/2 + |c·u| + |c·v|.

Because u,v are an orthonormal basis, (c·u)²+(c·v)²=r². Both sides in
|c·u|+|c·v| >= r are nonnegative, and squaring gives this inequality
from the nonnegative cross term 2|c·u||c·v|. Hence containment implies

    r² + r + 1/2 <= 1105/256.

Put rho=91/60. Exact rational arithmetic yields

    rho² + rho + 1/2 - 1105/256 = 31/57600 > 0.

If r>=rho, then
(r²+r)-(rho²+rho)=(r-rho)(r+rho+1)>=0, contradicting the preceding
inequality. Thus r<rho, even when the original corners use closed-Q
containment. In particular r<=rho is a universal necessary enclosure.
This derivation concerns the full Euclidean norm, not only the two
coordinate bounds. No old geometry initializer is imported.

## Exact supporting rows

For any rational direction (a,b), Cauchy–Schwarz gives

    a*x_i+b*y_i <= sqrt(a²+b²)*||c_i||
                  <= (91/60)*sqrt(a²+b²).

Every rational s satisfying both

    s >= 0,       3600*s² >= 8281*(a²+b²)

therefore gives the necessary row a*x_i+b*y_i<=s. Directions may have
either sign, and either or both coordinates may vanish. If a=b=0, the
row is 0<=s and is valid exactly under the nonnegative-RHS requirement.
The family does not claim the support bound is attained by a physical
closed-Q packing: the closed radius-rho disk is a safe relaxation of the
strictly smaller physical center region.

The existing original-column layout has center coordinates at2*i and
2*i+1 for i=0,...,8. The row uses only those two columns, with no new
variables. It is valid on all parent and child domains and on all shared
faces. It transports no child interval, selected SAT predicate, local
orientation or normalization.

## Producer, independent checker and discovery boundary

`physical_center_disk_rows.row(i,a,b)` computes the exact rational
radicand rho²(a²+b²), then rounds its square root upward on a dyadic
grid using integer square root and an exact final comparison. It prints
the index, direction and rational RHS in the row name. This algorithm is
only one way of constructing a valid row.

`independent_physical_center_disk_rows.verify_literal(row)` does not
import or repeat the producer's square-root algorithm. It decodes the
name, reconstructs the two original coefficients, checks the original
index, checks RHS identity and nonnegativity, and checks the exact squared
support inequality above. Any supplied row passing these checks follows
from the physical derivation, regardless of how its rational RHS was
selected. Its caller must still retain the original physical square and
its four closed-Q corner bounds, as the current nine-square callers do.

`physical_center_disk_separation.violated_parameters(point)` only
suggests radial directions from a floating LP point. Its grid, threshold,
violation ranking and potential omissions have no mathematical authority.
No solver or old context is imported by the universal row modules. An
eventual runtime must append rows without changing prior indices and
dispatch every weighted occurrence to the independent literal checker.

The separate exact controls check the corner expansion, radial bound,
dyadic upper construction, rational circle boundaries, zero/sign cases
and damaged literals. Rational centers at radiusrho are support-lemma
boundary controls, not alleged feasible square packings. Saved LP points
are untrusted relaxation diagnostics, not physical configurations.

This packet introduces no root normalization and excludes no original or
mask by itself. Source review and an actual weighted-use replay are
required before adopting the family in a proof continuation. Existing
workers, completed records and prior proof sources remain unchanged.
