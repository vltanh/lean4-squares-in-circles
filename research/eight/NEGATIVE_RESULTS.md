# Negative directions and safeguards in the eight-square search

These entries distinguish disproved reductions from merely unsuccessful numerical searches. They are not evidence that the original eight-square problem has no analytical proof.

## 1. Seven exterior squares alone do not determine the eight-square optimum

A tempting continuation of the central-square certificate was: discard the unique central square and prove that seven exterior squares already require Cantrell's radius. This is false.

`verify_seven_exterior_counterexample.py` gives exact rational centers and rational orthonormal frames for SEVEN interior-disjoint unit squares, all avoiding the origin even in their closed squares, inside radius

    197865/100000 = 1.97865.

This is below the reconstructed eight-square candidate radius 1.9787708653.... All 28 corners and 21 pair separators are checked by rational arithmetic. The smallest exterior-center coordinate exceeds 1/2 by 1/20000000, so the example is not using a square through the origin as a limiting loophole.

Conclusion: the central square's separation constraints MUST be retained in any sharp seven-ring argument. The central-square existence theorem remains useful, but the exterior ring cannot be optimized independently of its central obstacle.

The example was discovered by finite state sampling and cyclic difference-constraint optimization, then replaced by an exact rational verification. Only the latter establishes this counterexample.

## 2. An adjacent-pair-only cyclic budget loses non-neighbor obstructions

A discretized seven-state cyclic search found adjacent separation costs totaling less than 2*pi while some nonadjacent pair could not be disjoint at the proposed angular distance. Thus a proof built only from independently optimized adjacent edges needs an additional argument that it controls all non-neighbor pairs. Cyclic order alone is not that argument.

The exact seven-exterior counterexample above goes further: even retaining every exterior pair does not recover the missing central obstacle.

## 3. One frozen candidate stress has the wrong tilt curvature

For the five-corner construction polygon let the consecutive normals be

    n1=(0,1), n2=(-1,0), n3=(0,-1),
    n4=(sin t,-cos t), n5=(cos t,sin t),

and projected edge requirements be 2,3,2,1+sin t,2+cos t.
For nonnegative multipliers lambda_i, summing these inequalities and using
circle support gives the conditional lower bound

    R >= B(t)/D(t),
    B=2 lambda1+3 lambda2+2 lambda3+(1+sin t)lambda4+(2+cos t)lambda5,
    D=sum_i |lambda_(i-1)n_(i-1)-lambda_i n_i|.

The numerically equilibrated candidate multipliers, normalized by lambda5=1,
are approximately (0.64493422,0.99098197,1.07451183,1.04552232,1).
Freezing these multipliers gives a LOCAL MAXIMUM of B/D at the candidate tilt,
not a minimum (numerical second derivative about -0.2608). For instance the
frozen bound is about 1.96946 at t=0 and 1.97816 at t=0.2.

This is numerical diagnostic evidence, not a certified derivative theorem.
It rules out presenting this unmodified numerical stress as an angle-uniform
optimality proof. A tilt-dependent dual family or an additional tilt penalty
is required. Also, the five-corner inequalities are only conditional until a
global structural theorem produces that polygon from arbitrary packings.

## 4. Uniform occupied arcs on one auxiliary circle are too weak

At the candidate squared radius q, an exterior square with equal sorted
coordinates a=u=sqrt(q/2)-1/2 occupies on the unit circle an arc of width

    pi/2 - 2 asin(a-1/2),

approximately 0.7495, less than pi/4. Thus an argument assigning every exterior
square an occupied unit-circle arc of width at least pi/4 is false. Increasing
the auxiliary radius helps this distant state but can shrink the occupied arc
of a state near (a,u)=(1/2,0). The successful certificate instead uses a marker
whose separation is not simply the length of its occupied arc.

## 5. Numerical optimization is not a lower-bound certificate

A twelve-start SLSQP experiment around the candidate and from ring layouts
returned several apparent radii below the record with negative separation
margins. Those are INFEASIBLE outputs, not improved packings. For example,
one output had radius 1.97876629 but constraint residual about -8.85e-6.
Feasible converged runs near the candidate gave radii about 1.97877100 and
1.97884475; the experiment does not prove these are the only local minima.

The pair-state discretization initially missed u=1/2 and produced an
optimistically strong fitted label. Adding that special boundary state changed
the numerical optimum. Only full-domain exact verification, not a state grid,
can validate the marker theorem.

## Current consequence

Keep the unique central square and its actual separating axes throughout the
next reduction. The proven exterior marker budget gives a useful 2,2,2,1
quadrant occupancy pattern, but it does not force common orientations, full
boundary contact, or the candidate's five-corner polygon by itself.
