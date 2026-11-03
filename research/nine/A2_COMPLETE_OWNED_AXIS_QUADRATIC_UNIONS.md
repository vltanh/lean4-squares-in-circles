# Complete owned-axis union inequalities in the shared original moments

Fix an unchanged original parent and a physical pair i<j. All center, frame,
slope, Cartesian-difference, and diagonal-difference intervals in this note are
already certified on that entire parent. Put d=c_j-c_i and

    c=alpha_i alpha_j+beta_i beta_j,
    s=alpha_i beta_j-beta_i alpha_j.

Canonical original angles lie in [-pi/4,pi/4], so c>=0. For every choice of
owner o in {i,j}, axis e in {u_o,v_o}, and sign sigma in {-1,1}, let
P_k=sigma d·e. The complete physical separating-axis theorem says at least one
of these eight alternatives satisfies

    2P_k >= 1+c+|s|.

Thus each physical separating alternative satisfies, for both epsilon=-1,+1,

    T_(k,epsilon)=2P_k-c-epsilon s >= 1.          (1)

All expressions P,c,s,T are quadratic polynomials in the same 54 original
coordinates and frame variables. The eight alternatives are used only as a
complete disjunction; none is selected as an additional parent assumption.

## Exact projection ranges using the original unit frame

The certified slope t=beta_o/alpha_o belongs to [a,b] and alpha_o>0. At a fixed
displacement vertex, an owned-axis projection has the form

    f(t)=(X+tY)/sqrt(1+t^2).

For u_o use (X,Y)=(d_x,d_y); for v_o use (X,Y)=(d_y,-d_x).
Its derivative is (Y-tX)/(1+t^2)^(3/2). Hence both extrema on the closed slope
interval occur at an endpoint or at t=Y/X when X!=0 and that slope is inside
the interval. When X=0 the endpoint cases suffice, including the constant-zero
case.

For each fixed t the expression is affine in the center displacement, so its
extrema on a displacement rectangle occur at vertices. Checking the finite
endpoint/critical-slope set at all four vertices therefore gives a rigorous
range on the entire rectangle, with no angle split or omitted arc. A certified
diagonal rectangle for d_x+d_y and d_x-d_y is mapped to its four Cartesian
vertices by d_x=(S+T)/2, d_y=(S-T)/2. The physical displacement lies in both
rectangles; the intersection of their projection ranges remains valid.

All square roots are bounded outward by exact integer arithmetic. For rational
v>=0 and scale 2^40, let n=floor(sqrt(v)*scale). Integer square root of
floor(v*scale^2) computes this n exactly. Then n/scale is a lower bound and
(n+1)/scale is an upper bound, with equality handled exactly. Dividing a signed
rational numerator by these positive endpoints yields rational outward bounds
for every candidate value f(t).

## Relative cosine and sine intervals

The extreme relative angles are theta_j^lo-theta_i^hi and
theta_j^hi-theta_i^lo. They lie in [-pi/2,pi/2]. Sine is increasing there, and
cosine has its maximum at zero and its minimum at one of the interval endpoints.
At slopes x,y the exact values are

    cos(theta_j-theta_i)=(1+xy)/sqrt((1+x^2)(1+y^2)),
    sin(theta_j-theta_i)=(y-x)/sqrt((1+x^2)(1+y^2)).

The same rational square-root enclosure computes outward intervals, intersected
with 0<=c<=1 and -1<=s<=1. These are valid quadratic bounds on shared frame
products, not independent relative-frame choices.

## Safe alternative elimination and complete-union rows

Because c^2+s^2=1 and c>=0, c+|s|>=1. Every separating alternative consequently
has P_k>=1. An alternative is impossible if its certified upper bound on P_k
is strictly below1, or if its certified upper bound on either T_(k,epsilon) is
strictly below1. Retain every other alternative. Equality is retained.

Let K be the remaining set. If K is empty, all eight physical alternatives are
excluded and the unchanged parent is contradictory. Otherwise, for either
epsilon choose certified lower bounds L_k on T_(k,epsilon). If every L_k<1,
then every summand below is nonnegative, and at least one is at least1 by (1):

    sum_(k in K) (T_(k,epsilon)-L_k)/(1-L_k) >= 1.   (2)

Thus (2) is one unconditional quadratic inequality on the entire original
parent. The implementation skips this particular row if a lower bound is
already at least1; it makes no invalid division. The same argument with P_k
and its lower bounds yields a weaker unit-support union inequality.

Bounds on each P_k,c,s are themselves unconditional quadratic rows and can be
installed in the same moment lift. They also justify every bound L_k in (2).

## Two remaining owners of one signed axis

Suppose the only surviving alternatives are the same signed axis owned by i and
by j, and a certified bound gives |P_i-P_j|<=delta. Whichever owner separates,
both projections are at least (1+c+|s|)/2-delta. Therefore for both owners and
both epsilon signs,

    2P_o-c-epsilon s >= 1-2delta.

The difference bound is computed at displacement vertices. At each vertex,
the two original angles vary independently over their own certified intervals;
subtracting their exact projection ranges gives a valid difference interval.
Again intersect the Cartesian and diagonal rectangle bounds. This retains each
original physical orientation and covers both possible separating owners.

## Proof credit

Every row in this note is necessary on the unchanged original parent, and uses
the complete signed owned-axis cover. No row alone closes a cell. Closure still
requires independent reconstruction of the guarded finite calculations and a
positive exact terminal certificate after the entire inherited prefix has been
replayed. Numerical moment points and exhausted bounded runs remain OPEN.
