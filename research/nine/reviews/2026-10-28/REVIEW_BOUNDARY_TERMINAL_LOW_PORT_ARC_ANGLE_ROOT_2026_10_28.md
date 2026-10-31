# Root review of the full low-port terminal-center angle theorem

Date: October 28, 2026 UTC. Reviewer: root continuation.

**Disposition: PASS for the entire force-free local theorem.** Actual
pocket routing remains a separate premise. This source earns no whole
original gate credit by itself.

The entire source read and checked is

    BOUNDARY_TERMINAL_CENTER_LOW_PORT_ARC_ANGLE_BOUND.md
    SHA256 d94502aed4091098a1fa23801284a734f9f42989f130a5f0d9b0f464bb7497e6.

Root did not supply this proof. The author reported the intended scalar
result while developing the shared-slider caller; this review checks
the complete written proof independently of that intended application.

## 1. Exact physical scope and angle lift

The radius assumptions are 2<R<=sqrt(1105/256). E is an actual
contained physical boundary unit, and P=(-A,-h) is an actual point
of that same unit, with 0<A<=1 and |h|<=27/100. No force, normal,
owner, degree, circle coefficient, or graph hypothesis is used.

The actual center radius r exceeds 129/100, because its distance
from a physical circle corner is 1/sqrt(2)<71/100. Its distance
from P is at most the same unit circumradius. If C_x>=0, replacing
P's x coordinate by zero can only reduce the center-point distance;
the reverse triangle inequality then gives distance>102/100, a
contradiction. Thus C_x<0 and the specified angle lift is unique.

For C_y>=0 the claimed inequality follows immediately with the
correct lift. For C_y<0 the actual expression C=(-r*c,-r*s) has
c,s>0. The actual point distance gives r*s<=h+1/sqrt(2)<98/100,
hence s<98/129<4/5 and c>3/5. The remaining phi>beta case also
has s>1/4. These bounds do not presume a contact normal at P.

## 2. Continuous squared-distance proof

With rho=5/4 and beta=atan(5/16), the exact trigonometric values
are correctly stated. The two strict estimates used in the proof have
positive rational squared reserves

    625/16-281*(37/100)^2=371/625,
    36/25-400/281=116/7025.

Under the alleged reverse angular inequality, the horizontal
distance r*c-A is strictly greater than
(83/50)*c-(6/5)*s, which is itself greater than 9/250.
The vertical difference r*s-h is strictly greater than
(129/100)*s-27/100, which exceeds 21/400. Thus both lower
bounds are positive before squaring; no invalid squaring of a
negative estimate occurs.

I independently expanded the sum of squares minus 1/2. It equals

    4657/2000+(697/2000)*s^2
       -(498/125)*c*s-(3483/5000)*s.

Using c*s<=1/2 gives the stated scalar f(s). Its derivative is
negative throughout the enlarged closed interval [0,4/5], with
upper bound -695/5000, and its endpoint value is 113/50000>0.
This contradicts the true point-to-center bound 1/2 and proves
the angular implication over the entire continuous domain. No
angle sample or pose exclusion table is used.

## 3. Exact final inequality and caller limit

Because theta_A=pi/2+asin(A/rho) and theta=pi+phi in the only
nontrivial case, the proved strict comparison

    A>rho*sin(phi-beta)

is exactly theta-beta-theta_A<pi/2. The inverse sine is used
on its increasing branch, with 0<phi-beta<pi/2 and 0<A/rho<1.
All closed h endpoints and A=1 are retained. Horizontal reflection
gives the stated reversed-angle consequence without changing E.

The theorem concerns the actual terminal center and actual point P.
It neither proves that a proposed occupied crosscut has the required
winding nor that each completing unit's entire connected inner arc
lies in the claimed free interval. A full capacity caller must supply
both facts and an actual occupied centered arc in E. The source
states these requirements explicitly and does not claim a whole
graph/load exclusion.

The result therefore passes root review at its stated full scope.
A separate full independent review is required for adoption. No
original normal, mean, equation, physical mask, or unit was changed;
no Lean compilation, CI, workflow, or merge was performed.
