# Independent review of the simultaneous singleton-cycle rotations

Date: October 30, 2026. Reviewer: common_certificate continuation.

Target:
`SIMULTANEOUS_ROTATIONS_EXCLUDE_SINGLETON_CYCLES_WITH_PHYSICALLY_ISOLATED_MOVING_STARS_2026_10_30.md`

Final target SHA-256:
`d3688215df65fbfa810b0a357119cf0a5787151b53f773607e53c4d2032c0997`.

**Verdict: ACCEPT at the complete printed scope.** I read the whole
manuscript, reconstructed every contact and circle constraint, checked
the zero-coefficient case separately, and verified the directed-graph,
open-rate, canonical-stationarity and original-channel arguments. The
final pin differs from the first reviewed version only by the closing
display delimiter after equation (8.2), and by updating the direct-input
hash of the preceding rotation source after its own closing-display
repair. Both repaired displays were reread. No mathematical statement,
hypothesis or proof step changed.

The theorem handles both transmitter widths and loaded side ownership
without changing an original selected normal, application, mean, load,
or degree. Its moving-body physical-neighbor and singleton hypotheses
are essential and are retained throughout. The explicit nonparallel
and proper-concurrence assumptions remain part of the reviewed theorem.
No whole original coarse parent or unrestricted C7 family is declared
closed by this review.

## 1. Exact domain and contact classification

The comparison packing is the original minimum of radius and then
`Phi=sum |c_i|^2`, including every actual square. The entire selected
positive component is a simple cycle with at least two loaded vertices
and a nonempty unloaded run. Thus every cycle member has its true full
positive pair degree two. The radius interval is exactly

    sqrt(2)<R<3/sqrt(2).

The closed project window lies strictly inside it. Proper concurrence
is an explicit hypothesis over this larger interval; its standard
project-window caller is not silently extended to a larger interval.

Every loaded body has one physical circle corner with positive actual
coefficient. Its original proper force lines give `q=tau*z` inside
the square, `0<tau<=1`, and `p-q=alpha*n` with `alpha>=0` at each
positive contact. Side transmitters stay fixed. Loaded bodies and
diagonal transmitters comprise the moving set, and each has exactly
its two positive cycle neighbors as actual physical neighbors. All
its physical contacts are singletons.

The strict original separator convention at a vertex/vertex singleton
is printed explicitly. For a vertex in the relative interior of the
other body's side, the separator strictly exposes that vertex: a
non-strict normal there would make an adjacent edge collinear with
the owner's side, and the interior point would yield a positive
shared segment. Thus the source's two contact categories exhaust
every contact involving a moving body. In particular, an actual
corner cannot be treated as a side owner with a non-strict selected
normal merely to evade the strict point-normal convention.

## 2. Physical circle corners and diagonal-transmitter pivots

The fact that two contained squares cannot share a point of the
containing circle is valid. Such a point must be a corner of each
square, by strict convexity of the disk. If its inward adjacent edge
directions are `-u,-v`, containment of the adjacent vertices gives
`z.u>=1/2` and `z.v>=1/2`. Hence the short inward radial segment
from z lies in the open interior of each square. Sharing z would
therefore give overlapping open interiors.

A diagonal transmitter's actual ports are `c+/-sigma*d`, where
`sigma=1/sqrt(2)`. If it is circle-clear, rotation about its actual
center gives positive port coefficients sigma and preserves containment
locally. If it touches the circle, neither contact port can be a circle
corner by the preceding argument. Choose the perpendicular sign so
its boundary corner is `z=c+sigma*e`, and write `c=x*d+y*e`.
Comparison with both port norms gives `y>|x|`. Consequently the
opposite remaining corner is also strictly interior, so this is the
only physical circle corner. A second zero-weight corner is not lost.

The proposed pivot obeys

    q=(y/(y+sigma))*z,
    q-c=-(sigma*x/(y+sigma))*d.

Since `|x|<y<y+sigma`, it lies strictly inside the actual transmission
diagonal. Both signed port coefficients are positive, and it is a
positive inward multiple of the unique boundary corner. These are
exactly the properties later used in contact and circle feasibility.
Choosing this motion center changes no original stress datum.

## 3. Complete audit of the zero vertex-coefficient branch

This is the crucial degenerate case. Suppose a moving loaded body
supplies a vertex with `p=q`, so its normal-line coefficient is zero.
In its own side coordinates write its unique circle corner as `(a,b)`
and its square as `[a-1,a] x [b-1,b]`. Unique maximal corner norm
gives `a,b>1/2`. Because q is a positive multiple of `(a,b)`, it
cannot be either adjacent vertex. It cannot be the circle corner,
which is unshareable. The opposite vertex is proportional to `(a,b)`
only when `a=b=R/sqrt(2)`.

Thus q is the radial inner vertex. At a different second application,
the proper force normal would point along the nonnegative-coordinate
vector from q to that application. If both coordinates are positive,
the normal exposes the forbidden circle corner. If exactly one is
positive, the corresponding actual support is an outer side, at
coordinate `a=R/sqrt(2)`. Any neighboring unit square beyond this
side has width at least one in that axis and therefore has a point
of projection at least `a+1>R`. The inequality follows from
`R<2+sqrt(2)`, which is weaker than the assumed upper radius bound.

Both original applications must therefore equal q. Their normals
strictly expose q in this body by the contact classification, and
these are all its actual physical contacts. Rotating this one square
alone about q keeps the contact vertex fixed in both strict supporting
halfplanes. Its unique circle corner moves inward under the exact
radial-pivot formula; its other corners and all noncontacting squares
have positive local clearance.

Here `c=(R-sigma)*e`, `q=(R-sqrt(2))*e`, and

    det(q,c)=0,
    q.(c-q)=(R-sqrt(2))*sigma>0.

Its exact change in Phi is negative for every sufficiently small
nonzero rotation. This contradicts the original canonical minimum.
Thus every moving vertex supplier has a strictly positive coefficient.
The proof covers both coincident applications, imposes no extra
neighbor-incidence condition, and does not need a separate triangle
exception. Zero coefficients on an owned side remain permitted.

## 4. Ownership graph and exact two-sided contact motion

The source directs each ownership edge from its vertex supplier to
its side owner, retaining only moving endpoints. It is a subgraph
of the original simple cycle. A fixed side transmitter breaks that
underlying cycle into paths. If no side transmitter exists, an unloaded
diagonal transmitter supplies vertices at both incident contacts and
has no incoming ownership arrow. A directed cycle would have to be
the entire original cycle, which is then impossible. The ownership
graph is therefore acyclic in both cases.

For an arrow `i->j`, the original common point satisfies

    p-q_i=alpha*n,
    p-q_j=-beta*n,
    alpha>0, beta>=0.

Finite reverse topological order supplies positive rates satisfying

    a_i>(1+sqrt(1+beta/alpha))*a_j.

The inequalities are strict, so the allowed vectors form a nonempty
open set in the full space of moving-body rates. This is stronger
than merely finding one direction of motion. A fixed side transmitter
is always a side owner in this singleton domain, and its zero rate
does not introduce an opposite rate requirement.

I independently recomputed all three contact formulas. For a strict
moving vertex against a fixed side, the original supporting value
changes by `alpha*(cos(a_i*theta)-1)<=0`. For two moving strict
vertices, subtracting their supporting values gives the sum of two
such nonpositive terms. Their vertex labels remain strictly exposed
for small rotations.

For a moving vertex against a moving side owner, use the side owner's
actually rotating normal. The full support difference is

    F(theta)=-(alpha+beta)*cos(a_j*theta)
             +alpha*cos((a_i-a_j)*theta)+beta.

It has value and first derivative zero at zero, with

    F''(0)=-alpha*a_i^2+2*alpha*a_i*a_j+beta*a_j^2<0.

The rate inequality is exactly the positive-root condition for this
strict sign. Hence F is negative for every sufficiently small nonzero
theta of either sign. The supplier's vertex remains uniquely exposed
in the rotating normal, and the owner's plane is its actual supporting
side. This establishes separation of the entire rotated squares.
The case `beta=0` is fully included; there is no division by beta.

## 5. Feasibility is for every original square

Every actual contact of every moving body is among the preceding
cycle contacts, by the explicit physical-neighbor premise. Every
originally disjoint closed pair has positive distance and remains
disjoint locally. Fixed pairs and any extra contacts at fixed side
transmitters are unchanged. Finiteness gives a common sufficiently
small neighborhood for all pair constraints at each selected rate
vector.

Every moving body that physically touches the circle has exactly one
such corner z and the chosen `q=tau*z`. The exact formula is

    |q+R_(a_i*theta)(z-q)|^2
      =R^2-2*tau*(1-tau)*R^2*(1-cos(a_i*theta))<=R^2.

All other corners are strictly inside and remain so. Circle-clear
diagonal bodies also remain contained by continuity. Convexity then
contains every entire square. This proves a real feasible full-packing
curve for both signs of theta; no persistence of the original stress
or contact graph in the competing packing is assumed.

## 6. Why the open cone forces individual radial centers

At each moving body put `B_i=det(q_i,c_i)`. Differentiation of the
actual center motion gives

    Phi'(0)=-2*sum_i a_i*B_i.

Canonical minimality and two-sided feasibility set this equal to zero
for every rate vector in the nonempty open set. A linear functional
vanishing on such a set has all coefficients zero. Thus every B_i
vanishes individually. This conclusion does not require or claim
independent signs for the individual second derivatives.

At a loaded body q is a positive multiple of its unique circle corner
z, so c and z are collinear. The corner-center distance is sigma.
The alternatives placing c beyond z or opposite its radial direction
contradict disk containment or `R>sigma`. Hence exactly

    z=R*e,
    c=(R-sigma)*e.

This alignment follows even when a loaded body owns one or both sides
at its positive contacts. No assumption that all its contacts expose
its own vertices has been inserted.

## 7. Uniform original-port bound and the final contradiction

For a radial loaded square, outer-side applications again fail the
width-at-least-one argument, and the circle corner cannot be shared.
The inner radial vertex cannot be a positive application: Section 3
rules out zero coefficient, while a positive coefficient there forces
its normal to be inward radial. The full force equation then makes
the other normal radial too, contrary to the explicit nonparallel
hypothesis. This uses the true original two-force equation.

Only inner-side applications and lateral vertices remain. The former
have exact projection `p.n=1-R/sqrt(2)`. At a lateral vertex,
write `q=(r+delta)*e` with `r=R-sigma`. Proper inclusion and strict
vertex exposure give `-sigma<delta<sigma`. Its projection is

    g(delta)=(sigma^2-r*delta)/sqrt(delta^2+sigma^2).

I checked

    g'(delta)=-sigma^2*(r+delta)/(delta^2+sigma^2)^(3/2)<0,

using `r+delta>=R-sqrt(2)>0`. Therefore the lateral projection is
strictly greater than `g(sigma)=1-R/sqrt(2)`. No unjustified
restriction `delta>=0` is used. Every original loaded positive port
therefore satisfies

    p.n>=1-R/sqrt(2)>-1/2.

A maximal nonempty unloaded run has distinct loaded endpoints. Full
force balance and original torque preserve one signed normal and
telescope the actual applications to `p_B-p_A=L*n`, with every
internal width at least one and hence `L>=1`. The endpoint outward
normals are `n,-n`. Their two preceding projection bounds yield

    L=-p_B.(-n)-p_A.n<=sqrt(2)*R-2<1,

the stated contradiction. Both side and diagonal widths are retained;
the proof does not suppress any original positive branch or edge.

## 8. Pins, callers and unchanged limitations

The four direct source hashes printed in the target match the local
files. The complete canonical-minimum, previous rotation, and local
proper-concurrence inputs were already read and independently audited
in the earlier rotation review. I also read the full parallel-transmission
source; the exact normal-channel steps consumed here are reconstructed
directly in both the target and this review.

The theorem excludes every stated full simple-cycle feature in its
radius interval, and therefore all stated four-, five-, and six-load
short-C7 assignments throughout the closed project window. It does
not distinguish the side/diagonal placements. All nine actual squares
remain in the canonical comparison. Additional squares may touch
fixed side transmitters; an additional contact at a moving body cannot
be ignored. Positive shared segments incident to moving bodies and
second physical circle corners at loaded bodies remain outside the
theorem, even when their extra coefficients would be zero.

The reviewed theorem keeps nonparallelism and proper concurrence
explicit. Any separately proved project-window lemma supplying those
premises belongs to its caller and does not alter this pinned source.
There is no claim that every original open parent satisfies the
remaining physical-neighbor or singleton premises.

No numerical pose search, mesh, computational packing certificate,
Lean/Lake invocation, CI, inventory mutation or publication was used
for this review. No original fine or coarse flag changes here.
