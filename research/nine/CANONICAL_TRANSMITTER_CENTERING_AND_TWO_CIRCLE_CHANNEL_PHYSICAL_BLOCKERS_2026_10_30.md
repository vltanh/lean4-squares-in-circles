# Canonical transmitter centering and physical blockers at every two-circle channel

Date: October 30, 2026. Author: common-certificate continuation.

**Status: complete proposed uniform hand implications, awaiting separate
full-source review.** These statements keep all physical circle corners,
including zero-weight ones, and all original side applications. They
identify a necessary additional actual contact, not a missing positive
force and not a reason to change a transmitter's true positive degree.

The side result uses the existing `(R,Phi)` minimum. A final finite
integer tie-break of that same minimum gives the diagonal result.
Together they route every two-circle-endpoint singleton channel into
an explicit physical-blocker alternative at its original transmitter.

## 1. Original objects and a legitimate last canonical tie-break

Keep all original unit squares in the same origin-centered containing
disk. At the minimum radius choose a packing minimizing

    Phi=sum_i |c_i|^2,

as in the existing compact canonical-minimum source. A genuine unloaded
transmitter has true full positive body-pair degree two, zero selected
circle load, original force-and-torque balance, and its two original
applications on opposite supports. Its physical circle mask need not
be empty. The original two-force theorem gives either a side-normal
width-one transmission or a diagonal transmission of width `sqrt(2)`.

Where explicitly stated below, refine the choice once more: among
packings with these same minimum values of R and Phi, minimize

    N_phys=number of unordered pairs of actual squares that intersect.

This is a well-defined final tie-break. The preceding minimizer set is
nonempty, and the attained values of `N_phys` form a nonempty subset of
the finite integer set `{0,...,binomial(n,2)}`. Its smallest attained
value is attained by definition. No additional minimization of a
continuous function on this potentially nonclosed subset is needed.

This refinement preserves every conclusion whose only canonical premise
was the original `(R,Phi)` minimum. It is made before selecting the
current physical certificate. A competing packing need not retain that
certificate: canonical comparison is among all actual packings.

## 2. A side transmitter with only two actual neighbors is centered transversely

Let U be an original unloaded side transmitter. Let n be the signed
transmission direction and put `t=Jn`. Its actual square is

    U=c+[-1/2,1/2]*n+[-1/2,1/2]*t.

Write `c=x*n+y*t`. Its two original positive neighbors lie beyond
the fixed opposite support lines

    n.p=x-1/2, n.p=x+1/2.

Assume these two bodies are all its actual physical neighbors. Their
positive intersections may be shared segments, side endpoints, or
singletons; all original aggregate means are retained.

**Theorem 2.1 (canonical transverse centering).** At the original
`(R,Phi)` minimum one has

    y=c.t=0.                                             (1)

*Proof.* If `y!=0`, translate U a small positive distance in direction
`-sign(y)*t`. Its n-support lines are unchanged, so the same two
original separating halfplanes still separate it from its two actual
neighbors. This conclusion concerns the whole squares and does not
require an application mean to remain a contact point in the competing
packing.

Every other square is compact and disjoint from U, so its original
distance is positive and it remains disjoint for a sufficiently small
translation. There are finitely many such pairs.

The exact maximum squared norm of a corner of U is

    (|x|+1/2)^2+(|y|+1/2)^2.

The proposed translation reduces `|y|` and therefore preserves
containment, including all initially active physical circle corners.
It also strictly decreases `|c|^2=x^2+y^2`. All other centers stay
fixed. This contradicts the original Phi minimum. QED.

The actual force and torque equations fix the two original application
points or means in the form

    p_-=c-n/2+s*t, p_+=c+n/2+s*t,
    -1/2<=s<=1/2.

Thus (1) gives an immediate exact line-height bound:

    the distance of the original channel line from zero is |s|<=1/2.
                                                               (2)

The proof never deletes a zero-weight actual contact. It instead proves
that if `y!=0`, at least one such additional physical neighbor must be
present to prevent the decreasing translation. It does not assign that
neighbor a new positive coefficient.

## 3. A diagonal transmitter with only two actual neighbors can lose both contacts

Let U be an unloaded diagonal transmitter, with original contacts

    p_+=c+sigma*d, p_-=c-sigma*d,
    sigma=1/sqrt(2),

and original outward normals `d,-d`. They strictly expose those
opposite vertices. Assume again that these are its only two actual
physical neighbors. Any contact where U strictly exposes a vertex is
necessarily a singleton, since every intersection point must be on
that uniquely exposed face.

**Theorem 3.1 (diagonal physical blocker).** At the refined canonical
choice of Section 1, such a U cannot exist. Every original unloaded
diagonal transmitter therefore has an additional actual physical
neighbor.

*Proof if U is circle-clear.* Rotate U about its actual center c.
At either original normal its support value decreases exactly by

    sigma*(1-cos(theta))>0

for small nonzero theta. Both formerly positive contacts become
strictly separated. Every noncontact persists locally, and all corners
remain in the disk by their original positive clearance. Phi is exactly
unchanged because the center does not move. All other squares are fixed.
Thus R and Phi retain their minimum values while `N_phys` decreases
by exactly two, contradicting its chosen minimum.

*Proof if U physically touches the circle.* No containing-circle point
can belong to two contained unit squares: its short inward radial
segment belongs to the open interior of each. Consequently neither
contact port can lie on the circle. Choose `e` perpendicular to d so
one of the remaining vertices is the actual boundary corner

    z=c+sigma*e, c=x*d+y*e.

Its norm strictly exceeds both port norms. Subtracting their squared
norms gives `y>|x|>=0`. The opposite nonport vertex is strictly inside
as well; z is the unique physical circle corner, even though its
selected coefficient at this unloaded body is zero.

Set

    q=(y/(y+sigma))*z,
    q-c=-(sigma*x/(y+sigma))*d.                            (3)

This q lies strictly inside the actual transmission diagonal, so
both ports satisfy `p-q=alpha*n` with `alpha>0`. A small rotation
about q decreases both fixed-normal supports. Since `q=tau*z` with
`0<tau<1`, its circle corner stays inside by

    |q+Rot_theta(z-q)|^2
      =R^2-2*tau*(1-tau)*R^2*(1-cos(theta))<=R^2.

All other corners and noncontacts have positive local clearance.
This proves a full two-sided feasible one-body motion at the original
`(R,Phi)` minimum. Its Phi derivative is `-2*det(q,c)`, so that
determinant is zero. In the oriented `(d,e)` frame, (3) gives

    det(q,c)=-sigma*x*y/(y+sigma).

Because `y>0`, it follows that `x=0` and hence `q=c`. The same
rotation is now a center rotation, so Phi is exactly constant.
It strictly opens both actual contacts as before and preserves
containment. Thus it again decreases `N_phys` by exactly two, a
contradiction. QED.

The argument uses both physical-mask alternatives of U and does not
replace a physical zero-weight circle corner by a clearance assumption.
It needs no restriction on the graph degrees, masks, loads or other
forces of U's two original neighbors.

## 4. A side channel incident to a two-circle endpoint has height greater than one half

Work now throughout the closed project interval

    79/40<=R<=sqrt(1105)/16,
    a=sqrt(R^2-1/4), d=a-1.

Let X--U--Y be an original actual channel. U is a true unloaded side
transmitter; X has two physical circle corners; Y is physically
circle-touching. Neither endpoint's degree or individual circle weights
are restricted. Retain the original strict point-normal convention.

Use the actual radial frame

    X=[d,d+1]*e+[-1/2,1/2]*f, f=Je.

Let p be its unchanged application and g its original outward normal
toward U. The exact width-one channel gives the application on Y as
`p+g`. We reproduce the complete support cover to isolate every
physical assumption.

The outer circle vertices cannot be shared. The outer radial support
`d+1` cannot have a unit neighbor: that neighbor's width at least one
would give a point of projection greater than R. Therefore a strict
right-vertex normal and the positive radial axis are excluded.

For `g=-e`, the original application is `p=d*e+h*f`, `|h|<=1/2`.
Then the Y application is `(d-1)*e+h*f`. The exact project bounds give

    |d-1|<1/10, R-sqrt(2)>14/25,
    |p+g|^2<1/100+1/4=13/50<(14/25)^2.

Every point of the actual boundary square Y has norm at least
`R-sqrt(2)`, by its circle corner and its diameter. This excludes
the entire negative radial-axis case, including all original means.

For `g=+f` or `g=-f`, the original support value is `p.g=1/2`.
The Y application has g-projection `3/2`, and Y lies entirely beyond
that support. Its width at least one gives a point of projection at
least `5/2>R`, also impossible.

Every remaining normal and application is consequently

    p=d*e+f/2, g=-c*e+s*f,
    c,s>0, c^2+s^2=1,

or its reflected lower-vertex version. Thus the distance from zero
of the original force line through p is exactly

    |det(p,g)|=d*s+c/2
               >(s+c)/2>=1/2.                           (4)

Here `d>9/10>1/2` and `s>0` give strictness. This is a statement
about the unchanged original channel, with no normal or contact mean
chosen afterward. It uses no concurrence at the two-circle body and
retains either zero endpoint of its two physical corner coefficients.

## 5. The complete two-circle channel blocker implication

Combine (2) and (4).

**Theorem 5.1 (side-channel blocker at the original Phi minimum).**
Every original width-one channel X--U--Y with X physically two-circle
and Y physically boundary requires an additional actual physical
neighbor of U besides X and Y. It is impossible for U to have exactly
its two positive channel neighbors as physical neighbors.

The extra pair has zero selected coefficient because U's true full
positive degree is already two. This conclusion changes neither its
positive graph nor its actual degrees; it exhibits a required physical
constraint omitted by any proposed two-neighbor motion.

**Corollary 5.2 (both widths, with the last tie-break).** At the refined
canonical choice of Section 1, every original singleton transmitter
channel from a physically two-circle endpoint to a physical boundary
endpoint has such an additional physical neighbor. For width one use
Theorem 5.1; for width `sqrt(2)` use Theorem 3.1. Here "singleton
transmitter" means one internal body, not a claim that every endpoint
intersection is a point.

In every no-long C7 with four, five or six positive loads, each unloaded
vertex is one such genuine internal transmitter between its two loaded,
hence physically boundary, neighbors. Therefore every transmitter
incident to a two-circle loaded body has an additional actual physical
contact in the refined canonical packing, across all width assignments,
original means and individual circle weights.

With four loads and three isolated unloaded vertices, every loaded
vertex has an unloaded neighbor: there is exactly one loaded-loaded
edge in the whole cycle. Consequently every two-circle loaded mask
in that entire four-load domain forces at least one such transmitter
blocker. With five or six loads, a two-circle body inside a consecutive
loaded run need not be incident to a transmitter; that case is not
silently included in this corollary.

No assertion is made that all required blockers are distinct, that they
must be one of the two completion squares, or that they can be summed
as independent capacity charges. They may be zero-weight contacts to
other cycle bodies. Their full geometry remains a necessary separate
join. No whole original C7 parent is closed by this implication alone.

### 5.3 Complete clean four- and five-load C7 families

There is nevertheless a full family exclusion when the blockers are
absent, including every loaded physical circle mask.

In the refined original canonical packing, suppose an entire simple
positive cycle has t loaded vertices and k isolated unloaded vertices,
with `k>=1`. Assume:

* Every unloaded vertex has exactly its two positive neighbors as
  actual physical neighbors.
* Every physical-unique loaded vertex has exactly its two positive
  neighbors as actual physical neighbors.
* Every positive cycle intersection is a physical singleton, with the
  original strict vertex/vertex separator convention.

Physical-two loaded bodies may have additional actual contacts; they
are not moved in the proof below. Every individual circle coefficient
is retained. We are in the same closed project radius window.

First, the original pair normals at any physical-unique loaded vertex
are nonparallel. To verify this directly, let its unique circle corner
be z and put `e=z/R`. If the two normals were parallel, their full
force equation and the positive circle load would make both normals
belong to `{e,-e}`. The direction e uniquely exposes z: containment
of its two adjacent vertices gives `z.u>=1/2>0` and `z.v>=1/2>0`
in its outward own axes. An e contact would share the circle corner,
which is impossible. Both normals must therefore be `-e` and both
applications the same opposite vertex p.

Each distinct neighboring square then contains `p-epsilon*e` in its
open interior for all sufficiently small positive epsilon. At a
relative-side-interior contact this is the neighbor's inward normal;
at a vertex/vertex contact strict original exposure places it strictly
inside that neighbor's inward vertex cone. The two neighbors would
have intersecting open interiors. This contradiction proves the
nonparallel claim. The existing project-window proper two-force lemma
therefore supplies the original q inside the unique-corner body and
both nonnegative proper port coefficients.

Theorem 3.1 now excludes every diagonal transmitter, so all k remaining
transmitters are side normal. Theorem 5.1 excludes a physical-two
loaded endpoint at any one of them. Consequently both ends of every
maximal loaded run are physically unique.

At a singleton contact a side transmitter owns its normal direction,
and the loaded endpoint supplies a strict vertex. Indeed if the
transmitter applied at its own corner, a vertex/vertex contact would
violate strict exposure in that body, while a vertex lying in the
neighbor's side interior would give a collinear positive shared segment.
If both applications were side interiors, their intersection would
again have positive length. These alternatives exhaust the boundary
features, so the actual contact is a strict loaded vertex against the
transmitter's side interior.

A loaded run of length one is therefore a physical-unique loaded body
with two strict vertex ports and no other actual neighbor. Its proper
q gives precisely the complete screen excluded by
`INWARD_CORRECTED_CANONICAL_ROTATION_EXCLUDES_THE_FULL_UNIQUE_CORNER_VERTEX_SCREEN_2026_10_30.md`.

A run of length two has physically unique ends A,B. At each end the
transmitter contact already exposes a strict vertex. To avoid that
same exclusion, its other contact, the direct AB edge, must be owned
by that loaded body. Thus both A and B would own the singleton AB
edge, which is impossible: a side/side support at an actual common
relative-interior point gives a positive-length shared segment, and
the vertex endpoint alternatives were just exhausted.

Every maximal loaded run consequently has at least three bodies.
There are exactly k such runs because the unloaded vertices are
isolated. Hence the complete necessary count is

    t>=3k.                                               (5)

**Theorem 5.3 (complete clean no-long C7 exclusion with four or five
loads).** Under the three complete physical conditions above, no
no-long positive C7 with four or five positive loads exists in the
refined original canonical packing. The two respective pairs
`(t,k)=(4,3),(5,2)` violate (5). All transmitter-width assignments
and all physical one-/two-circle masks are included. No two-circle
coefficient endpoint is discarded.

For six loads the bound permits the one run of length six. Its two
ends are necessarily physical-unique, and every possible physical-two
loaded body lies strictly inside that run. This is an explicit
remaining case, not a six-load exclusion.

Theorem 5.3 is a complete physical-feature family exclusion. If a
purported four- or five-load no-long C7 survives, at least one of the
three printed physical conditions must fail: an actual extra neighbor
at an unloaded or physical-unique loaded body, or a genuinely shared
positive contact, or the stated original strict-point convention.
It makes no claim that the full original coarse parent lacks those
remaining alternatives.

## 6. Direct sources and verification boundary

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | Existing original `(R,Phi)` minimum before the finite final tie-break. |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | True full-degree transmission and original support/moment equations. |
| `SIMULTANEOUS_ROTATIONS_EXCLUDE_SINGLETON_CYCLES_WITH_PHYSICALLY_ISOLATED_MOVING_STARS_2026_10_30.md` | `d3688215df65fbfa810b0a357119cf0a5787151b53f773607e53c4d2032c0997` | Actual diagonal-transmitter circle-mask and pivot calculation, repeated in Section 3. |
| `RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md` | `2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e` | Complete radial endpoint support cover and actual channel-height inequality, repeated in Section 4; no pocket-capacity conclusion is required here. |
| `INWARD_CORRECTED_CANONICAL_ROTATION_EXCLUDES_THE_FULL_UNIQUE_CORNER_VERTEX_SCREEN_2026_10_30.md` | `532af1f5caab560afea6a9c7b20e7503c85417a6692322d55f9adf45917b6742` | Complete screened-star exclusion in the loaded-run proof of Section 5.3. |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` | Project-window properness for the true-degree-two, now-proved nonparallel physical-unique loaded caller in Section 5.3. |

The side slide, finite integer tie-break, diagonal contact deletion and
whole two-circle blocker implication are proved above. No graph-only
rerouting, virtual contact, changed original mean, fictitious degree,
or discarded zero-weight physical corner is used.

No numerical pose search, mesh, computational packing certificate,
Lean/Lake build, CI, original flag mutation or remote edit was used.
