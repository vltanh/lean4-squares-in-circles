# Independent full review of the shifted two-column six-unit capacity theorem

Date: October 28, 2026 UTC. Reviewer: house_finish_v2.
Author of reviewed target: tc_finish_v2. This reviewer did not author
or edit the target or its operative inputs.

**Verdict: PASS at the exact target pin below.** The complete continuous
six-unit geometry admits at most two additional actual unit squares,
at arbitrary orientations. The inaccessible-hole argument, strict
central clearance, complete circle-arc decomposition, every clipped
height endpoint and both continuous angle comparisons are valid.
No original graph family or flag is closed by this review alone; a
separate literal caller must supply the six actual units and the whole
slider range. That caller is not assumed here.

## 1. Exact frozen read set and independent method

I read the following files in full, without omitting any section or
relying on the verdict in an earlier review. The first is the target,
the second its sole direct analytic input, and the last two are the
operative arc prerequisites used by that input.

| File | SHA256 | Bytes | Lines |
| --- | --- | ---: | ---: |
| TWO_RADIAL_TERMINALS_SHIFTED_TWO_COLUMN_SIX_UNIT_CAPACITY_TWO.md | 1a9cc8be18de4a5a0c281faa0b99ec0ff1d7174cb8d1377fc34f8cb123dbec96 | 12105 | 313 |
| FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md | 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517 | 6528 | 192 |
| NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md | 4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366 | 6418 | 173 |
| NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md | 4da80eec56859a863f042257d8ae391c17409e2b0e82dbee2e6b7173838fa54b | 5848 | 181 |

This is a complete 859-line read set. I independently reconstructed
the support and interval geometry and the continuous trigonometric
inequalities. Ephemeral exact rational arithmetic checked the printed
identities and reserves. No pose sample, finite-angle mesh, numerical
optimizer, exclusion checker, Lean/Lake command, CI, metadata change,
staging, commit or remote operation was used. The frozen source bytes
were not edited.

## 2. Complete physical domain and scalar bounds

The target assumes six distinct actual contained interior-disjoint
units, with

    1/11<x<1/10,
    epsilon=x^2, d=1+epsilon, U=1-epsilon, V=2x,
    R^2=(d+1)^2+1/4,
    -1/2<=t<=z<=V.

The actual A,T rectangles form one left column; actual B,D form the
two possibly separated right pieces; actual C,L are the two specified
radial units. No stress, positive graph, load, boundary status of an
extra unit or orientation of an extra unit is assumed. Containment
and nonoverlap are hypotheses, so the proof may use a scalar range
that also includes nonrealizable six-unit configurations.

I verified U^2+V^2=d^2, so the given e=(-U,V)/d is indeed unit
and the stated L is an actual unit with orthonormal axes e,Je.
The whole interval bounds U>99/100, d<101/100 and
2/11<V<1/5 are strict as printed. The radius bound is

    R^2<42901/10000<1105/256,
    1105/256-42901/10000=4209/160000.

Thus every extra is contained in the same disk needed by the arc
input, without changing the original origin or radius of the packing.
Both real radial terminals remain occupied units in the argument.

## 3. The entire hole and every physical endpoint

The exact actual left union is

    K_L=[-U,epsilon] times [V-2,V].

When t<z, the potential gap H=(epsilon,d) times (t,z) has
its whole closed boundary covered by the original units. Its bottom
edge belongs to D and its top edge to B. Its left edge belongs to A,
because

    [t,z] subset [-1/2,V] subset [V-1,V].

Its right edge belongs to C, because [t,z] is contained in
[-1/2,1/2]. These containments include t=-1/2, z=V,
all horizontal and vertical edge endpoints, and all four corners.
The height is z-t<=V+1/2<7/10<1.

The target correctly uses the closed original units as barriers to
the open interior of any extra E. If a point of a closed prescribed
unit lay in int(E), the density of that unit's open interior would
give actual open-interior overlap near the point. Thus int(E)
avoids every prescribed closed unit, including their boundaries.

If the connected open square int(E) entered H and also had a point
outside H, an interior path would cross the occupied boundary of H.
Hence entering H would confine the entire int(E) to H. This is
impossible because every unit square has vertical projection width
at least one, whereas the hole height is strictly below one.
The same conclusion excludes a closed E point in the open H:
nearby points of int(E) would still belong to H.

It follows that the whole closed rectangle

    K_R=[epsilon,d] times [t-1,z+1]

is inaccessible to int(E), with no physical square moved or replaced.
At t=z there is no inserted hole, and K_R is exactly the actual
B union D. Since t<=z, the smaller rectangle

    K_0=[epsilon,d] times [z-1,z+1]

is a valid blocked subset in every case. No force, degree or actual
application is attributed to either filled rectangle. This is an
accessibility argument about the same actual E, not a replacement
packing or an assumption about its center.

## 4. Strict central clearance and the complete arc prerequisite

I checked that K_L union K_0 contains the whole closed origin disk
of radius V. On its part x<=epsilon, the x range is contained in
[-U,epsilon] because U>V, and [-V,V] is contained in [V-2,V].
On its part x>=epsilon, d>V and the exact endpoint bounds give

    z-1<=V-1<-V,
    z+1>=1/2>V.

Thus any actual closed E point strictly inside this disk would have
nearby interior points in the blocked union. The proof has already
excluded such interior points, including those in H. Seams do not
allow an open part of E to pass through. Therefore

    dist(O,E)>=V>2/11>1/8.

This is stronger than the strictly greater than 1/8 hypothesis of
the imported arc theorem. The equality counterexample at clearance
1/8 is irrelevant here because the new strict reserve has been
proved for every actual extra.

I also checked the complete analytic input, not merely its statement.
Its two actual far-coordinate domains a>rho and a<=rho are both
retained. In the first, fixed-radius convexity proves the strengthened
quadratic bound with exact reserve 411/200000 at the larger endpoint
estimate. All four actual interval endpoint differences exceed
2pi/9; the clipped top-face endpoint creates no second arc because
the inner vertical face is strict. In the second, the strict
clearance gives 0<B<=A<=1/8 and a>13/12; both outer faces remain
in the full interval. Their sine estimate is exactly greater than
59/81, which exceeds sin(2pi/9). The inner-face and both strip
comparisons also exceed that same angle, including a=rho and b=rho.

The unit-incircle argument for the actual center direction is valid
as well, although the target capacity proof does not need to route
units by that direction. The exact upper center-radius reserve is
31/57600 at 91/60. Consequently every actual extra supplies its
entire connected open radius-9/8 circle intersection, of length
strictly greater than delta=2pi/9. These arcs are pairwise disjoint
because the actual open square interiors are disjoint.

## 5. Exact closed arcs of C, L and the left column

The definitions

    a=acos(d/rho), b=acos(U/rho), c=acos(epsilon/rho),
    phi=atan(V/U), alpha=asin(4/9), rho=9/8

have all angles in their stated positive branches. In particular
a,b,c<pi/2, and alpha<pi/6.

For each real radial terminal the inner face is the active constraint.
The lower parameter endpoint gives d>122/121, and

    64*122^2-65*121^2=911>0.

Therefore d^2>rho^2-1/4, the circle's transverse coordinate within
the inner-face arc has absolute value strictly below 1/2, and
a<alpha. The outer face is inactive because rho<d+1. Hence the
entire closed physical intersections are exactly

    C: [-a,a],
    L: [pi-phi-a,pi-phi+a].

This includes both inner-face equality endpoints. No smaller selected
subarc has been substituted for either terminal.

For K_L, a point at nonnegative height has squared norm at most
U^2+V^2=d^2<rho^2. No such point belongs to this inner circle.
The bottom height V-2 is below -rho, and the top height V is
positive. Thus only the horizontal x range cuts the lower semicircle,
giving the exact closed intersection

    [pi+b,2pi-c].

Both its endpoint signs and its circle wrap position are correct.

## 6. Right-column clipping and the exhaustive three-gap decomposition

On the right semicircle, epsilon<=x<=d is equivalent to
a<=|theta|<=c. The upper height z+1 is positive and the lower
height z-1 is negative. The target's definitions

    eta_+=min(c,asin(min(1,(z+1)/rho))),
    eta_-=min(c,asin(min(1,(1-z)/rho)))

therefore give exactly, with all equality endpoints,

    K_0 upper: [a,eta_+],
    K_0 lower: [-eta_-,-a].

Both eta values are at least alpha, and alpha>a. This follows
from z+1>=1/2, 1-z>4/5, and c>alpha. It remains valid when
a height exceeds rho, when the outer asin is pi/2, and when
the x cutoff c is the active endpoint. The common intervals are
never reversed or empty. Together with C they block the whole
closed East interval [-eta_-,eta_+].

I independently checked the cyclic order used to list the complement.
Since U<d, one has b>a; and the proved phi<a gives phi+a<pi/3.
Thus the L start is above 2pi/3 while eta_+<pi/2. Its end is
before pi+b because a-phi<b. The left-column end is 2pi-c,
and the East interval resumes at 2pi-eta_-, which is no earlier.
There are exactly the following open gaps, with no omitted interval:

    G_top=pi-phi-a-eta_+,
    G_side=b+phi-a,
    G_bottom=c-eta_-.

The top and side gaps are positive; the bottom may vanish. Every
blocked endpoint is closed, so a connected open extra arc cannot
cross from one gap to another through an endpoint. The formula also
includes the entire wrap around East.

For the side estimate, the conservative exact bound is already

    rho*U-d^2>(9/8)(99/100)-(101/100)^2
                 =1873/20000>0.

Since cos(phi)=U/d, this proves phi<a. Also

    (22/25)^2-3/4=61/2500>0,
    U/rho>22/25>sqrt(3)/2.

Hence b<pi/6 and G_side<b<pi/6<delta. No actual extra's
strictly longer than delta connected arc fits there.

## 7. The complete continuous sum of the other gap lengths

Put M=sqrt(rho^2-epsilon^2), so 1<M<rho and c=asin(M/rho).
When z>=M-1 the upper angle equals c, while the lower is at least
alpha. When z<=1-M the lower equals c, while the upper is at
least alpha. These are the two complete clipped regimes, including
both threshold equalities and the original z endpoints.

In the entire middle interval |z|<=M-1, the unclipped expressions
remain valid, including equality with c at a threshold. Their two
arguments lie strictly below one because M<rho. Convexity of asin
therefore proves

    eta_++eta_-
       >=2asin(8/9)>pi/2+alpha>c+alpha.

For the strict middle inequality, beta=asin(8/9) has
2beta-pi/2 in (0,pi/2) and

    sin(2beta-pi/2)=47/81,
    47/81-4/9=11/81>0.

Sine is strictly increasing on that full interval. The resulting
uniform bound eta_++eta_->=c+alpha is consequently valid on the
whole original z range, without a sample or an unproved endpoint.

The remaining comparison phi+a+alpha>pi/3 is also correct.
The exact reserves checked independently are

    200/1111-9/50=1/55550>0,
    rho^2-(101/100)^2-(49/100)^2=217/40000>0.

Thus V/d>9/50 and sqrt(rho^2-d^2)>49/100. The exact cosine
identity and upper comparison give

    cos(phi+a)
       =U/rho-(V/d)*sqrt(rho^2-d^2)/rho
       <8/9-49/625=4559/5625.

On the other side,

    cos(pi/3-alpha)=sqrt(65)/18+2sqrt(3)/9>22/27,
    22/27-4559/5625=73/16875>0.

Both compared angles lie in (0,pi), so the direction of the strict
cosine inversion is correct. Therefore

    G_top+G_bottom
       <=pi-phi-a-alpha<2pi/3=3delta.

This single strict estimate applies to every t and z in
-1/2<=t<=z<=V. The parameter t affects the genuinely excluded
hole and the blocked-set inclusion; it has not been fixed or chosen
to improve an arc inequality.

## 8. Capacity conclusion, exact acceptance and scope

Every additional actual unit has its whole connected open arc in
one of the three actual complementary gaps. The side gap holds
none. Three further actual units would give three pairwise disjoint
arcs, each longer than delta, in the union of the top and bottom
gaps. Their combined length would exceed 3delta, whereas the whole
available length is strictly smaller. This is a contradiction.

The conclusion is therefore exactly the claimed capacity at most
two, for every extra orientation, contact and physical mask. The
proof does not presume an extra is circle-loaded, circle-clear,
central, in a geometric pocket, or wholly in a sector determined
by its center. It proves the necessary clearance for each actual
unit and routes its actual complete arc.

I accept the exact 1a9cc8be18de4a5a0c281faa0b99ec0ff1d7174cb8d1377fc34f8cb123dbec96
source at its whole displayed physical scope. No repair or source
edit is required. A separate original-graph assembly must still
supply all six literal actual squares and the whole slider cover.
No fine flag, coarse flag, whole original family or computational
certificate is retired merely by this force-free capacity review.
