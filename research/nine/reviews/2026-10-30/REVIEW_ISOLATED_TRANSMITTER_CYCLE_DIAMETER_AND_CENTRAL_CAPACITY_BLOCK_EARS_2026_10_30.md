# Isolated-transmitter cycles: full path-premise and central-capacity review

Date: October 30, 2026 UTC.

**Verdict: PASS at the full stated scope. No repair requested.**

Reviewed source:
`ISOLATED_TRANSMITTER_CYCLES_HAVE_SHORT_CENTER_DIAMETER_AND_CENTRAL_CAPACITY_ONE_2026_10_30.md`.

Frozen length: 18,026 bytes. SHA256:
`e5a4522cad96c419ea0d65eea515557b9118c66e910660cfe4ea873a64a98f6b`.

I read this entire source and all seven complete sources in its pin
table. In particular I read all 630 lines of the original width-one
path proof, all of the diagonal path and two-middle-boundary path
proofs, the full loaded-force/nonparallel and proper polygon proofs,
and the entire central-transfer and exterior-routing sources. The new
premise removal is checked against the actual proof, not against its
title or a local summary. The existing subsidiary geometric lemmas
remain imported at the accepted scopes explicitly identified by those
complete sources; this review does not claim a new global selected-
certificate construction.

## 1. Exact preserved domain

The theorem retains one original compatible physical certificate in
79/40<=R<=sqrt(1105/256), including force and angular equations,
point normals, owned-side means, physical circle masks, diagonal
avoidance, physical embedding and simultaneous exterior spokes.
The entire positive component is a simple cycle on 3<=n<=7 bodies,
with at least three positive total circle loads and no adjacent
unloaded vertices. Thus every cycle vertex really has full positive
pair degree two. An unloaded vertex may still physically touch the
circle; the source explicitly retains that possibility.

No extra edge is deleted to manufacture a transmitter or a loaded
degree-two concurrence. No force-only certificate is promoted to a
torque-balanced one. All actual squares outside the component remain
in the packing. The theorem is conditional on the specified compatible
certificate, and does not settle the separate common-selection audit.

## 2. The proper-channel join with an unloaded A

The only extended local path has consecutive actual bodies
A--B--U--C, with U unloaded, B,C loaded, and A of either load
status. If A is unloaded, B has two unloaded immediate neighbors.
This is exactly a case covered explicitly by
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md. Its proof follows the
two whole channels to their next loaded endpoints, which are distinct
because there are at least three loads. Its radial-D/radial-S
alternatives retain the actual means and exclude all possible pairs
of reserves. It has no premise that B has an immediate loaded neighbor.

The full convex force polygon theorem therefore applies unchanged.
It gives proper concurrences, exact contraction of every original
unloaded run, nonzero common moment, the physical spoke order and
positive winding, and then a strictly convex contracted force polygon
containing the origin. Its Section 5 gives the actual positive channel
height, the nonnegative transverse endpoint-center heights and opposite
longitudinal center signs. These conclusions concern B--U--C and the
original whole component. None requires A to be loaded.

The true U force and moment equations give actual width one or sqrt(2)
and keep the exact two contact means. In the diagonal case the original
compatible diagonal convention gives the actual endpoint side axes;
the source has not selected a new normal. Thus the whole-cycle caller
supplies every listed local premise, including B's true nonparallel
two-force properness, when A is unloaded.

## 3. Complete audit of the width-one proof

The theorem statement of
FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md lists A as loaded,
but its complete displayed proof uses no circle equality, positive
circle atom, or force equation at A. I checked the following full
dependency chain.

First, actual support and the original means give
P_C=P_B+d, |d|=1, and d.(z-P_B)<=0 on B. For every z in B,
|P_C-z|>=d.(P_C-z)>=1, while z=P_B attains one. Therefore
dist(P_C,B)=1 exactly, including the full original side-mean interval.

For R<sqrt(17)/2 the universal contained-center inequality alone
makes every center radius less than 3/2. In each of the other three
closed radius rows, the actual upper radius is strictly less than
M_j^2+M_j+1/2. A hypothetical endpoint distance at least three
therefore puts both center radii in (3-M_j,M_j), regardless of A's
physical circle status.

The proof next uses circle equality only at C. In C's own frame it
derives x>59/40, |y|<7/50 and the stated small radial tilt. The
horizontal-owned support alternative would put the unchanged B mean
inside radius 129/200; every point of the actual boundary B has radius
greater than R-sqrt(2)>129/200. Thus the original C application is
its inward upper/lower vertex. This argument uses B and C boundary
status, not A boundary status.

The complete far-A wall is a containment argument. With A's actual
center radius rho and actual radial frame tilt psi, it uses

    rho^2+rho(cos psi+sin psi)+1/2 <= R^2
                                       < M_j^2+M_j+1/2.

The assumed endpoint distance supplies the small center-angle interval
|eta|<theta and radial deficit
M_j-rho<M_j tan(theta)(theta-|eta|). The actual containment inequality
then gives psi<(3/2)(theta-|eta|). The two sign cases for eta bound
the actual support halfwidth and prove the strict whole-square wall
A subset {p:n.p<1/2}. They never set a corner of A on the containing
circle. In particular, the radial interpolation is a scalar comparison
of containment inequalities, not a replacement by a boundary pose.

After that wall, the proof uses A once: its actual A/B contact lies
in B and in the wall, so min_B n.p<=1/2. Nothing in the rest of the
proof involves A's load, circle mask, frame or degree.

I checked the rest of the proof to ensure the wall was the only A
input. The original C application is bounded in the wall frame by
the three unchanged radius rows. The adverse radial comparison and
zero-tilt endpoint calculation concern C alone. The actual channel
center signs and B's boundary radius then force B into the upper-left
wall quadrant. Both signs of the channel angle are treated, including
the full support-mean inequalities used in the negative-angle case.

Finally B's two farthest-circle-corner alternatives are exhaustive in
that quadrant. The P+v branch uses its positive-definite quadratic
completion with reserve 1289/318400. The P+u+v branch includes its
nonpositive bottom height, the fixed (15,-8)/17 separator, and the
remaining actual own-side separator. The fixed radical comparisons
cover all three radius rows; the last orientation intervals have
strict lower gaps 4011/4000, 807/800 and 631/625. All circle ties and
face endpoints remain included. These prove dist(P_C,B)>1 and
contradict the original exact channel distance.

Thus the unchanged entire side proof proves |c_A-c_C|<3 with A
merely contained and actually contacting B, once the listed proper
channel premises are present. It is legitimate to remove precisely
that unused A load premise. B's and C's actual boundary premises
remain essential and are preserved.

## 4. Diagonal and two-middle-boundary inputs

The diagonal source already states the merely-contained-A extension
in its Section 6. I read its full proof. Its only A inputs are the
universal radius bound, the assumed far endpoint distance, the actual
whole-square support halfwidth and the original A/B contact. The far
distance forces whole A into x<-2/3. Actual B/C diagonal axes, the
original channel height and B's proper concurrence then exhaust B's
downward support alternatives. In the strict bottom-left case, the
original support vector has positive components and slope below4/15;
it gives support less than11/24 of its first component, contrary to
the unit-square lower bound1/2. No circle equation at A occurs.

The two-middle-boundary path theorem explicitly allows both endpoints
to be merely contained and of arbitrary degree. I read the complete
endpoint-sector and angular-shadow argument. It uses circle contact
only for the two middle units. The endpoint radial interpolation starts
from containment, not circle equality. Minor angular distance and its
triangle inequality give the sector split, so no circular order of a
path containing circle-clear endpoints is inferred. It proves the
strict endpoint bound independently of stress.

These two inputs and the extended side proof therefore cover exactly
the local cases required by the new pair argument.

## 5. Complete graph pair cover

On a simple cycle of length at most seven, every pair has a shorter
path of at most three edges. An actual contact bounds adjacent center
distance by sqrt(2), since each center is at distance at most
1/sqrt(2) from the same contact point. Two-edge paths have distance
at most2sqrt(2)<3.

For a three-edge path S_0--S_1--S_2--S_3, if both middle vertices
are loaded, the two-middle-boundary theorem applies directly. Otherwise
they cannot both be unloaded, by the original isolation assumption.
Reverse the path if necessary to put the unloaded middle vertex at
S_2. Its two actual neighbors S_1,S_3 are loaded, again by isolation.
The local path is therefore A--B--U--C with B,C loaded and A of
arbitrary original load status. The extended side or already extended
diagonal proof applies, as determined by U's unchanged true width.

These alternatives exhaust every pair without any placement table or
assumption that unloaded endpoints are boundary units. They establish
the full actual center diameter strictly below three. Three-edge
paths have four distinct vertices in the simple cycle, as required by
the local inputs. No path with two consecutive unloaded middle bodies
is included; a long channel is correctly outside this theorem.

## 6. Whole central free union, including weak physical junctions

The source forms the original center/contact chain Gamma using the
same actual means. The accepted central-capacity theorem requires
actual contained ring squares, actual successive contacts, all pairwise
center distances below three, and a nonzero winding label around every
point of every proposed central extra interior. The first three
premises are now literal properties of the unchanged configuration.

The compatible physical embedding supplies the fourth. A compact
subset of an extra interior has positive distance from the closed core
union. Small physical Jordan routings and homotopies inside the actual
core preserve its bounded-side winding. This argument is applied to
all proposed central extras, not to one chosen bounded component.

I read the full geometric transfer. It replaces the occupied
center/contact chain by the actual center chain using clear-endpoint
chords and replacement triangles of area at most1/4. It proves winding
preservation without assuming that center chain is simple or convex.
Its missing-face extraction uses that winding and actual edge lengths,
then the accepted parallel and nonparallel local pair exclusions use
actual ring centers and their diameter bound. No fictitious hull edge
or independently chosen witness is inserted by this application.

Consequently at most one additional unit can lie in the whole central
free union, even when extra zero-weight physical contacts divide that
union into several components. The theorem does not assign a separate
capacity allowance to each component and does not substitute the
contracted force polygon for the actual physical enclosure.

## 7. Literal seven-body completion consequence and limits

I read the entire original channel-pocket routing source. Its Sections
1--2 concern any whole multi-load simple positive component; the later
C6 table is an application, not a restriction on those two sections.
The proper positive-height channel and its actual occupied transmitter
segment join the facing physical circle corners to give an exterior
crosscut. The actual sector/spoke order identifies the corresponding
outside region. Small physical junction perturbations and homotopies
inside occupied squares preserve every proposed extra's region label.
Two-corner radial caps and direct loaded-pair pockets cannot hold a unit;
zero-weight contacts on a transmitter can only subdivide its same
exterior region.

For n=7 there are two actual completion units. Since at most one is
central, at least one belongs to an actual exterior singleton-channel
pocket. The isolation premise ensures every nonempty unloaded run is
indeed a singleton. This covers four, five, six and seven load counts,
all isolated placements, every side/diagonal assignment and every
physical zero-weight circle contact. The all-loaded subcase has no
such pocket and therefore cannot accommodate two extras.

For a six-load cycle, the further one-central/one-exterior allocation
uses the separately accepted capacity-one result for its sole pocket
only in that result's radius range, as the source explicitly states.
The new theorem does not exclude simultaneous central and exterior
occupancy. For lower load counts it likewise does not add incompatible
capacity maxima or declare all seven-body completions impossible.

All seven dependency pins match the current source bytes. No original
proof gate, ledger, normal, contact mean, load or actual body was changed
by this proof or review. No numerical pose search, Lean/Lake build or
CI execution was used.
