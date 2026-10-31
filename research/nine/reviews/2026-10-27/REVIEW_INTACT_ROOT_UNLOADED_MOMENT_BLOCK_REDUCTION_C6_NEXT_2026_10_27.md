# Independent review of the distance-free intact-root moment obstruction and block reduction

Date: October 27, 2026.

**Verdict: ACCEPT without mathematical correction.** This accepts the
entire distance-free local unloaded-neighbor theorem and the complete
necessary original-component normal form. It does not exclude the
remaining additional cyclic block or close another coarse cell by
itself. No original gate or shared ledger is changed.

Reviewed source:

    GLOBAL_NEXT_INTACT_ROOT_UNLOADED_MOMENT_AND_BLOCK_REDUCTION.md
    SHA256 103a0f4ceccba044c132a45c632bd64df57540feb70fd69d6159c52759e449c6

## 1. Exact local scope and complete physical cap

The local theorem assumes only actual open containment of the closed
D_epsilon in E, an actual unloaded positive neighbor U, and the strict
original moment pattern in which the E force has the opposite sign
to every other original U pair force. The full actual star is kept.
It has no positive-degree, proper-concurrence, extra distance, boundary-
neighbor or new normal-selection premise.

The initial whole-plane reflection fixes the moment signs together;
all later own-frame changes are proper rotations. The actual closed
U avoids int E and hence avoids the closed D_epsilon. Compactness
gives the strict distance dist(O,U)>epsilon. This applies at every
radius endpoint, including epsilon=0.

The source explicitly states and correctly uses both physical support
facts from 8def789e. Every actual contained neighbor beyond a support
h requires h<=d. If an actual contact point also has h>1 and
|p|^2>=2, the actual neighbor center has normal coordinate >3/2
and norm <91/60. Its transverse coordinate is therefore smaller
in absolute value than sqrt(181)/60, while the actual contact's
transverse absolute coordinate exceeds sqrt(3479)/60. Their distance
would exceed 11/15>1/sqrt(2), impossible inside that actual unit.

I independently reconstructed the exact bounds:

    2-(61/60)^2                         = 3479/3600;
    (91/60)^2-(3/2)^2                   = 181/3600;
    3479-58^2                          = 115;
    14^2-181                           = 15;
    (11/15)^2-1/2                      = 17/450.

This full cap does not require the neighboring unit to avoid the
epsilon-disk or to have any specified degree or load. It applies
to the actual point and actual support, including every original
owner and mean. That exact scope is needed in the new near-corner
case and is correctly retained.

## 2. The entire far-interval case is legitimately extracted

If an actual own interval misses zero by more than epsilon, a
proper own frame gives

    U=[a,a+1] x [b,c], c=b+1,
    a>epsilon, c>=-epsilon.

The proper quarter-turn argument covers the other interval with
c<-epsilon without reversing the already fixed moment signs.
Then a+1>1+epsilon>=d, and the actual root support is below
-epsilon. These are exactly the premises used after the frame
construction in d7c7c69d Sections 2--4. Its former strict distance
hypothesis has no later use.

I checked the complete restated feature proof. The support/moment
screen forces n_x<0. For n_y<0 the root lower-left moment gives
b>0; for n_y=0 its actual side mean gives c>0 without assuming
b>0. Every other negative-moment normal then has nonpositive
vertical component. The root's strict negative component, or
the remaining all-negative-horizontal balance in the axial case,
contradicts the complete U equation.

For n=(-u,v), u,v>0, the vector w=(v,u) is perpendicular to
the actual root force. The full upper/side/lower feature cover
makes every other negative-moment force have strictly negative
w-projection. In the only delicate lower-right cone, the two
endpoint supports at e_x and -n both exceed d, and all intervening
normals expose the same lower-right vertex. Their positive conic
coefficients sum to at least one, so every intervening unit normal
also has support above d. The remaining lower-right normals have
strictly negative w-projection. Every original side mean and cone
endpoint is included. The full force equation is again impossible.

Thus the entire far-interval case is proved at its exact extracted
scope; no second intact petal or distance above sqrt(2)*epsilon
is silently restored.

## 3. The new near-corner case covers the whole complementary domain

Suppose neither own interval misses zero by more than epsilon.
If either contained zero, the exact rectangular distance would be
at most epsilon, contrary to the strict disk avoidance. Both
intervals therefore miss zero. One of the four proper quarter
turns gives

    U=[a,a+1] x [b,b+1], 0<a,b<=epsilon.

No ordering of a and b is required. This case is empty when
epsilon=0, as the source states.

The actual root support below -epsilon rules out both negative
axes and both mixed-sign quadrants: their support is at least
-epsilon because a,b<=epsilon. The nonnegative quadrant has
positive support. Thus the unchanged root normal is strictly
southwest and has strictly negative vertical component.

For another original force to have negative moment, it cannot
use the top side or upper-left cone, whose actual moments are
strictly positive. At the upper-right vertex p=(a+1,b+1),
every unit normal (s,t) in its entire closed cone satisfies

    h_U(s,t)=(a+1)s+(b+1)t>s+t>=1,
    |p|^2>2.

The complete physical cap therefore excludes every actual contact
at that vertex, not merely a selected negative-moment direction.
Both axis endpoints at that vertex are included. An unrelated
horizontal side mean is correctly retained, and has zero vertical
normal component. Every remaining side or lower corner cone has
nonpositive vertical normal component.

The root force has a strictly negative vertical component while
all remaining original positive forces have nonpositive components.
Their full unloaded sum cannot vanish. This proves the new case
and exhausts the complete actual own-interval domain. All strict
and shared support features and original mean endpoints survive
until their displayed contradictions.

## 4. Full original-graph transfer at a single intact root

The complete intact-root theorem supplies D_epsilon inside int E
from one genuine intact triangle, with its two true loaded tips.
Work is confined to E's original positive connected component;
all other physical units and any other components stay present.

The already fully audited 8def789e theorem makes every cyclic
block contain E, every private positive edge nonradial, and every
private same-sign directed cycle impossible by the actual intact
tip exterior path. The complete bridge cut moment sum makes
every bridge radial. Consequently all bridges are incident to E
and their other endpoints are genuine degree-one leaves: another
private bridge would avoid E, and an additional cyclic block at
such an endpoint would provide an alternative path to E.

In any additional cyclic block B, each private vertex retains its
entire original B star and circle system. There is no outside
positive pair: another cyclic block would share both E and that
private vertex, and an E bridge would contradict the path already
inside B. The source proves this before applying the local kernel.

B-E is connected and has at least two actual vertices. Orient its
nonzero-moment edges positively. The forbidden private-cycle result
makes this orientation acyclic, so it has distinct source and sink
vertices, each incident to a private edge. Their complete torque
equations require actual E edges with moment opposite to all their
private moments. The new distance-free local theorem makes both
vertices circle-loaded. They are two distinct physical boundary
neighbors of E, with no degree-two equation or concurrence assigned
to either. This proves the entire arbitrary-degree block conclusion.

## 5. The necessary component form and all counting statements

Different additional cyclic blocks have disjoint private vertices.
Two such blocks would therefore supply four distinct boundary E
neighbors beyond the two intact tips, contradicting the complete
no-six physical theorem. Thus at most one additional cyclic block
exists. With such a block present, two direct genuine E leaves
would give six boundary neighbors again, so at most one is present.
All these are physical boundary counts, including possible zero
total multiplier at other physical contacts.

At least one additional cyclic block is necessary: with only the
intact triangle and any number of direct E leaves, their complete
positive center pressures contradict the full physically clear E
equation. If the additional block were a triangle, its two private
vertices have no outside forces and are true loaded degree-two
tips; the same complete pressure contradiction applies to the
two intact triangles and the possible direct leaf. The source
keeps both S and D genuine leaf alternatives in this argument.

Consequently the exact necessary form is one intact triangle,
one further cyclic block B at E, and zero or one genuine direct
E leaf, with no other positive vertex or edge in that component.
For q=|B| and ell in {0,1}, the exact original counts are

    component size = q+2+ell <=9,
    4<=q<=7-ell,
    degree(E)=2+degree_B(E)+ell.

The two source/sink neighbors give the lower bound of two
physical boundary B neighbors at E. The no-six theorem, after
the two intact tips and ell genuine leaves, gives the upper
bound 3-ell. Thus when ell=1 exactly two B neighbors are physical
boundary and every other B neighbor is physically clear. Further
zero-stress contacts can only strengthen this necessary bound;
they are not asserted absent.

The same-nine R>2 and full no-six-neighbor prerequisite scope is
explicitly retained, including the reviewed finite-certificate
dependency. No replacement packing or stronger table-free
prerequisite is asserted.

## 6. Exact whole-block pressure, dependency pins and accepted limits

I checked the complete end-triangle pressure interface statement
in BOWTIE_CELL_CLOSED.md Section 2 and the full genuine S/D leaf
identities in RADIAL_BRIDGE_AND_LEAF_REDUCTION.md Sections 5--6
in the immediately preceding uniform two-petal audit. Their exact
arbitrary-root scope and current hashes remain unchanged here.
The common-root forest source is used only for its recorded
pressure join, not an unstated bridge degree reduction.

The actual private B stars have no external pair force, so summing
their original force equations identifies the complete S_B circle
sum with all original E-to-B forces. The full remaining E equation
is exactly M_T+S_B+sum alpha_j e_j=0. The actual intact-petal and
genuine-leaf center pressures are positive, so c_E.S_B<0 strictly.
This is a necessary sign of the unchanged whole block sum; no
individual boundary force or circle atom is assigned that sign.

The principal current hashes were independently verified:

    new full source: 103a0f4ceccba044c132a45c632bd64df57540feb70fd69d6159c52759e449c6;
    complete cap/order input: 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49;
    complete far-interval input: d7c7c69d2ac398b402d0dcfaa4e77864c83596e7a1e520db0db3c023f34f7298.

The other current physical and pressure pins were verified in
REVIEW_TWO_INTACT_PETALS_COMPLETE_EXCLUSION_C6_NEXT_2026_10_27.md,
SHA256 aceba0387b6f8a3a79c0f17aed8f51e3666bbb588188419f5d6b89dc25477cc0,
and match the source's exact uses.

The full distance-free theorem and original-component normal form
are therefore independently accepted. No remaining q=4..7 block
or further coarse cell is inferred excluded from this necessary
form alone. All nine physical units, every circle mask, force,
normal, mean and genuine S/D leaf remain. The unrestricted bound
and equality classification stay separate original obligations.
No numerical pose, force sample, Lean compilation, CI, workflow,
physical motion, remote mutation or shared-ledger edit is used.
