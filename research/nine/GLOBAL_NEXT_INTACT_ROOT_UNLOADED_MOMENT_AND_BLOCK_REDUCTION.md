# An intact root excludes every unloaded neighbor with one opposed moment and permits only one further cyclic block

Date: October 27, 2026.

**Status: complete proposed uniform local theorem and full original-graph
reduction, frozen for root and separate independent review.** No shared
ledger, original gate or remote source is changed.

Keep all nine actual unit squares, their common compatible selected
physical certificate and the original window

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60.

Every circle mask, zero individual weight, original positive force,
actual normal, contact point, side mean, true degree and physical unit
is retained. All disks below are closed.

## 1. Uniform local statement without an additional distance premise

Let actual E contain D_epsilon in its open interior. Let U be an
actual positive neighbor of E with zero total circle force. Suppose
the original U-to-E force has nonzero origin moment, and every other
original positive force at U is a pair force with a nonzero moment
of the opposite sign. Then this configuration is impossible.

U's true positive degree is arbitrary. All its original forces are
included; no circle or pair force is dropped. E and all other
neighbors retain arbitrary actual degrees, full forces and circle
masks. No proper concurrence or normal selection is assumed in this
local theorem. In particular there is no dist(O,U)>sqrt(2)epsilon
premise.

Reflect the whole coordinates if needed so that the U-to-E moment
is positive and all the others are negative. Thereafter use only
positively oriented own frames, preserving those chosen signs.
Actual closed U is disjoint from D_epsilon, because that entire
disk lies in int E. Compactness gives dist(O,U)>epsilon.

We use the two complete physical support facts in Section1 of

    GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md
    SHA256 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49.

First, a contained unit V beyond an actual unit-normal support
n.x>=h requires h<=d. This follows from its center bound
|c_V|<=d+1/2 and its half-width at least1/2.

Second, no actual contact application p and neighbor V beyond
n.x>=h=p.n can satisfy simultaneously

    h>1, |p|^2>=2.                                          (1)

For completeness, h<=d<61/60 and c_V.n>3/2 would imply

    |p.Jn|>sqrt(3479)/60,
    |c_V.Jn|<sqrt(181)/60,
    |p-c_V|>(58-14)/60=11/15>1/sqrt(2).

The last inequality contradicts p belonging to the actual unit V.
This entire cap uses neither neighbor degree, boundary status nor
disk avoidance. It includes all support owners and original means.

For the unchanged U-to-E unit normal n at its actual point p,
the actual common support and strict disk containment give

    h_U(n)=p.n=min_(x in E) n.x< -epsilon,
    det(p,n)>0.                                             (2)

## 2. Complete case with a far own interval

Suppose at least one actual own interval of U misses zero by more
than epsilon. Then there is a positively oriented own frame

    U=[a,a+1] x [b,c], c=b+1,
    a>epsilon, c>=-epsilon.                                (3)

Choose the far interval as the positive x interval. If the resulting
c is below -epsilon, make the proper quarter turn x'=-y,y'=x;
its new a is -c>epsilon and its new c is the old a+1>0.
Thus a+1>1+epsilon>=d in every case, including epsilon=0.

The full support-feature proof of
GLOBAL_NEXT_TWO_INTACT_PETALS_HOUSE_FAN_BOUQUETS_EXCLUSION.md,
SHA256 d7c7c69d2ac398b402d0dcfaa4e77864c83596e7a1e520db0db3c023f34f7298,
Sections2--4 applies from (3) onward. Its earlier distance hypothesis
was used only to establish the existence of a far interval. To make
this extraction explicit, here is its complete remaining argument.

Equation(2) forces n_x<0. If n_x>=0,n_y>=0, the support is at least
-epsilon by c>=-epsilon. The downward vertical axis has negative
moment. For n_x>0,n_y=-v<0, positive moment at (a+1,b) forces b<0,
but then its support (a+1)n_x-bv is positive. All these alternatives
contradict (2).

If n_y<0, the positive moment at the lower-left vertex (a,b) forces
b>0. If n_y=0, its actual left-side mean has positive height, so
c>0 without any assertion about b. For c>0 every other negative-
moment normal has nonpositive vertical component: the top and
upper-left moments are nonnegative, the right-side support exceeds
d, and an upper-right normal (s,t) with negative moment would have

    h_U(s,t)>(a+1)/s>=a+1>d

when t>0, with the horizontal endpoint already excluded. The other
features are the left side and lower cones. Thus n_y<0 makes the
full vertical force sum negative. For n_y=0, vertical balance forces
all other normals to be horizontal; +e_x is impossible, so they
all point -e_x and cannot balance the root force. This includes
the actual uncentered left-side mean and all endpoint cases.

It remains n=(-u,v), u,v>0, at (a,c). Set w=(v,u), so w.n=0.
Every other negative-moment force has strictly negative w-projection.
Here are all possible features:

* Right side and top side are excluded as above. At the upper-right
  corner, negative moment is impossible for c<=0 and forces support
  greater than d for c>0 by the same complete calculation.
* In the upper-left cone, g=(-s,t), s,t>=0, negative moment forces
  c<0,s>0 and t/s<-c/a. The positive root moment a v+c u>0 gives
  -c/a<v/u. Hence w.g=-v s+u t<0.
* Left side, bottom side and the lower-left cone have normals
  -e_x, -e_y and (-s,-t); all have strictly negative w-projection.
* For a lower-right normal g=(s,-t), s,t>0, the inequality
  t/s<=v/u would put g in the cone between e_x and -n. Those two
  endpoint normals expose the same lower-right vertex, and

      h_U(e_x)=a+1>d,
      h_U(-n)=u+v-h_U(n)>1+epsilon>=d.

  Write g=lambda e_x+mu(-n), lambda,mu>=0. Since g is unit,
  lambda+mu>=1. Linearity of support on that vertex cone gives
  h_U(g)>d(lambda+mu)>=d, impossible for an actual neighbor.
  Thus t/s>v/u and w.g=v s-u t<0. The two axis endpoints were
  already covered.

The root force has zero w-projection and all other positive forces
have strictly negative projection, contradicting the full unloaded
equation. This finishes the far-interval case, without requiring a
second intact petal or any further distance premise.

## 3. Complete remaining near-corner case

Suppose neither own interval misses zero by more than epsilon. If
one interval contained zero, the exact distance of U from O would
be at most epsilon, contradicting disk avoidance. Thus both intervals
miss zero strictly, and a positively oriented own frame puts

    U=[a,a+1] x [b,b+1],
    0<a<=epsilon, 0<b<=epsilon.                            (4)

One of the four proper quarter turns gives this first-quadrant
chart. The case epsilon=0 cannot satisfy (4) and was already covered
by Section2. No comparison or ordering between a and b is imposed.

The support inequality (2) forces both components of n to be strictly
negative. Indeed an axial negative normal has support -a or -b,
at least -epsilon. A normal (-u,v), u,v>=0, has support
-a u+(b+1)v>=-epsilon, and a normal (u,-v) has support
(a+1)u-bv>=-epsilon. The nonnegative quadrant has positive support.
These exhaust every direction except the strict southwest cone.
Consequently the actual root force has strictly negative vertical
component, at U's actual near vertex (a,b).

Every other negative-moment normal has nonpositive vertical component:

* A top-side normal has positive moment p_x>0.
* An upper-left normal (-s,t), s,t>=0, has moment
  a t+(b+1)s>0 for every unit normal in that cone.
* No actual neighbor can touch the upper-right vertex at all.
  At p=(a+1,b+1), every unit normal (s,t), s,t>=0, has

      h_U(s,t)=(a+1)s+(b+1)t>s+t>=1,
      |p|^2=(a+1)^2+(b+1)^2>2.

  The full physical cap (1) forbids that actual contact. This
  includes both axis endpoints at that vertex. It does not forbid
  an unrelated right-side mean, which still has zero vertical
  normal component.
* Both side horizontal normals have zero vertical component. The
  bottom side and both lower corner cones have nonpositive vertical
  component, with all means and endpoints included.

The full vertical sum is therefore strictly negative because of
the root force. This contradicts U's unloaded equation and proves
the complete uniform theorem of Section1.

The proof has exhausted all actual own intervals, support features,
owner classes, original means and radius endpoints. The new part
uses only the exact contained-neighbor cap, without giving a circle
load or fictitious radial point to any other body.

## 4. Every additional cyclic block at an intact root has two loaded root neighbors

Now let E carry one actual intact triangle E-P-Q-E. The complete
root theorem gives D_epsilon subset int E. Its exact source is
ROOTED_INTACT_PETAL_CENTRAL_DISK_INTERIOR.md, SHA256
8a2fda961a9d9f76191add305ff65d4942e9e583a611448ec51d77df313035a8.

Work only in E's original connected positive component, leaving all
other positive components and physical units untouched. The full
8def789e theorem gives:

1. every actual cyclic biconnected block in this component contains E;
2. every positive edge between two bodies other than E has nonzero
   original origin moment;
3. no actual private simple cycle has all directed moments of one
   strict sign, because it would wind around O and obstruct the
   original E-to-P boundary access.

Every positive bridge is radial by summing the complete cut-side
origin-moment equations. Internal pairs cancel at their unchanged
common applications and every original circle atom has zero moment.
Consequently property2 excludes every bridge whose endpoints both
differ from E. Each remaining bridge E-L has a genuine degree-one
other endpoint: any other bridge there would avoid E, while any
cyclic block there would also contain E and would make E-L nonbridge.
Thus all bridges are genuine direct leaves at E.

Let B be any cyclic block different from the intact triangle. Its
private vertices have no outside pair force. Another cyclic block
there would share both that vertex and E with B, impossible for
distinct maximal biconnected blocks. A bridge there would have to
join E and contradict its bridge status. Hence all actual pair
forces at a private B vertex are exactly its B forces; its complete
original circle system remains.

The graph B-E is connected and has at least two vertices. Orient
each of its nonzero-moment edges in the positive-moment direction.
By property3 this is a finite acyclic orientation. It has distinct
source and sink vertices U,V, each incident to a private edge.
The full source torque equation forces an actual U-to-E edge of
strictly negative moment, because all private outward moments are
positive. The sink equation forces an actual V-to-E edge of
strictly positive moment, opposite to all its private outward
moments. No force at either vertex was omitted in these statements.

The complete local theorem of Sections1--3 forbids either U or V
from having zero total circle force. Both are therefore actually
circle-loaded, in particular physical boundary neighbors of E.
Their actual units are distinct from each other and from the two
intact tips. We have proved the full arbitrary-degree conclusion

    every further cyclic block supplies at least two distinct
    physically boundary positive neighbors of E.                 (5)

The source/sink orientation is auxiliary graph reasoning only.
No physical positive force, original magnitude, normal or mean is
changed, split or reassigned by this orientation.

## 5. Complete original-component normal form

The uniform geometric theorem says no actual square can have six
distinct physical boundary neighbors in this same nine-packing.
Use NINE_SQUARE_CENTRAL_DISK_AND_SIX_BOUNDARY_NEIGHBORS_EXCLUSION.md,
current accepted-header SHA256
3d80e291f2f5c095f91011fbc7e6014dbb4f5abd5441bc4c2a2da64fb14d2058,
reviewed mathematical SHA256
b270c64641ae3299e8b471084b807fc44f2ef2a5e6ff1a8621826ddbd2f1d4e5.
Its radius premise follows from the accepted same-nine R>2 theorem,
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md, current SHA256
46220c8a3eb3f539c682bf6a6fa932edf003e37484e0f6004d321e7cb14d7957.
The latter's reviewed five-charge finite certificate and existing
prerequisite-audit status remain explicit; no table-free replacement
is claimed.

E has its two intact physical boundary tips. Two further cyclic
blocks would give four more distinct boundary neighbors by (5),
contradicting that physical theorem. Thus there is at most one
further cyclic block B. If B exists, two genuine direct leaves
would give six boundary neighbors together with its two source/sink
neighbors and the intact tips. Hence there is at most one direct
leaf when an additional cyclic block exists.

There must in fact be one additional cyclic block. Otherwise the
entire E component is its intact petal and genuine direct E leaves.
The complete actual root equation is their force sum. Its scalar
product with c_E is strictly positive, because an intact petal has
strictly positive center pressure and each real S or D leaf has
strictly positive center pressure. E is physically clear since it
contains O openly. The full pressure sources and the actual leaf
identities are recorded in Section6 below. This contradicts the
whole root equation, including the case of no leaves.

The additional block B cannot be a triangle either: its two private
vertices have no outside pair force, so it would be a second genuine
intact petal. The same full pressure contradiction applies to two
petals and the possible direct leaf. No isolated-bowtie root equation
or fictitious leaf replacement is imposed here.

Consequently any remaining component containing an intact petal has
the following complete original form:

    one intact triangle at E;
    exactly one further cyclic block B at the same E;
    zero or one genuine direct leaf at E;
    no other positive block, bridge, or vertex in that component.

Write q=|B| and ell for the number of direct leaves. Then

    ell in {0,1},
    4<=q<=7-ell,
    actual positive component size = q+2+ell <=9.             (6)

All physical completion squares remain, including any additional
positive component not connected to E. Every private B vertex keeps
its true B degree and full original circle system. E's true degree
is 2+deg_B(E)+ell. Its number of physical boundary B neighbors is
at least two and at most 3-ell. In particular if ell=1, exactly two
B neighbors are physical boundary and every other B neighbor of E
is physically clear, including zero-weight circle-contact proposals.

## 6. Full pressure scope and the strict necessary sign of the remaining block

The complete end-triangle pressure theorem is BOWTIE_CELL_CLOSED.md
Section2, current SHA256
6feb6e53387be1ba25adc0f3ca901ffce029e6dd3466678b548991d198c6dcf6.
It gives c_E.M_T>0 for the full two-tip resultant M_T at arbitrary
true E degree, with all original masks, weights, normals and means.

The complete genuine-leaf identities come from
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md Sections5--6, current SHA256
faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676.
For an actual S leaf direction e,

    c_E.e=d-H_E(e)>=d-1/sqrt(2)>0.

For an actual D leaf the strict point-normal bridge convention
makes its E contact relative-side-interior, and

    c_E.e=R-sqrt(2)-1/2>0.

Both alternatives and all their actual force magnitudes are retained.
These same full identities are assembled in Section4 of
GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md,
current accepted-header SHA256
543bd9504574af9c039e54857657d47cc84c4d973c32c4cfe710610433797e33.
No bridge-only minimal-support reduction from that source is needed
here; Section4 above supplied the entire actual bridge conclusion.

For the exact remaining block B in (6), let S_B be the unchanged
sum of all original private B circle resultants. Summing those
actual private equations identifies S_B with the sum of the
original E-to-B forces. All other E forces are exactly the intact
petal pair and its possible direct genuine leaf. Therefore

    M_T+S_B+sum_(direct leaves j) alpha_j e_j=0,
    c_E.S_B<0.                                             (7)

The inequality is strict because c_E.M_T>0. This is the actual
whole-block circle sum and full root balance, not an assigned
individual-pressure sign or a split physical circle load.

## 7. Exact limits and reuse

The new local theorem has no distance premise beyond actual
D_epsilon containment at E. The graph reduction is uniform for
every original component with an intact triangle, independent of
the order or chord pattern of any remaining cyclic block. It gives
necessary complete scopes (5)--(7); it does not assert that any
such remaining block is realized or already excluded.

In particular a decorated private triangle vertex is not treated
as an intact tip. No outside leaf force is deleted from a private
star, and no source/sink body is created in place of an original
unit. All genuine direct S/D leaves and all physical completion
squares remain until a whole original contradiction applies.

The complete C3.335 closure and the uniform two-intact exclusion
have their separate frozen sources and reviews. No further coarse
cell is closed by this necessary normal form alone. The unrestricted
bound and equality classification remain open. No numerical pose,
sampling argument, Lean compilation, CI, workflow, remote mutation
or shared-ledger edit is used.
