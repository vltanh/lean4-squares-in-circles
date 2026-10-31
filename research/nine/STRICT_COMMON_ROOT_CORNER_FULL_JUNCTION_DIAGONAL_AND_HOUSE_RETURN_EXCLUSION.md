# A strict common root corner forces the full junction diagonal and excludes both house-return branches

Date: October 29, 2026 UTC. Author: broad_s_families continuation.
Exact published comparison: a5f3922a9c12830b76f2a7ee9dd4dbf1024f85b5.
Actual comparison Git tree: 2617ed629140d69171c86bfa68b0ee5784ab8c8c.

**Status: complete proposed hand theorems, frozen for separate full
independent review and root adoption.** This source excludes the entire
original owned-leaf TC feature in which the actual AD and AT normals are
both strict (-u,+v) directions at the same original root corner. It retains
the parallel and nonparallel original C force rows, all original D/T
owners, all actual side means and coincidences, and every physical T
circle mask and individual coefficient. No whole original TC closure is
claimed.

The principal broad export is radius-free: a strict host-corner contact
shared with a third actual unit is a vertex of each unit, and the complete
unloaded three-force star sends its third support to the opposite vertex.
The original means are not moved to the shared corner. A separate local
quadrant argument then supplies a whole-unit halfplane, rather than an
assertion about its center or force direction.

## 1. A strict host corner shared by three actual units

Let A,D,T be three actual unit squares with pairwise disjoint open
interiors and a common point S. Because A has interior points arbitrarily
near S, the point S cannot lie in the open interior of D or T. Suppose
S is a vertex of A and there is
an actual separating support normal from A to D that strictly exposes
that A vertex. If S were in the relative interior of a D side, D's local
open tangent sector at S would be a halfplane. A's local open tangent
sector is a right-angle quadrant in the opposite halfplane.

Strict exposure means both bounding rays of that A quadrant are strictly
inside the opposite halfplane. After removing the closed A quadrant, the
two remaining angular intervals in that halfplane each have width
strictly less than pi/2. The local open tangent sector of T has width at
least pi/2 and is connected. It can occupy neither interval while staying
disjoint from the open tangent sectors of A and D. This is impossible.

Thus S is an actual vertex of D. If the actual A-to-T normal also strictly
exposes S in A, the same argument, with D and T interchanged, proves that
S is an actual vertex of T as well. This statement includes an arbitrary
contact set between D and T; their common point S need not be their
original mean or their only common point.

Assume now the original positive AD and AT contacts carry the prescribed
strict vertex/vertex convention: at a physical point-only contact between
two vertices, the unchanged normal strictly exposes the vertex in both
units. Since A's strict support is the singleton {S}, both intersections
A intersect D and A intersect T are exactly {S}. Their prescribed normals
therefore strictly expose S in D and T respectively. Nothing is reselected
after the original multipliers or means have been fixed.

### 1.1. The full unloaded junction has an opposite-vertex third support

In addition let D have exactly its three original positive pair neighbors
A,T,C, no circle load, and its complete original vector balance. The
actual positive DT contact is retained, with its original normal G/|G|
and original full mean F. Because S belongs to D intersect T, S belongs
to the same original supporting face of D as F. This is true even when
F is a different point of a nondegenerate common side.

Use the actual two inward unit side axes j,k of D at S. The unchanged
D-to-A force has strictly negative projections on both j and k, by the
prescribed strict exposure just proved. The unchanged D-to-T force has
nonpositive projections on both, because its maximum support includes S.
Both forces have their original positive magnitudes. The full D3 balance
therefore makes the D-to-C force have strictly positive projections on
both axes. Its actual support is the unique opposite vertex:

    Q=P_DC=S+j+k,
    |Q-S|^2=2.                                      (1)

This is a full-star statement. It remains valid when F=S, when F is
either endpoint of a shared side, and throughout the original open
mean interval. No torque or force is dropped, no normal is changed,
and no artificial DT point is substituted for its original mean.
No degree or boundary status is imposed at A,T,C beyond the physical
and strict-contact premises explicitly stated here.

## 2. A whole returned-unit halfplane from one actual diagonal

Suppose, in orthonormal coordinates translated only for this local
geometric statement, that

    A=S+[0,1](1,0)+[0,1](0,-1),
    Q-S=(-K,-W), K>1, W>0, K^2+W^2=2,             (2)

and Q is the actual opposite vertex of D from S. Suppose T is an actual
third unit having S as a vertex, with interior disjoint from A and D.
No force or circle premise is needed in this section.

From (2), 0<W<1<K and K>W. The actual inward axes of D are, up to
interchange,

    j=(-c,s), k=(-s,-c),
    c=(K+W)/2, s=(K-W)/2,
    c>s>0, c^2+s^2=1.                            (3)

Write theta=arg(j), so 3*pi/4<theta<pi. The open local tangent quadrant
of D occupies (theta,theta+pi/2), while A occupies (3*pi/2,2*pi).
The angular complement of their closed quadrants consists of two
intervals: one from 0 to theta, and one from theta+pi/2 to 3*pi/2.
The second interval has width pi-theta<pi/4, so it cannot contain the
open right-angle tangent quadrant of T. Thus T's entire right-angle
quadrant is in the closed first interval [0,theta].

In particular both actual inward axes of T have nonnegative vertical
components. Since T is their unit parallelogram from S, the conclusion
holds for its entire closed physical unit:

    T subset {Y_y>=S_y}.                          (4)

Weak equality of a T edge with a bounding ray is allowed. No gap between
the closed units, no generic angular separation and no mean perturbation
has been assumed.

### 2.1. An explicit opposite-corner radius bound

Use the unchanged circle origin O=0 and suppose S=(epsilon,V), with
0<=epsilon<V. For any actual unit T with S as a vertex and (4), choose
its actual inward axes as

    e=(C,S0), f=(-S0,C), C,S0>=0, C^2+S0^2=1.

Its opposite actual corner is Z=S+e+f. Consequently

    |Z|^2
      =epsilon^2+V^2+2+2*epsilon*(C-S0)+2*V*(C+S0)
      >=epsilon^2+V^2+2+2*(V-epsilon)*(C+S0)
      >=(V+1)^2+(1-epsilon)^2.                    (5)

Both aligned endpoints C=0 or S0=0 are included, as is every intermediate
orientation. This is an actual corner of T, whether or not it is a
physical circle corner or has a circle coefficient.

## 3. Exact original TC feature and unchanged full stars

Keep all nine actual units and the literal selected original component

    AT,DT,AD,AB,BC,CD,AL,
    true A4,D3,B2,C2,T2,L1,
    positive circle loads precisely T,C,L.

B is the original unloaded transmitter, D the original unloaded full
degree-three junction, and L the genuine radial S leaf. No BD edge is
invented. The other three arbitrary actual units remain present.

The complete original reduction and whole upper-mean union leave this
owned-leaf chart:

    R^2=(2+epsilon)^2+1/4<=1105/256,
    d=1+epsilon, 0<epsilon<1/60,
    epsilon<q<3/8, V=1-q,
    u=(-a,t), v=(-t,-a), a,t>0, a^2+t^2=1,
    a=(q^2-epsilon^2)/(q^2+epsilon^2),
    t=2*epsilon*q/(q^2+epsilon^2),
    A=[epsilon,d]u+[-q,V]v,
    L=[d,d+1]u+[-1/2,1/2]v,
    q*t=epsilon*(1+a), epsilon*t=(1-a)*q.        (6)

The unchanged world chart is

    B=[epsilon,d] times [z,z+1],
    C=[d,d+1] times [-1/2,1/2],
    P_AB=(epsilon,q), P_BC=(d,q),
    z<=q<=z+1, max_D y<=z<=q.                   (7)

Unless expressly labeled world, all following coordinates are in the
proper actual (u,v) frame about the same circle origin O. The feature
treated by this source is exactly

    S=P_AD=P_AT=(epsilon,V),
    F_AD=(-rho,omega), rho,omega>0,
    F_AT=(-eta,beta), eta,beta>0.                 (8)

These are the original forces from A into its actual neighbors. Their
directions are both strict (-u,+v) at the same actual A vertex. No D or
T owner is prescribed. The actual original DT mean is arbitrary.

Let mu>0 be the original AB and BC magnitude, retained by the true B2.
The real leaf force is kappa*u, kappa>0. The complete A4 vector and
origin-moment equations give

    omega+beta=mu*t,
    kappa=mu*a+rho+eta,
    V*(rho+eta)=mu*a*q.                         (9)

Indeed the AB moment is -mu*epsilon*t-mu*a*q, the two corner moments
sum to epsilon*(omega+beta)+V*(rho+eta), and the AL moment is zero.
Every original positive term remains in (9).

The full physical-C theorem keeps both positive circle coefficients and
the complete original alternative

    parallel: g_world=East, Q_world=(d,y),
              -1/2<=y<0, mu*q+nu*y=0;

    nonparallel: (g_world)_x,(g_world)_y>0,
                 Q_world=(d,-1/2), nu>0.         (10)

Here nu*g is the original D-to-C force. The actual C remains loaded
degree two; its radial physical shape is not a leaf equation.

### 3.1. Uniform physical strict-AD tilt bound

The world coordinates of the unchanged common corner are

    S_world=(epsilon-t,q-a).                    (11)

Both rows of (10) give Q_world=(d,y) with y>=-1/2. Thus the actual
two points S,Q of D have horizontal difference 1+t. Its diameter gives
t<=sqrt(2)-1<5/12; the latter strict inequality follows from
(17/12)^2-2=1/144. Therefore

    a^2=1-t^2>119/144>(9/10)^2,
    a>9/10.                                     (12)

The squared reserve is 59/3600. In particular

    Q_y-S_y>=a-q-1/2>9/10-3/8-1/2=1/40>0.      (13)

So equality t=sqrt(2)-1 is impossible as well. This reproduces the
needed bound directly from the actual two D points, without importing
any theorem about the unproved other original owner features.

## 4. The whole parallel-C branch contradicts actual properness

Let G be the original D-to-T force and let F_T be the full original
positive physical circle resultant at T. The complete original stars give

    (rho,-omega)+nu*g+G=0,
    F_T=(-eta,beta)+G,
    (F_T)_u=-(rho+eta)-nu*g_u,
    (F_T)_v=omega+beta-nu*g_v.                   (14)

In the parallel row, g=(-a,-t) in the root frame. From its actual C2
moment and the full mean interval in (10),

    nu=mu*q/(-y)>=2*mu*q.

Together with (9), and V>5/8>1/2, this gives

    (F_T)_u=a*(nu-mu*q/V)>0,
    (F_T)_v=t*(mu+nu)>0.                         (15)

The two incoming T forces cannot be parallel: if G were parallel to the
strict (-eta,beta), their nonzero full resultant would be collinear with
that vector, whose coordinate signs are opposite. It cannot be the
strict positive-positive vector (15). No separate parallel-star exit is
being imported here.

If the original AT and DT applications coincide, the complete
one-application theorem 3808 gives q_T=S=s0*F_T, s0>0. Otherwise the
two nonparallel original forces have the complete boundary-free proper
concurrence

    q_T=s0*F_T=S+ell*(-eta,beta),
    s0>0, ell>=0.                               (16)

The coincident case is the same expression with ell=0. Both zero-ray
endpoints remain; no inside-T assertion is used for a physical two-corner
mask. All actual circle coefficients, including a zero individual one,
stay in F_T. The strict-high interval is contained in
sqrt(2)<R<1+sqrt(2), so the entire stated radius scope of 3808 applies.

Equation (16) gives (q_T)_u<=epsilon and (q_T)_v>=V. As both components
of F_T are positive, it follows that

    V*(F_T)_u<=epsilon*(F_T)_v.                  (17)

Substitute (15), then use both exact leaf identities in (6). Inequality
(17) becomes

    nu*(a*V-epsilon*t)<=mu*(a*q+epsilon*t),
    nu*(a-q)<=mu*q.                              (18)

But (12) and q<3/8 give a-q>21/40>1/2. Hence

    nu*(a-q)>nu/2>=mu*q,

contradicting (18). This excludes the entire parallel-C branch, all
original D/T owners, every actual parallel-C mean and all T physical
masks, including the coincident-application endpoint.

## 5. The whole nonparallel-C branch contradicts one actual corner

Now Q_world=(d,-1/2). Because both AD and AT are strict contacts at S in A,
the complete three-unit local geometry of Section 1 applies. The original
prescribed normals make S a strictly exposed D vertex. The actual DT
support contains S, regardless of where its full original mean lies.
The complete D3 consequently forces (1), with no D-owner hypothesis.

In world coordinates the same opposite-vertex equality is

    2=(1+t)^2+(a-q-1/2)^2.

Set k0=q+1/2, so 1/2<k0<7/8. Expanding with a^2+t^2=1 gives

    t=a*k0-k0^2/2.                              (19)

By (12), the right side is strictly greater than
(9/10)*k0-k0^2/2. That quadratic is strictly increasing on the whole
closed interval [1/2,7/8], because its derivative is at least
9/10-7/8=1/40>0. Therefore

    t> (9/10)*(1/2)-(1/2)*(1/2)^2=13/40.

The unchanged genuine-leaf identity q*t=epsilon*(1+a), with a<1,
epsilon<1/60, now yields

    q< (1/60)*2/(13/40)=4/39,
    V=1-q>35/39.                                (20)

Write the same actual Q-S in root coordinates:

    Q-S=(-K,-W),
    K=a+t*(q+1/2),
    W=V+t*d-a/2>1/8.                            (21)

The last inequality uses q<3/8, d>0 and a<1. Also

    K-1=t*(q+1/2-t/(1+a))>0,                    (22)

since q+1/2>1/2 while (12) gives
t/(1+a)<(5/12)/(19/10)=25/114<1/2. Equality (1) becomes
K^2+W^2=2. Thus every geometric premise of Section 2 is satisfied by
the actual A,D,T. In particular the entire closed actual T satisfies
v>=V. This conclusion concerns the whole physical unit, not only a
force, center, contact segment or boundary corner.

At its actual vertex S=(epsilon,V), equation (5) supplies an actual T
corner with

    |Z|^2 >=(V+1)^2+(1-epsilon)^2
           >(74/39)^2+(59/60)^2
            >1105/256>=R^2.                     (23)

The final exact reserve is 2441399/9734400>0. This contradicts containment
of that actual corner. It does not require that corner to carry a circle
coefficient, or even that it be T's farthest corner. No force or mean
subdivision remains in this branch.

Sections 4 and 5 exhaust the actual C force cover and prove the entire
stated strict-common-corner feature (8).

## 6. Exact operative inputs, contribution and remaining scope

All complete inputs below were read at the stated exact bytes. The new
local tangent-sector, full-junction diagonal, whole-halfplane and corner
bound arguments are printed completely in Sections 1--2 and 5.

| Complete input | SHA256 | Literal use |
| --- | --- | --- |
| GENUINE_S_HOUSE_TC_TILTED_RADIAL_C_COMPLETE_ASSEMBLY.md | 6f5634d78b0e217f91898852e721aedbc06a09c4398528c86753f29e4aaf89c2 | Exact original residual, true graph/degrees, both actual leaf charts and C force rows |
| ALIGNED_RADIAL_C_OWNED_LEAF_WHOLE_UPPER_MEAN_OWNER_UNION_2026_10_29_CONTINUATION.md | ea076feb168f61c9928c2e3d35d6e36e736af04d2068c4f64aac16c32656f334 | Entire original q>=3/8 exit, used only to identify the complementary q<3/8 interval |
| HIGH_SUPPORT_SIDE_CHANNEL_TOUCHING_RETURN_FORCES_TWO_POSITIVE_CIRCLE_CORNERS.md | 2a6f8da941de756abbea77f5c9aac75e5225968efdf278c683295b0dec900143 | Complete actual C force/mask cover, both positive original coefficients and original parallel mean equation |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Entire actual one-application and two-distinct-nonparallel positive radial/proper-ray alternatives, with both physical masks |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | The prescribed strict point-only vertex/vertex convention retained on the same original selected certificate; no new selector or thinning operation |

The author discovered the new local common-corner diagonal argument and
both complete original branch contradictions. The strict-AD tilt estimate
in Section 3.1 is rederived here; its earlier occurrence in the accepted
be0af78e support-face source is provenance, not an extra mathematical
input. The separate d92ec805 near-side theorem, the separate a813f3cc
parallel-T theorem and the separate selected AB-endpoint corollary are not
operative inputs. No derivative or bound from their proposed or accepted
proofs has been silently transferred into this source.

This theorem does not exclude the A-owned AD-side feature, the A-owned
AT=-u feature treated separately by d92e, the +v/outer (+u,+v) AT returns,
or the upper-adjacent genuine-leaf chart. No unproved three-extra allocation
is used. The whole original TC.S family and other stated feature classes
remain open until separately proved and joined over their complete cover.

All original force equations, positive magnitudes, physical contacts,
original means, physical masks, individual coefficients, all nine units
and the original selected certificate remain. No geometric certificate,
finite pose/angle partition, Lean/Lake, CI, original flag/count edit,
certificate retirement or remote action was performed. Separate complete
independent mathematical review and root adoption are required before
these exact proposed bytes are accepted.
