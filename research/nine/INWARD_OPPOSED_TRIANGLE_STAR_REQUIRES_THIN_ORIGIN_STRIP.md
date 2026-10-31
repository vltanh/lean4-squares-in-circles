# An inward opposed triangle star must lie in the thin origin strip

Date: October 28, 2026 UTC. Author: s_family.

**Status: complete proposed uniform hand reduction, submitted for full
root and separate independent review. No original fine or coarse gate
is changed.** This strengthens the existing opposed-moment star theorem
when the two nonexceptional neighbors physically touch: a merely negative
exceptional support already forces the actual unloaded unit to meet the
closed epsilon disk. Both missing-coordinate cases and the entire far
single-interval case are excluded. The stated thin strip remains open.

Retain the same actual interior-disjoint closed unit squares, their
unchanged containing circle and all original physical forces and means,
with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60.

No new normal selection, load, force or physical contact is introduced.

## 1. Exact full-star hypotheses and conclusion

Let U have zero total circle force and exactly three original positive
pair neighbors X,V,W. Write its actual outward unit normals as n,g,k,
its original applications as p,q,z and their positive magnitudes as
lambda,mu,nu. Suppose

    lambda*n+mu*g+nu*k=0,
    lambda*det(p,n)+mu*det(q,g)+nu*det(z,k)=0,

    h_U(n)=p.n<0,
    det(p,n)>0,
    det(q,g)<0, det(z,k)<0.                              (1)

Suppose further that the distinct actual units V,W physically touch.
That contact need not be positive. There is no degree, force or circle
load premise at X,V,W. U may initially have physical circle contacts
of zero weight; zero total circle force alone is not used as clearance.

**Theorem.** After a proper choice of U's own orthonormal axes, its
actual square must have the form

    U=[a,a+1] x [b,c],
    0<a<=epsilon, b<=0<=c, c=b+1.                       (2)

In particular dist(O,U)=a<=epsilon, epsilon>0, and U is physically
circle-clear. The same conclusion holds when all three determinant
signs in (1) are reversed, by reflecting the whole physical configuration.

The exceptional actual feature in (2) is either West at (a,y), with
0<y<=c, or strict Northwest at (a,c), with n=(-u,v), u,v>0 and
cv<au. Every original side-mean endpoint is retained. Equation (2)
is a necessary reduction, not an exclusion of its entire thin domain.

## 2. Two elementary physical bounds and one occupied-center cap

Every contained unit has center C with

    |C|^2+|C|+1/2<=R^2,
    |C|<=d+1/2<91/60=:M.

Its half-width in any unit direction f is at least 1/2. Hence an actual
contained unit beyond a support f.x>=h requires

    C.f>=h+1/2, h<=d.                                 (3)

Also an actual common support point Q belongs to that neighbor and
satisfies |Q-C|<=1/sqrt(2).

### 2.1. A support above one cannot carry a point of squared norm at least two

Suppose an actual neighbor beyond f.x>=h=Q.f had h>1 and |Q|^2>=2.
Equation (3) gives h<61/60 and C.f>3/2. Thus

    |Q.Jf|>sqrt(3479)/60,
    |C.Jf|<sqrt(181)/60,
    |Q-C|>(sqrt(3479)-sqrt(181))/60
           >(58-14)/60=11/15>1/sqrt(2).

This contradicts Q in the actual unit neighbor. The entire normal
cone, all side means and their endpoints are included in this cap.

### 2.2. Two different units cannot both be beyond the same support above one

If two distinct contained units both lie in x>=h with h>1, their centers
both have x>3/2 and norm<M=91/60. They lie in the same open rectangle
with horizontal width 1/60 and vertical height 2sqrt(181)/60. Its
squared diameter is

    [1+4*181]/3600=29/144<1.

But distinct interior-disjoint unit squares have center separation at
least one, by their disjoint open incircles of radius 1/2. This proves
the occupied-center cap without any force or circle-load hypothesis.

## 3. The two missing-coordinate case is entirely impossible

The strict support h_U(n)<0 puts O outside the actual closed U. If
both own intervals miss zero, a proper quarter-turn of U's own frame
puts them in the first quadrant:

    U=[a,a+1] x [b,b+1], a,b>0.

No ordering between a and b is imposed. The whole first-quadrant far
corner (a+1,b+1) has squared norm greater than two and every outward
normal there has support greater than one. Section 2.1 excludes all
actual contacts at that corner, including its axis-normal endpoints.

The exceptional support and positive determinant in (1) leave exactly
West, strict Southwest at (a,b), or strict Northwest at (a,b+1).
North and East have positive support. South and strict Southeast have
negative determinant. The Northeast cone has positive support. These
statements cover every feature and actual mean.

### 3.1. Southwest and West exceptional normals

For a strict Southwest exceptional normal, every negative-determinant
other feature has y-component at most zero. The top side and Northwest
corner have positive determinant; the Northeast corner is excluded
above; West has determinant equal to its strictly positive height.
The full vertical force sum is therefore strictly negative, impossible.

For a West exceptional normal, full vertical balance similarly makes
both other normals horizontal. Their negative determinants require
both to be East. Both distinct original neighbors would lie beyond
x=a+1>1, contradicting Section 2.2. All original East-side means
are retained in this contradiction.

### 3.2. Northwest: complete negative-moment feature cover

Write

    c=b+1>1, p=(a,c), n=(-u,v), u,v>0,
    -a*u+c*v<0.                                      (4)

The only remaining negative-determinant other features are East,
South, strict Southwest and strict Southeast. The Northwest cone and
top side have positive moment, West has positive moment, and the
Northeast corner is excluded by Section 2.1.

First suppose neither of the two other normals is East. Full horizontal
balance requires one strict Southeast normal. Name it g=(f,-t),
f,t>0, at q=(a+1,c-1). Its other actual triangle port is South,
Southwest or Southeast. The following uses the original magnitudes
and means throughout.

* If k=South at z=(x,c-1), a<=x<=a+1, then torque about p gives
  mu*(f-t)=nu*(x-a)>=0. Full balance gives lambda*u=mu*f and
  lambda*v=mu*t+nu. Since x-a<=1, nu>=mu*(f-t), so v>=u.
* If k=(-s,-w) is strict Southwest at z=(a,c-1), then torque about
  p gives nu*s=mu*(f-t). Full horizontal balance then gives
  lambda*u=mu*t, while vertical balance gives lambda*v=mu*t+nu*w.
  Hence v>u.
* If both other normals are strict Southeast at the same actual root
  vertex, torque about that vertex gives lambda*(u-v)=0. Hence u=v.

These three cases all imply v>=u. Equation (4) then gives a>c>1.
The actual corner (a+1,c) would have squared norm greater than five,
contrary to U's original containment in the target disk, whose squared
radius is 1105/256<5.

It remains that one other force is East. The other cannot also be
East, since the exceptional vertical component is positive. Because
V,W physically touch, the owned-axis triangle theorem applied to U's
East normal makes the remaining normal's x-component nonnegative.
It is therefore South or strict Southeast, by the preceding feature
cover. Write the actual East mean as

    q=(a+1,y), b<=y<=c, delta=c-y in [0,1].

If the remaining force is South at (x,c-1), full balance and torque
about p give

    mu=lambda*u, nu=lambda*v,
    mu*delta=nu*(x-a),

and hence delta<=v/u. If it is strict Southeast (f,-t) at
(a+1,c-1), those same complete equations give

    lambda*u=mu+nu*f, lambda*v=nu*t,
    mu*delta=nu*(t-f).

Using delta<=1, they imply

    lambda*u*delta=nu*(t-f)+nu*f*delta<=nu*t=lambda*v.

Thus in every actual mean and axis limit,

    delta<=v/u<a/c,
    y=c-delta>c-a/c>1-a.                              (5)

If a<=1, then y>1-a>=0, and the actual East application satisfies

    |q|^2>(1+a)^2+(1-a)^2>=2.

If a>1, already q_x>2, so |q|^2>4. Its actual East support is
a+1>1 in either case. Section 2.1 contradicts this actual contact.
This excludes the entire East alternative and completes the whole
two-missing-coordinate case, without a lower bound on either a or b.

## 4. The one missing interval outside epsilon is entirely impossible

Only one own interval now misses zero. A proper own-frame rotation
gives

    U=[a,a+1] x [b,c], a>0, b<=0<=c, c=b+1.

Suppose a>epsilon. Then a+1>1+epsilon>=d, so no actual East-normal
neighbor exists by (3).

The negative exceptional support forces n_x<0. A North or South normal
has nonnegative support. A normal with nonnegative x-component has
nonnegative support because its support y-coordinate has the same sign
as its y-component. A strict Southwest exceptional normal would have
determinant -a*v+b*u<0. Therefore the exceptional feature is exactly
West at a positive-height actual mean or strict Northwest at (a,c).

There is no negative-moment actual contact in the Northeast cone.
For a strict Northeast normal (f,t), a negative moment at (a+1,c)
would give (a+1)t<c*f and therefore

    h_U(f,t)=(a+1)f+c*t>(a+1)/f>=a+1>d.

Its axis endpoints are the already excluded East normal and the
positive-moment North normal. This proves the full feature exclusion.

### 4.1. West exceptional normal

All other negative-moment features have y-component at most zero:
the top and Northwest features have nonnegative moment, and the only
remaining positive-y cone was just excluded. Full vertical balance
therefore makes both other normals horizontal. East is impossible,
and three positive West forces cannot sum to zero. This excludes every
original West mean, including its endpoint values allowed by (1).

### 4.2. Northwest exceptional normal and the only possible dangerous port

Put

    p=(a,c), n=(-u,v), u,v>0,
    -a*u+c*v<0,
    w=(v,u), w.n=0.

Every other possible negative-moment feature is West, South, Southwest
or Southeast. West, South and Southwest all have strictly negative
w-projection. The full force equation dotted with w therefore requires
one strict Southeast force g=(f,-t) with

    f,t>0, t/f<=v/u.                                  (6)

It acts at q=(a+1,c-1). Since V,W physically touch, the other actual
triangle force cannot be West: the owned West axis would require
its dot product with g to be nonnegative, whereas it is -f<0.
Thus that force is South, Southwest or Southeast.

The full force/torque identities in Section 3.2 apply verbatim at the
same original points, regardless of the sign of c-1. They imply v>=u;
in the South/Southwest cases they also give f>=t. In the Southeast
case u=v, so (6) itself gives f>=t. The strict negative support then
implies a>c, since c>=0.

Write f=cos(theta), t=sin(theta), 0<theta<=pi/4. The actual dangerous
support is

    h_U(g)=(a+1)cos(theta)+(1-c)sin(theta).

Here 0<=c<=1, so this positive function is concave on [0,pi/4]. Its
minimum is at an endpoint. But both endpoint values exceed d:

    a+1>d,
    (a+2-c)/sqrt(2)>sqrt(2)>d.

This violates the actual-neighbor support bound (3). The entire strict
Northwest case, including equal slopes and all South-side means, is
therefore excluded. This completes the one-missing-interval case a>epsilon.

## 5. Exact residual strip and physical-clearance consequence

The negative support in (1) already excludes O in the closed U.
Section 3 excludes both missing intervals. Section 4 excludes a>epsilon
when exactly one interval misses zero. The sole possible geometric
domain is therefore exactly (2).

In that chart the same elementary support and determinant signs used
in Section 4 leave only West at positive height or Northwest at (a,c)
for the exceptional force, with cv<au in the strict Northwest case.
No near-side mean is centered or replaced.

Since 0<a<=epsilon, the residual domain requires epsilon>0 and hence
R^2>17/4. Moreover U has an actual point at distance a<=epsilon.
If U also physically touched the circle, those two actual points would
be separated by at least R-epsilon>47/24>sqrt(2), exceeding its unit
diameter. Thus U is physically circle-clear, not merely unloaded.

This theorem does not exclude the residual strip, does not assign it to
a chosen body without a literal caller, and does not derive opposed
moment signs without the caller's own complete torque and topology.
In particular a small negative exceptional support alone does not permit
one to omit the hypotheses on the other two original moments.

## 6. Direct operative dependencies and comparison

The center/support bounds and the forbidden corner cap were reconstructed
in full above; they are the same elementary physical inequalities used
in the accepted degree-free moment-port and opposed-star sources.
The only nontrivial geometric imported implication is the owned-axis
triangle theorem:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | If an actual U-to-V normal is U-owned and U,V,W physically form a triangle, its dot product with the unchanged U-to-W normal is nonnegative |

The former general opposed-star theorem in
`UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md`
assumes exceptional support below -epsilon and permits arbitrary degree
and unrelated neighbors. The present theorem instead assumes support
merely below zero, true degree exactly three and actual contact between
the other two neighbors. It concludes the precise near-origin strip.
These are complementary scopes; neither is silently substituted for the
other.

All three original force magnitudes and applications, every shared-side
mean and endpoint, every physical circle mask and zero weight, and all
other physical units remain. No additional computational certificate,
angle mesh, pose search, Lean compilation, CI or remote write was used.

## 7. Literal lower-house TDC.D near-body consequence

Keep exactly the original house positive edges and real leaf edge

    AT, DT, AD, AB, BC, CD, BL,

with a genuine D leaf L at lower root B and positive block circle loads
exactly T,D,C. Thus the unchanged true degrees are

    B3, A3, D3, T2, C2, L1.

The genuine D geometry puts O in int(B). The actual A is unloaded but
is not initially assumed physically clear. Let n_BA be its original
normal from B to A and let h=h_B(n_BA)>0. Positivity here comes from
O in int(B), not from a new support choice.

**Original-family conclusion.** The actual A must satisfy

    A intersects closed D_epsilon.                      (7)

Consequently epsilon>0, A is physically circle-clear, and every one of
the other seven original units, excluding exactly B and A, satisfies

    dist(O,E)>3/125>sqrt(2)*epsilon.                    (8)

The whole original fine family M6.B5L.HOUSE.LOWER.LTDC.D remains open;
(7)--(8) are additional necessary physical restrictions on its full
original domain, retaining the weak distance endpoint in (7).

### 7.1. The complete contradiction if A avoids the small disk

Suppose A avoids closed D_epsilon. The private graph after deleting
B,L is exactly the actual triangle A--T--D--A plus the edge D--C.
All four of its actual units then avoid closed D_epsilon: this is the
supposition for A, and T,D,C are physical boundary units, whose point
norms are at least r=R-sqrt(2)>11/20>epsilon.

Every original private edge has nonzero moment. Indeed a radial
application p=t f, t>0, would have an inner unit with a missing own
interval [a,a+1], a>0, and an actual outer neighbor requiring t<=d.
The radial support puts its corresponding coordinate at a+1, so
t>1 and a<=t-1<=epsilon. Two missing intervals give t>sqrt(2)>d;
one gives an actual point (a,0) in the inner unit and closed D_epsilon.
Either contradicts its avoidance. An application at O is also excluded.

Orient each actual private edge by its positive original origin moment.
A directed private cycle winds positively about O by the full
degree-free port theorem. At every cycle vertex both of its actual
cycle neighbors avoid closed D_epsilon, so the theorem's complete
neighbor premises hold literally. In the same compatible physical
embedding, such a Jordan cycle also encloses c_B: the whole compact
segment O--c_B lies in int(B) and avoids all its private units. The
actual B--L edge would then trap the boundary leaf L inside that cycle,
contradicting protected exterior access. Weak junctions are routed
within the actual positive O clearance, as in the original theorem.

The private orientation is therefore acyclic. It has a distinct source
and sink. Neither T nor D can be either, since every original pair force
at each is private and their full original origin moments sum to zero.
Their actual physical circle atoms also have zero origin moment. Thus
the extrema are exactly A,C, in opposite roles.

At A, the actual AT and AD moments have the same strict sign. Its full
original A3 torque makes the actual AB moment nonzero with the opposite
sign. Its reversed exceptional support is

    h_A(-n_BA)=-h<0.

The two other actual neighbors T,D physically touch by the original
positive TD edge. Thus all hypotheses (1) hold for this true unloaded
A3 star, after one whole reflection if needed. Sections 1--5 force
dist(O,A)<=epsilon, contradicting the supposition that A avoids the
closed disk. This proves (7) on the whole original domain.

This argument does not presume that a small support makes A near O.
The new near-body fact follows from the full graph, winding, original
torques and the strengthened actual triangle-star theorem.

### 7.2. Physical clearance and the seven actual far units

Every actual unit distinct from B avoids O, because O is open in B.
Hence (7) forces epsilon>0. If A had a physical circle point, that point
and its actual point in closed D_epsilon would have distance at least
R-epsilon>47/24>sqrt(2), contradicting A's unit diameter. This proves
physical clearance directly from (7), without the radius-two lower-bound
theorem or a claim based only on its zero multiplier.

Now epsilon<1/60<3/125, so A meets closed D_(3/125). The accepted uniform
theorem `D_LEAF_ROOT_AT_MOST_ONE_OTHER_UNIT_IN_THREE_125_DISK.md`, applied
to the real D root B, says at most one other actual unit can meet that
closed fixed disk. A is already one, so every original unit E distinct
from both B and A avoids it. Compactness gives the first strict inequality
in (8). The second follows from sqrt(2)<36/25 and epsilon<1/60, since
(36/25)/60=3/125.

All seven units are actual: T,D,C,L and the three arbitrary completing
squares. No positive-component or load premise is put on the three
completing units. Every full original force and side mean is retained.

The established D-root clear-neighbor theorem would give the same
physical-clearance conclusion because B's other nonleaf neighbor C is
boundary. That older route explicitly uses the same-nine R>2 theorem.
It is **not** an operative dependency here: the direct diameter proof
above supplies clearance on the full stated radius window. No W.3
five-charge or analytic-measure certificate is imported into this join.

### 7.3. Exact new join dependencies and retained frontier

| Source | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine D root contains O openly; real leaf and original graph moments |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Only Sections 2--3: complete directed-cycle winding when all cycle units avoid closed D_epsilon |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | One common physical embedding, weak-junction routing and protected boundary access |
| D_LEAF_ROOT_AT_MOST_ONE_OTHER_UNIT_IN_THREE_125_DISK.md | 34385a647c1889564b3423ecfff03a7a75747275e45f68346c3f8a9f06abfaaf | Whole fixed-disk near-unit limit at the actual genuine D root, all arbitrary original units included |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original lower-house TDC.D graph, loads, true degrees and retained nine-body contract |

The earlier small-support reduction still applies, including its strict
high-radius chart, h<=epsilon, shallow B margin and unchanged C-normal
sign. Equations (7)--(8) strengthen that domain; they do not exclude it.
The actual A is not assigned the local chart (2) solely from (7): the
opposed moment pattern was derived under the contradicted far-A
supposition and has not been proved for every remaining near-A member.
No fictitious A--C contact, degree reduction, chosen application or
closed original checkbox follows from this partial join.
