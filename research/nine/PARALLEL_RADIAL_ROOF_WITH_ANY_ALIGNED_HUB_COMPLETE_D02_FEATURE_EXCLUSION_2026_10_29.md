# Every parallel radial roof with an aligned hub excludes both original D02 rows

Date: October 29, 2026 UTC. Author: shared_terminal continuation.

**Status: complete proposed whole-feature hand proof, frozen for separate
full independent review.** Retain the complete original six-body D02
component with circle-load set L135 or L1345, all seven positive edges,
all original forces and means, all physical masks and all three actual
completion squares. Suppose its loaded roof is the actual radial S
square, both original incoming roof normals are its inward side axis,
and at least one of the two unloaded hubs is aligned with that roof.
The entire feature is impossible in a nine-square packing.

Both positive-length and singleton hub interfaces are included. The
singleton proof derives a uniform small-tilt domain from the full
equations and an actual neighboring unit's support bound. It then
bounds the entire opposite tilted pocket and supplies the full joint
central/channel allocation by the angular measure of the two unchanged
hubs together. It does not impose individual small-vertex margins on
those hubs.

The radial roof is an explicit premise. Nonparallel roof forces and a
parallel roof with both hubs strictly tilted remain outside this source.
No complete original fine row is marked closed merely by this feature.

## 1. Entire original domain and the complete shared-side alternative

Keep nine actual interior-disjoint closed unit squares in D_R about the
unchanged O=0, with

    2<=R<=sqrt(Q), Q=1105/256,
    d=sqrt(R^2-1/4)-1, a=d-1.                        (1)

The selected positive component has the original exterior rim
01,12,23,34,45,50 and positive chord02. Use the literal actual roles

    A=0, D=2, V=1, B=5, C=3, N=4.                  (2)

The positive total circle-load set is exactly {1,3,5} or {1,3,4,5}.
Thus A,D are genuinely unloaded of full true degree three with
neighborhoods {V,D,B} and {V,A,C}; V,B,C are loaded true2; N is true2,
unloaded in L135 and loaded in L1345. Every other original force at
each named body remains. Keep all original physical circle corners,
individual nonnegative circle coefficients, singleton normal owners,
complete shared-side means and compatible pre-extraction selections.

Assume the actual roof is

    V=[d,d+1] times [-1/2,1/2],                      (3)

with both original incoming normals East and original magnitudes
mu,nu>0. Its two physical circle coefficients are equal and positive.
Its complete original moment is mu*y_A+nu*y_D=0. At least one hub is
aligned with V; name it A, exchanging the two full hub/return roles
if needed. No original force magnitude or application is equated by
that naming.

If the actual A--D intersection has positive length, the complete
source
`SHARED_HUB_PARALLEL_ROOF_COMPLETE_D02_L135_L1345_FEATURE_EXCLUSION_2026_10_29.md`
already excludes the entire feature, for all means and masks. That
theorem also derives the aligned stack itself from the positive shared
interface. It is applied only in its genuine shared-side domain here.

The only remaining actual hub contact is a singleton. The complete
local theorem
`PARALLEL_RADIAL_ROOF_ONE_ALIGNED_HUB_SINGLETON_INTERFACE_POCKET_EMPTY_2026_10_29.md`
gives, after a single reflection if necessary,

    A=[a,d] times [h-1,h], h=-H, 0<H<1/2,
    q=p_AD=(d-l,-H),
    w=(l,s), u=(-s,l), l,s>0, l^2+s^2=1,
    D=q+[0,1]w+[0,1]u,
    p_DV=q+w=(d,s-H), 0<s-H<1/2,
    p_AV=(d,y_A), -1/2<=y_A<=-H,
    mu*y_A+nu*(s-H)=0.                             (4)

The original A-to-D normal is North, with magnitude gamma>0; its
actual point q is in the relative interior of A's top side. No owner
at this singleton is presumed: that complete local theorem proves it.
Its full original equations give

    F_AB=(-mu,-gamma), S_B=(a,-H-1),
    F_DC=(-nu,gamma),
    mu*(1+H+y_A)=gamma*(1-l).                       (5)

It also proves that the entire original lower V--A--B hub pocket is
empty. The rest of this source treats the complete singleton domain
(4)--(5), including every original DC support owner and side mean.

## 2. One physical support bound forces a uniformly small tilt

Define the unchanged positive force ratio

    lambda=mu/gamma.

The actual B is supported at S_B with inward unit normal
(-lambda,-1)/sqrt(1+lambda^2). Every actual contained unit lying in
n.z>=b has b<=d. Indeed its center has norm at most d+1/2, while its
width in every unit direction is at least one. Applying this whole
physical support fact to the original B yields

    (1+H-a*lambda)/sqrt(1+lambda^2)<=d=1+a.          (6)

This uses the actual full B, not an abstract point, a new force or an
invented unit at a weighted mean. It does not use B's degree or torque.

From the full A moment in (5),

    lambda=(1-l)/(1+H+y_A)
           <=(1-l)/(1/2+H).

The strict roof endpoint s-H<1/2 gives 1/2+H>s. Therefore

    0<lambda<(1-l)/s=s/(1+l)=:tau.                 (7)

### 2.1. A single concave scalar excludes every s>=3/5

Suppose s>=3/5. Write

    c=sqrt((1+l)/2), t=sqrt((1-l)/2),
    s=2ct, tau=t/c,
    1/sqrt(10)<=t<1/sqrt(2).                       (8)

The upper radius bound gives a<1/60 and d<61/60. The function

    z -> (1+H-z/60)/sqrt(1+z^2)

has derivative -(1/60+z*(1+H))/(1+z^2)^(3/2)<0 for z>=0.
Together with (6),(7) and H>s-1/2, it follows that

    60*d>(60*s+30)*c-t
          =119*t-120*t^3+30*sqrt(1-t^2)=:f(t).      (9)

The function in (9) is strictly concave on the whole interval (8):

    f''(t)=-720*t-30/(1-t^2)^(3/2)<0.

Its minimum is therefore at an endpoint of the closed interval. Both
endpoints exceed 61:

    f(1/sqrt(10))=197/sqrt(10)>61,
    f(1/sqrt(2))=89/sqrt(2)>61.

The exact positive squared reserves are 1599 and 479 respectively.
This contradicts d<61/60. Hence

    0<s<3/5, l>4/5>s.                              (10)

This is one continuous scalar comparison, retaining the closed
s=3/5 endpoint. It is not an orientation mesh or a finite pose test.

### 2.2. Every DC owner gives H>s/2

In D's actual frame, the complete force F_DC in (5) has components

    F_DC.w=-nu*l+gamma*s,
    F_DC.u=nu*s+gamma*l>0.                           (11)

If gamma*s>nu*l, the actual DC application is the unique original
vertex q+w+u. Its full D moment about q, together with the roof force,
is nu*l+gamma*(l-s)>0 by (10), impossible. Therefore the entire
surviving DC owner domain satisfies gamma*s<=nu*l, including equality.

The original roof mean y_A>=-1/2 gives mu>=2*nu*(s-H). Substituting
this into (5), after using the roof moment, gives

    (s-H)*(1+2H)
       <=(gamma/nu)*(1-l)
       <=l*(1-l)/s=s*l/(1+l)<s/2.                  (12)

Since s-H>0, equation (12) proves H>s/2. The equality DC side-normal
feature has not been dropped; the final strictness comes from l<1.
Equations (7),(10),(12) sharpen the force-ratio bound to

    lambda<2*(1-l)/(1+s)
           =2*s^2/((1+l)*(1+s))<(10/9)*s^2.         (13)

### 2.3. Exact high-radius and small-parameter bounds

Rearranging (6) gives

    H<=sqrt(1+lambda^2)-1
           +a*(sqrt(1+lambda^2)+lambda).           (14)

If a<=0, (13) and sqrt(1+x)<1+x/2 for x>0 would give

    H<lambda^2/2<(50/81)*s^4<(2/15)*s<s/2,

where s<3/5 was used in s^4<(27/125)*s. This contradicts (12).
Consequently a>0 and d>1. The equality d=1 is excluded by the same
strict contradiction.

Using 0<a<1/60 in (14) gives

    H<1/60+lambda/60+(61/120)*lambda^2
      <1/60+s^2/54+(305/486)*s^4.

Again s<3/5 bounds the last two terms by

    s/90+(61/450)*s=(11/75)*s.

Since H>s/2, this proves

    0<a<1/60, 0<s<5/106<1/20,
    l>99/100, lambda<1/360,
    0<H<1/59.                                      (15)

For the final height bound, the preceding estimate gives exactly

    H<1/60+1/21600+61/15552000
       =259981/15552000<1/59.

The last reserve is 213121/917568000. The squared comparison for
l>99/100 has reserve 87/5000; no limiting tilt or zero mean was
silently normalized away.

## 3. Entire opposite return, including the actual shared-side mean

The two surviving signs in (11) give a complete actual DC cover.
If gamma*s<nu*l, its application is the actual vertex S=q+u.
If gamma*s=nu*l, its actual normal is u and its complete mean is

    S=q+u+eta*w, 0<=eta<=1.

The full D torque about q in this equality case is

    -nu*s+eta*(nu/s)=0,

so eta=s^2. Thus both owner alternatives are represented exactly as

    S=q+u+eta*w, eta=0 or eta=s^2.                  (16)

The zero value represents the strict vertex branch; the equality
branch retains the original point or genuine shared mean, derived
from the full equations rather than selected for convenience.

Put x_q=d-l=a+1-l. Equations (15) imply

    0<x_q<1/60+1/400=23/1200<1/50,
    -1/20<S_x=x_q-s+eta*l<1/50,
    S_y=-H+l+eta*s>29/30.                          (17)

For the upper S_x bound, eta<=s^2 and -s+s^2*l<0. For the height
bound, 99/100-1/59-29/30=113/17700>0.

The actual global normal F_DC=(-nu,gamma) is strict Northwest.
The complete minimum-support span lemma therefore gives

    max_C x<S_x+1<d, min_C y>S_y-1>-1/30.           (18)

The middle strict inequality follows from

    S_x+1-d=1-l-s+eta*l
       <=s^2/(1+l)-s+s^2*l<2s^2-s<0.

In particular C and V are closed-disjoint. No circle or degree
equation at C was shortened to prove these physical statements.

Let c_C be C's actual center. Physical circle contact gives
|c_C|>=R-1/sqrt(2)>31/24. Its half diagonal is less than17/24, so
(17) gives |(c_C)_x|<91/120. The last bound in (18) and vertical
half-width at least1/2 give (c_C)_y>7/15>0. Hence

    (c_C)_y>31/30,                                 (19)

because (31/24)^2-(91/120)^2-(31/30)^2=23/900>0.

Use the same fixed vector v=(5,14) as in the complete shared-hub
capacity proof. Since 91/120<31/40, every point of the whole C has

    v.z>1271/120-sqrt(221/2)>0.                     (20)

The exact squared reserve is 24241/14400. Also every actual C circle
corner has positive y coordinate and |x|<3/2, from (19) and the
half-diagonal bound. Consequently every one satisfies y>sqrt(7)/2.
Every physical circle corner is covered independently of its coefficient.

## 4. The entire tilted upper pocket has capacity one

Choose the unchanged actual circle-spoke corners z_V and z_C. Either
V circle corner is allowed, and every actual C circle corner is allowed.
Write P=p_DV=q+w and T=q+w+u. The upper occupied crosscut is

    z_V -- P -- T -- S -- z_C,                      (21)

closed by the upper containing-circle arc from z_V to z_C.

The first segment is in V, meeting D only at P. The next two are
actual D sides. In the strict DC vertex branch, D intersect C={S},
so the last segment meets D only at S. In the equality u-normal
branch, D is in u.z<=u.q+1 and C in the opposite half-plane. Every
C circle corner has strictly larger u-coordinate than this support:
if the C minimum is a vertex it is S, which is strictly inside the
disk; if its minimum is a side, its frame is aligned with u,w and
u.q+1>0, so every farthest corner is on its other u-side. Thus in
this branch too the last segment immediately leaves the D support
line and meets the preceding D path only at S. A genuine shared
DC interval may lie along part of T--S, but causes no self-crossing
of the displayed geometric path.

Equation (18) keeps C disjoint from V. The remaining D side pieces
meet only at T. This proves that (21) is a simple proper occupied
disk crosscut, with only its two endpoints on the containing circle.
For completeness D is physically clear: its x coordinates lie between
x_q-s and d, of absolute value at most d, and its y coordinates lie
between -H and -H+s+l<3/2. Thus all its corner norms squared are
less than d^2+9/4<R^2. The same is immediate for A.

The whole crosscut lies in v.z>0. On P--T its x coordinate is at
least d-s>19/20 and its y coordinate is positive. On T--S its
y coordinate is at least S_y>29/30 and its x coordinate exceeds
-1/20. The C strand is covered by (20). The actual V segment has
positive endpoint projections even if z_V is its lower circle
corner, because 5(d+1)-7>0 and P_y>0.

All C circle corners are strictly above sqrt(7)/2, whereas the V
circle heights are +/-1/2. The upper angular interval from z_V to
z_C lies in the same open v-positive semicircle. It is precisely
the closing arc in (21), including either original roof corner.
The complete closed loop therefore lies in that open half-plane.

Every point of the loop has norm strictly greater than1/2. This is
immediate on the D pieces from the preceding x/y bounds. Every
point of the physically boundary endpoint units V,C has norm at
least R-sqrt(2)>1/2. The outer arc has radius R>=2. Compactness gives
a strict margin. The negative-v ray from O reaches infinity without
crossing the loop, so its bounded side is disjoint from the closed
half disk and lies wholly in v.z>0.

Suppose two whole actual extras occupied that side. On the common
circle of radius5/4, those two extras and the actual C each contribute
open angular measure at least Lambda>4/5, all inside the same open
semicircle. These are the complete sharp quarter-clear arc theorem
and its exact rational constant bound, since all three units are
strictly half-disk clear. The radial V contributes in that semicircle
its explicit arc of length

    asin(2/5)+atan(5/14)>3/4.

The complete comparison and every endpoint are printed in the earlier
capacity source, Sections4 and7, at this identical actual V and vector
v. The four unchanged open unit interiors are disjoint, but their
measure sum would exceed

    3*(4/5)+3/4=63/20>22/7>pi,

impossible in one semicircle. Hence the entire tilted upper pocket
has capacity at most one.

## 5. The two actual hubs together occupy more than a third of the small circle

Put rho=1/20 and retain the same actual A,D of (4). Write

    b=w.q=l*x_q-s*H, c=u.q=-s*x_q-l*H.

The coupled strict H>s/2 gives

    b<l*a+l*(1-l)-s^2/2
      =l*a-(1-l)^2/2<a.                             (22)

Also b>-s*H>-1/1180, and
c>-(1/20)*(1/50)-1/59>-1/50. Therefore both D upper own faces
b+1 and c+1 are strictly above rho. They cannot cut this small circle.

Consider the right small-circle arc x>1/50. Its exact measure is
2acos(2/5). At every point z of it,

    w.z>l/50-s/20>173/10000>1/60>a>b,               (23)

with exact reserve 19/30000 in the middle comparison. Thus D's
minimum-w face does not exclude any of this arc. Its only remaining
own-face condition is

    u.z>c, equivalently
    y>-H+(s/l)*(x-x_q).                             (24)

Every point of the same arc with y<-H lies in int A: its x is between
a and d, and its y is strictly above -H-1. Since x>1/50>x_q, any
part of this arc not in int A or int D is therefore confined to

    -H<=y<=-H+(s/l)*(x-x_q)
          <-H+1/396.                               (25)

The last bound uses s<1/20, l>99/100 and x<=rho=1/20.
On this right arc y=rho*sin(theta) is strictly increasing with
derivative x>1/50. Consequently the total angular measure of (25)
is at most

    50/396=25/198.                                 (26)

This also covers an empty or truncated strip and all boundary
tangencies. The finitely many intersections with actual face lines
have zero angular measure. No pointwise claim about a missing triangle
in the occupied union is made; its entire possible lost arc is
explicitly bounded in (25)--(26).

The two actual open hub interiors are disjoint. Their combined measure
on the radius-rho circle is therefore at least

    2acos(2/5)-25/198>2pi/3.                        (27)

Indeed integrating 1/sqrt(1-t^2)>1 on 2/5<t<1/2 gives
2acos(2/5)-2acos(1/2)>1/5, and

    1/5-25/198=73/990>0.

This entire angular budget uses the actual tilted D and aligned A.
Neither hub was replaced by an aligned comparison square, and no
individual hub vertex was assigned a strict distance from O.

## 6. Literal original pockets and every completion square

Retain the actual exterior rim and original positive chord02. The
bounded physical faces are the triangle012 and the pentagon02345.
The entire central free union has unit capacity at most one, by the
complete chorded-hexagon central theorem. Every central extra lies
inside an actual finite enclosing ring.

The physical embedding and protected original circle spokes, together
with full component balance, give the unchanged exterior order. In
the current chart, all C circle corners are strictly above sqrt(7)/2,
all B circle corners lie below the lower hub contact height -H-1
by the reflected corner-height proof in the one-sign source, and
the complete V resultant points East. Thus the original V--A--B
route is the already proved empty lower pocket, and the original
V--D--C route has precisely the upper closure (21). In the four-load
case N's original spoke lies on the remaining C--N--B route.

More explicitly, the full component resultants are distinct and sum
to zero, so every consecutive directional gap is below pi. The two
endpoints of (21) and their resultants lie in its v-positive lift.
The corresponding consecutive V,C gap is the displayed upper one.
Every original physical corner choice stays in its own disjoint
corner interval. The lower pocket uses the reflected argument from
the accepted one-sign source. No spoke is moved in a force equation.

Every whole completion square has one central or exterior face label:
its connected open interior avoids all closed core units and occupied
center/contact paths. At weak junctions, compact inner squares retain
their labels under sufficiently small compatible routings; exhaustion
and closure retain the whole original unit. Further zero-weight
contacts only subdivide the regions. Thus the list is exhaustive:

* the central free union, capacity at most one;
* the lower hub pocket, empty;
* the upper tilted hub pocket, capacity at most one;
* in L135, the actual B--N--C channel pocket;
* in L1345, the actual direct B--N and N--C boundary-contact pockets.

In L1345 both last pockets are empty by the complete direct-boundary
contact theorem. The central and upper-pocket capacities then sum to
at most two, contradicting the actual three completion units. The
loaded N keeps its full positive circle force and is never called
an unloaded transmitter.

In L135, N is the genuine unloaded true2 original transmitter. Its
full force and torque give exactly the side or diagonal normal-channel
alternatives. The complete recovered diagonal theorem at the explicit
path

`recovered_variants/parallel_diagonal_2026_10_29/FULL_PARALLEL_RETURN_STARS_DIAGONAL_CHANNEL_EXTERIOR_POCKET_EMPTY.md`

applies to the literal true2 B--N--C channel, with one original
nonchannel force at each loaded endpoint. It makes that entire
original diagonal pocket empty, including every physical mask and
original-spoke choice. The versioned dependency resolution is the
same as in the complete shared/parallel join, not the older current
cap preimages. Again only two completion places remain.

For a side channel, the complete force-free capacity theorem gives
capacity at most one in its entire original exterior pocket. If
occupied, the complete proximity theorem gives for the original N

    dist(O,N)<1/40, all its vertices have norm>7/100. (28)

These arbitrary-endpoint-degree theorems retain the actual B,C stars
and do not require their other neighbors A,D to be boundary.

If an actual central extra E also exists, the complete enclosing-ring
restriction gives

    dist(O,E)<sqrt(2)*121/7200<1/40,
    all its vertices have norm>19/300>1/20.         (29)

Its ring-center premise is literal for all contained units:
|c|^2+|c|+1/2<=R^2 and
(91/60)^2+91/60+1/2-Q=31/57600>0. Thus every ring center has norm
strictly below91/60. The own-coordinate and strict-vertex conclusions
of the enclosing theorem give (29) exactly.

On the radius1/20 circle, (28)--(29) make each of N,E contribute
open angular measure at least2pi/3. The complete one-square proof is
Sections6 of the shared/parallel join: a nearest face at distance at
most rho/2 supplies an arc of measure at least2acos(1/2), while the
strict vertex margin also covers O on or inside the unit. This is a
radius-free one-square lemma, independent of either hub's shape.

Together with (27), the four actual disjoint open interiors A,D,N,E
would have total measure strictly above2pi on the same circle. This
contradiction excludes simultaneous central and side-channel occupation.
Their combined capacity is therefore at most one. The upper tilted
pocket has capacity at most one, and the lower pocket is empty.
All three original extras would again have to fit in capacity at
most two. This completes L135's side alternative.

Every original AD type under the stated aligned-hub radial-roof
premise, both load masks, both actual transmitter widths, every DC
owner and every closed application endpoint have now been retained
through a complete contradiction. Whole-data graph reflections
transport the theorem without independently changing a frame or mean.

## 7. Exact source pins and full review boundary

All paths are relative to research/nine. The previously accepted
sources below are used only at their complete declared interfaces.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PARALLEL_RADIAL_ROOF_ONE_ALIGNED_HUB_SINGLETON_INTERFACE_POCKET_EMPTY_2026_10_29.md | 77f0de779733353f2e791d0f2f2db54611f0930826917834c43f4146194272c4 | Entire singleton owner chart, full original equations and empty aligned-side pocket |
| RADIAL_ROOF_STACK_ONE_SIGN_HUB_POCKET_EMPTY_2026_10_29.md | fbae486a8a481dffb3fee77d41712607d5ca57fb44fe4e3f728d7b14dec62eff | Reflected original lower-pocket and all physical B circle-corner height conclusions |
| SHARED_TRIANGLE_HUBS_PARALLEL_ROOF_BOTH_EXTERIOR_POCKETS_CAPACITY_ONE_2026_10_29.md | ccc05fb4a7a8a633b9ba3abf5ad8712f71c50e2f754b75c1b5847297e5e5b1e5 | Only the complete quantitative quarter-clear arc constant, explicit actual V clipped arc and same-vector sum; the new tilted loop is proved here |
| SHARED_HUB_PARALLEL_ROOF_COMPLETE_D02_L135_L1345_FEATURE_EXCLUSION_2026_10_29.md | 315b5af77c055aff089ac86d0de430a2e1307af3e1f8454f0f3c7ad0db0dc7e8 | Whole original shared-AD alternative only; its separately printed radius-free one-square small-circle lemma in the singleton join |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original stars, actual applications, all masks, true2 widths and compatible contact conventions |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Whole-unit strict support span at the actual C support |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original physical plane embedding, protected spokes and all-extra winding assignment |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original D02 degrees, loads, exterior rim and three completion units |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Complete central free-union capacity and enclosing-ring assignment |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Entire direct touching-boundary exterior pockets and actual corner-order compatibility |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 418229089de594515bbb60da5bdcdb4cd044bd4e9396aacfa47d27de96194055 | Complete genuine side-channel exterior capacity and original full-component gap join |
| FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md | 5e8f69ad14c78b6ad99a1ba46855fc3627df5ccc1d5451f295826d2b06709abb | Original occupied N distance and strict vertex margins |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Original enclosed E own-coordinate and vertex restrictions |
| recovered_variants/parallel_diagonal_2026_10_29/FULL_PARALLEL_RETURN_STARS_DIAGONAL_CHANNEL_EXTERIOR_POCKET_EMPTY.md | 60aafee1c86633dd2a384d703425d9b60369f0b522c7ef0f85fe5eac4472b078 | Entire original true2 diagonal B--N--C exterior pocket, resolved through its explicit exact analytic variant bundle |

The new complete scalar narrowing, every DC owner, full tilted-pocket
loop, all-extra assignment and coupled small-circle measure require
their own full independent review. Source pins do not substitute for
that review. The explicit radial-roof premise is not silently replaced
by an unpublished general star classification.

The displayed rational reserves were independently checked with exact
fractions. All mathematical comparisons are proved over their complete
continuous domains. No numerical pose search, angle mesh, new finite
packing certificate, original force deletion, mean movement, Lean
compilation, CI, remote write, merge or authoritative ledger edit is
used in this proof.
