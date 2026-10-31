# An occupied actual side cap forces its transmitter to meet a tiny disk about the origin

Date: October 26, 2026.

**Status: accepted complete whole-channel theorem, both original four-load
C6 joins, and the entire simple-C6 load-cover assembly, after full-source
and original-domain reviews in
REVIEW_SIDE_OCCUPIED_CAP_AND_COMPLETE_C6_ROOT_2026_10_26.md and
REVIEW_SIDE_OCCUPIED_CAP_COMPLETE_C6_GLOBAL_2026_10_26.md.**
No shared ledger is changed by this source.

Put

    Q=1105/256, s=1/sqrt(2),
    T=sqrt(R^2-1/4), D=T-1, M=T-1/2=D+1/2,
    r0=R-s,                         2<=R<=sqrt(Q).

Every contained unit has center norm at most M. Indeed its farthest
corner squared norm is its center squared norm plus 1/2 plus the sum
of the absolute own center coordinates, and that sum is at least the
center norm. Every physical boundary unit has center norm at least r0
by its circumradius s. We will use

    9/10<D<61/60, M<91/60, R<21/10, T>19/10.             (1)

The upper strict comparison follows from

    (91/60)^2+91/60+1/2-Q=31/57600>0.

Keep an entire original simple positive cycle with at least three
positively circle-loaded bodies and an actual side-normal transmitter
X-U-Y. All physical squares, circle masks, individual circle weights,
forces, original point normals and actual side means remain unchanged.

**Theorem.** If the actual exterior X-U-Y pocket contains an additional
physical unit E, then the outward side of U has height at most D in its
channel frame. Consequently

    dist(O,U)<1/60.                                      (2)

The theorem does not assert that E lies wholly above U's outward side.
Its proof instead covers every possible center of E that could avoid U.

## 1. Full actual channel domain and a radial interior point

The accepted complete channel results give

    P_X=(-a,h), P_Y=(b,h), a+b=1,
    X subset {x<=-a}, Y subset {x>=b},
    U=[-a,b] times [v,v+1], v<=h<=v+1,
    h>3/10, a>7/100, b>7/100.                            (3)

Here the height bound is
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`; the full-mask port margin is
`SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`,
Sections 1--3, independently reviewed in
`REVIEW_SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_C6_2026_10_26.md`.
The unchanged endpoint centers have nonnegative heights and the
appropriate left/right horizontal signs. Original pocket routing gives
the whole inclusion E subset {y>=h}.

Suppose, for a contradiction, that v+1>D. Choose any radius rho with

    D<rho<min(v+1,41/40).

Such radii exist by (1). Write c_E for the actual center and r=|c_E|.
Every unit has support half-width at least 1/2, so

    (c_E)_y>=h+1/2>4/5, r>4/5, r<=M.

The point z_rho=rho*c_E/r lies strictly inside E's inscribed radius-1/2
disk. Indeed r-rho<1/2 and rho-r<41/40-4/5=9/40<1/2.
In particular z_rho is in the open interior of E and has height >h.
It also has height <v+1. Since E and U have disjoint open interiors,

    (z_rho)_x<-a  or  (z_rho)_x>b.                      (4)

Equality with either vertical side is also impossible: a point of E's
open interior on that side would have a neighborhood meeting U's open
interior. Because a,b>0, the alternative in (4) is fixed by the sign of
(c_E)_x. Reflect if necessary so it is always the left alternative.

Write the reflected center of E as (x,y)=(-(c_E)_x,(c_E)_y), with x,y>0.
Letting rho decrease to D in (4) gives

    x/r>=a/D, y>=h+1/2, x^2+y^2<=M^2.                   (5)

In particular a<D. This limit changes no physical point, mean, force
or square; it only proves a closed scalar inequality for the fixed
actual center c_E.

## 2. Every actual endpoint mask except the opposite corner is excluded directly

First suppose X owns the channel's vertical side. Its full original
form, including its actual mean, is

    X=[-a-1,-a] times [B-1,B],
    B>=1/2, B-1<=h<=B,
    R^2=(a+1)^2+B^2.

By (3), a+1>107/100>41/40>rho, so (z_rho)_x>-a-1.
The left alternative in (4) gives (z_rho)_x<-a, and its height is
strictly above h>=B-1. Also

    B^2-(D^2-a^2)=2(D-a)+1/4>0.

Choosing rho sufficiently close to D therefore gives
(z_rho)_y<sqrt(rho^2-a^2)<B. Thus z_rho lies in the open interior of
both X and E, a contradiction. This covers the whole actual side-mean
interval without selecting a new mean or assuming a unique circle mask.

Otherwise the rightmost channel application is the actual exposed
vertex p=(-a,h). Choose its original side vectors

    u=(c,t), w=(-t,c), c,t>0, c^2+t^2=1,

so X has vertices p,p-u,p+w,p-u+w. Put

    k=-ac+ht, j=at+hc>0.

The physical farthest circle corner is p+w when k>=1/2, or p-u+w when
k<=1/2; the physical two-corner tie is k=1/2 and is included in the first
case. If k>=1/2, the actual circle equation gives

    R^2=k^2+(j+1)^2, j<=sqrt(R^2-1/4)-1=D,
    |p|^2=R^2-2j-1>=D^2+1/4.                            (6)

For rho sufficiently close to D, rho^2<D^2+1/4. But (4) and
(z_rho)_y>h>0 give |z_rho|^2>a^2+h^2=|p|^2, contradicting (6).

The only remaining case has k<1/2 and a unique physical farthest corner
p-u+w. Its unchanged proper degree-two concurrence is on the positive
ray through that corner, inside X, at the channel height h. Therefore
the circle corner has height at least h, and c>=t. This is precisely
the original proper-concurrence consequence already used in
`GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md`, Sections 1.1 and 3.1.
It is used only for a physically unique mask; radial ties were handled
by (6), without imposing an inside-body radial concurrence on them.

Put C=c+t and J=c-t. The actual center of X, after reflecting its
horizontal coordinate, is

    c_X'=(a+C/2,h+J/2),
    1<=C<=sqrt(2), 0<=J<=1.

In particular it has the form

    Z=(a+w0,B0),
    1/2<=w0<=s, h<=B0<=h+1/2, |Z|>=r0.                 (7)

The next lemma shows that the entire center set (5) is strictly within
distance one of Z. This contradicts disjoint unit interiors, since their
open inscribed radius-1/2 disks are disjoint.

## 3. A continuous center cover for the complete opposite-corner wing

**Center-cover lemma.** Assume (1), h>3/10, 0<a<D, and let Z satisfy (7).
Then every point (x,y) in

    K={x^2+y^2<=M^2, y>=H:=h+1/2,
       x>=a*y/A},       A=sqrt(D^2-a^2),                 (8)

has distance strictly less than one from Z.

The original center inequalities (5) imply exactly (8). If K is empty
there is nothing to prove. Otherwise H<=MA/D, and its three boundary
joins are

    P=(Ma/D,MA/D),
    Q0=(sqrt(M^2-H^2),H),
    L=(aH/A,H).                                         (9)

Its boundary consists of the two segments L-P and L-Q0 and the circular
arc P-Q0 in the first quadrant. Squared distance from Z is convex on
each segment. On the circular arc, it equals
M^2+|Z|^2-2M Z dot (cos theta,sin theta); its second derivative is
2M Z dot (cos theta,sin theta)>0. Thus it suffices to check the three
points in (9). Degenerate boundary joins are harmless.

### 3.1. The cone endpoint P

The horizontal gap from Z to P is

    (a+w0)-Ma/D=w0-a/(2D)>0,

and P's height is at least H>=B0. Increasing w0 to s and decreasing
B0 to the smallest value allowed by |Z|>=r0 and B0>3/10 can only
increase the squared distance. Define

    a_* = sqrt(r0^2-9/100)-s.

Then 0<a_*<7/10<D. Indeed r0>5/4 gives the first inequality, and
a_*<R-s-s=R-sqrt(2)<7/10 gives the upper bound. For a<=a_* the resulting
lower height is sqrt(r0^2-(a+s)^2); for a>=a_* it is 3/10. Hence it
suffices to bound

    F(a)=(s-a/(2D))^2+(M sqrt(1-a^2/D^2)-B(a))^2,

    B(a)=sqrt(r0^2-(a+s)^2) if a<=a_*,
    B(a)=3/10                 if a>=a_*.

For a>=a_*, both nonnegative gaps in F decrease with a on the relevant
domain: the vertical gap stays positive because P's height is at least
H>4/5. Therefore F(a)<=F(a_*).

For 0<=a<=a_*, the relaxed point (a+s,B(a)) has norm r0, while P has
norm M. We have M>r0: since R-T=(1/4)/(R+T)<5/78 and s>7/10,

    M-r0=s-1/2-(R-T)>1/5-5/78>0.

Also P_x=a+a/(2D)<a+1/2<a+s. Consequently the polar angle of P is
strictly larger than that of the relaxed point. Call their positive
angle difference delta(a). Its derivative is

    delta'(a)=1/B(a)-1/sqrt(D^2-a^2).

Its sign changes at most once, from negative to positive, because

    D^2-a^2-B(a)^2=D^2-r0^2+s^2+2as

increases strictly with a. Thus delta attains its maximum at a=0 or
a=a_*. Squared distance is M^2+r0^2-2Mr0 cos(delta), increasing in this
positive first-quadrant angle difference. Therefore only those two
endpoints need checking.

At a=0,

    F(0)=1/2+(M-sqrt(r0^2-1/2))^2<3/4.                 (10)

Indeed r0^2-1/2=R^2-sqrt(2)R increases for R>=2 and is at least
4-2sqrt(2)>8/7>(61/60)^2. Its square root is below r0<M, and M<91/60,
so the positive difference in (10) is less than 1/2.

For the other endpoint put z=a_*/D. We claim

    z>7/12                      for every R>=2,
    z>3/5                       for R>=51/25.            (11)

For either k=7/12 or k=3/5, the inequality z>k is equivalent, after
squaring positive quantities, to

    G_k(R)=(1-k^2)R^2-2sR-9/100+2sk-3k^2/4
                 -2k(s-k)T >0.                        (12)

The quantities squared are sqrt((R-s)^2-9/100) and s+k(T-1), both
strictly positive. On R>=2, R/T<21/20. With s<17/24,
7/12<=k<=3/5 and 0<s-k<1/8, differentiation gives

    G_k'(R)=2(1-k^2)R-2s-2k(s-k)R/T
           >64/25-17/12-63/400=1183/1200>0.

At R=2, using s<17/24 and T=sqrt(15)/2<31/16 in (12) gives

    G_(7/12)(2)>241/57600>0.

At R=51/25, using s<17/24 and T<989/500 gives

    G_(3/5)(51/25)>1571/250000>0.

These substitutions are lower bounds: (12) decreases with s and with
T, since s>k. The radical comparison reserves are 1/256 and
221/250000 respectively. This proves (11) on the two entire intervals.

If 2<=R<=51/25, then M<37/25 because

    (37/25)^2+37/25+1/2-(51/25)^2=11/1250>0.

By (11), sqrt(1-z^2)<sqrt(95)/12<13/16 and s-z/2<5/12. The positive
vertical gap in F(a_*) is less than 361/400. Hence

    F(a_*)<(5/12)^2+(361/400)^2
           =1-17111/1440000<1.                          (13)

If 51/25<=R<=sqrt(Q), then z>3/5 and M<91/60. Therefore

    F(a_*)<(s-3/10)^2+(137/150)^2
           <1-1/45000<1.                              (14)

The last comparison uses s^2=1/2 and s>707/1000; its displayed rational
reserve is exact. These two overlapping radius intervals exhaust the
whole range. Equations (10)--(14) prove |P-Z|<1.

### 3.2. The horizontal boundary endpoint Q0

Its vertical gap from Z is H-B0 in [0,1/2]. Since K is nonempty,
(Q0)_x>=Ma/D>a. Thus if Z_x>=(Q0)_x, its horizontal gap is less than
w0<=s<4/5. In the other direction, H>4/5 and (1) give

    (Q0)_x^2<M^2-(4/5)^2<5977/3600<(13/10)^2,

whereas Z_x>a+1/2>1/2. That horizontal gap is again less than 4/5.
Consequently

    |Q0-Z|^2<(4/5)^2+(1/2)^2=89/100<1.                (15)

### 3.3. The lower sector corner L

Because L_x<=P_x<Z_x, the horizontal gap is positive and equals

    Z_x-L_x=w0+a(1-H/A).

Again the vertical gap is in [0,1/2]. If H>=A, the horizontal gap is
at most w0<=s, giving squared distance at most 3/4. If H<A, then

    a^2=D^2-A^2<D^2-H^2<1417/3600<(19/30)^2,
    1-H/A<1-H/D<1-(4/5)/(61/60)=13/61.

It follows that

    Z_x-L_x<s+247/1830<17/24+247/1830<17/20.

The last reserve is 49/7320. Thus in this case

    |L-Z|^2<(17/20)^2+(1/2)^2=389/400<1.                (16)

Equations (13)--(16), (10), and the complete boundary argument after
(9) prove the center-cover lemma on the whole continuous domain.
There is no sampled pose, angle mesh, coefficient packet or omitted
orientation endpoint in this cover.

## 4. Whole-channel conclusion

The masks in Section 2 exhaust the actual endpoint X. In the final
opposite-corner case, its unchanged center has form (7), while the
unchanged extra center satisfies (8). Section 3 gives |c_E-c_X|<1,
contrary to disjoint open unit inscribed disks. Reflection treated the
other alternative in (4) without changing any physical datum.

The assumption v+1>D is therefore impossible, proving v+1<=D. By (3),
v+1>=h>0 and -a<0<b, while

    v<=D-1<1/60.

If v<=0, U contains O. If v>0, the distance is v. Thus dist(O,U)<1/60
in every original mean and slider, proving (2).

Notice that this argument does not infer whole vertical separation of
E and U. It allows tilted extras with a lowest point outside the port
strip. The actual center of every such candidate is covered by an
endpoint exclusion disk, which is the stronger obstruction needed here.

## 5. Complete original four-load bare-C6 join

Retain either entire original orbit

    U-A-V-B-D-C-U,              U-A-B-V-C-D-U,

with its four positive circle loads, both original transmitters,
all true degree-two equations, physical circle masks, full original
side means, physical unit bodies and three actual extras.

For a nine-square packing in the candidate disk, the accepted global
bound `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` gives R>2. Thus the whole
range of this source applies, including every original radius survivor.

The accepted full pair covers and
`FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md` give central capacity
at most one for both whole orbits and every width pattern. Every actual
side cap has capacity at most one by
`GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md`. Every actual diagonal
cap is empty by the accepted whole-channel theorem
`FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`.

If either transmitter is diagonal, the total capacity for the three
extras is at most two. Hence both transmitters must be side-normal,
and each of the two caps and the central region must contain exactly
one actual extra. Call them E_U,E_V,T0, respectively. The present
whole-channel theorem applies separately to the two original occupied
caps and gives

    dist(O,U)<1/60<1/40, dist(O,V)<1/60<1/40.            (17)

The complete central routing and local inner-square bounds in
`SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md`, Section 5, give

    dist(O,T0)<1/40,
    every actual vertex norm of T0>19/300>3/50.

The full port theorem used in (3) gives every actual vertex of U,V
norm greater than 7/100>3/50, for their unchanged original sliders.
The three original units U,V,T0 have pairwise disjoint open interiors.
By (17) they all meet the closed disk of radius delta=1/40, and every
vertex lies outside the disk of radius d=3/50. Since delta<d/2 and
d<1/2, the independently reviewed angular theorem in
`SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`,
Section 4, says that at most two such units can exist. This contradiction
excludes the entire remaining (1,1,1) allocation.

Thus both complete original four-load bare-C6 orbits are excluded,
including their joint-cap obligations and all width patterns. No
positive circle force, actual channel equation, original mean,
physical endpoint or additional square has been dropped. This proof
does not claim any positive-chord hexagon family, which retains its
additional actual forces.

After independent acceptance, this supplies the complete exits for
the two original FOUR_ZERO_DISTANCE2 and FOUR_ZERO_DISTANCE3 parents
and their CAPS gates. The exact whole bare-C6 assembly follows next.

## 6. Complete original simple-positive-C6 load-cover assembly

The accepted necessary cover in
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`, Sections 2, 3 and 4.1,
has precisely the following six orbits when there is no positive chord.
Its hypotheses are the selected entire positive component, the physical
boundary path-forest theorem and the connected loaded noncontact graph.
They give at least three and at most five positive circle loads.
Six loaded bodies would form a forbidden physical boundary six-cycle.
Zero load is not otherwise replaced by physical circle clearance.

Label the original rim 0,1,2,3,4,5. Rotations and reflections act on all
actual physical data at once. The complete accepted cover and exits are:

| Loaded representatives | Whole original family | Complete exit |
| --- | --- | --- |
| 013 | Three loads, cyclic gaps (1,2,3) | `SIX_CYCLE_THREE_LOAD_LONG_CHANNEL_EXCLUSION.md` |
| 024 | Alternating three loads | The complete width/mask union below |
| 0123 | Four loads, adjacent unloaded bodies | `BOUNDARY_THREE_EDGE_PATH_DIAMETER.md`, Section 3 |
| 0124 | Four loads, unloaded cyclic distance two | Section 5 of this source |
| 0134 | Four loads, opposite unloaded bodies | Section 5 of this source |
| 01234 | Five loads | `GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md`, Section 7, with its accepted central-capacity join |

For clarity, the entire alternating row is already accepted by
`REVIEW_C6_COMPLETE_ALTERNATING_ROOT_RECOVERY_2026_10_26.md` and its
independent original-parent reviews. Its actual exhaustive sibling
union is reproduced here without changing any source premise:

| Actual widths and physical masks | Complete accepted source |
| --- | --- |
| At least two diagonal transmitters; every mask | `SIX_CYCLE_ALTERNATING_DOUBLE_DIAGONAL_EXCLUSION.md` |
| Exactly one diagonal; all eight ordered unique/radial masks | `SIX_CYCLE_ONE_DIAGONAL_ALL_MASKS_EXCLUSION.md` |
| All side-normal; all three loaded units physically unique | `SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md` |
| All side-normal; exactly one physical radial loaded unit | `SIX_CYCLE_ONE_RADIAL_COMPLETE_EXCLUSION.md` |
| All side-normal; at least two physical radial loaded units, including three | `SIX_CYCLE_ZERO_DIAGONAL_TWO_RADIAL_EXCLUSION.md` |

The two physical masks are determined by all actual circle corners,
not by which individual circle weights happen to be positive. The
one-radial and one-diagonal assemblies explicitly retain zero individual
weight endpoints and genuine side-mean endpoints. Every unloaded
degree-two transmitter has its original actual width one or sqrt(2),
so these alternatives exhaust that whole row. The long three-load and
adjacent-zero four-load sources are complete core contradictions; their
three arbitrary extras remain present. The alternating and five-load
assemblies give complete nine-square contradictions with those same
three extras. Section 5 supplies precisely the formerly missing two
four-load completion families.

Consequently the entire selected simple positive six-cycle has no
nine-square completion in the candidate radius window. The same-nine
R>2 theorem used in Section 5 also covers every smaller-radius candidate
before the common full-window sources are applied. No positive edge,
load, original physical body, actual mean or additional square has been
deleted while moving between the six actual load alternatives.

After full-source and original-parent independent acceptance, exactly
the following five existing unchecked labels obtain complete exits:

    M6.B6.C6.FOUR_ZERO_DISTANCE2.CAPS,
    M6.B6.C6.FOUR_ZERO_DISTANCE3.CAPS,
    M6.B6.C6.FOUR_ZERO_DISTANCE2,
    M6.B6.C6.FOUR_ZERO_DISTANCE3,
    M6.B6.C6.ALL.

This is the entire component with exactly the six rim positive edges.
A graph with a positive chord has further actual forces and different
degrees. No chord is deleted to apply this theorem. Positive-chord
hexagon families and the full coarse cell C1.6.b0 remain separate open
obligations. The unrestricted sharp theorem, its original equality
classification and Lean integration are not concluded here.

No Lean compilation, CI, remote write, or shared-ledger edit is
performed by this source.
