# The adjacent shared triangle chart has closing boundary-path pocket capacity at most one

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed hand pocket theorem for the full stated
physical chart, awaiting root and separate independent review.**
A separate exact adjacent-share cover must establish this chart
before using it for an entire original owner family. No whole
original graph/load checkbox is changed here.

The proof uses three fixed inner-circle points of the actual
boundary square on three complete height intervals. It uses no
numerical pose, orientation grid or approximate scalar certificate.

## 1. Exact chart and complete actual component

Put Q=1105/256 and work in 2<R<=sqrt(Q). Retain the same
original physical squares and their selected full equilibrium.
Suppose a complete positive component consists of an unloaded U
and a loaded boundary path

    V,W,B_3,...,B_(k-1),T,       3<=k<=6,

together with exactly the three U spokes UV,UW,UT. Its actual
outer-face order is U,V,W,...,T,U. Thus U has true degree three,
V and T have true degree two, W has degree three, and every
other path body has degree two.

In an actual common U,V,W frame about the unchanged origin,
assume their entire physical squares are

    U=[-a,1-a] times [b-2,b-1],
    V=[-a,1-a] times [b-1,b],
    W=[1-a,2-a] times [b-1-delta,b-delta],              (1)

where

    1/2<a<1,       b>sqrt(3),       0<delta<1,
    a^2+b^2=R^2.                                     (2)

All original means on their shared sides remain arbitrary.
The actual UV normal from U is North, UW from U is East,
and VW from V is East. The physical V circle corner is
Z_V=(-a,b). W is also physically boundary, with its actual
unique corner (2-a,b-delta). No equation at W is reduced.

**Theorem.** The actual closing exterior pocket through U
between V and T contains at most one whole additional unit.

Every original force, torque, degree, mean, physical circle
corner and individual zero circle weight remains. T may have
either physical circle mask and any original contact owner
at its U or boundary-path port. All additional units remain.

## 2. Full U force, the actual third port, and two global chart improvements

Write mu_V,mu_W>0 for the actual U force magnitudes toward
V and W. Its complete unloaded force equation gives

    mu_T*n=-(mu_W,mu_V),
    mu_T>0, n_x<0,n_y<0,                              (3)

where n is the unchanged U-to-T unit normal. It strictly
exposes the actual southwest U vertex. Thus the original
UT application is forced to be

    P=(-a,b-2).                                       (4)

No original side mean was reassigned in obtaining P.

Since P belongs to the actual boundary unit T, one of its
physical circle corners is at distance at most sqrt(2)
from P. Hence

    |P|>=R-sqrt(2).

Using |P|^2=R^2+4-4b and R>2 gives

    b<=1/2+R/sqrt(2).                                 (5)

Consequently

    b<197/100<2.                                      (6)

The exact upper comparison is
(147/100)^2-Q/2=863/320000>0.

Also

    a^2=R^2-b^2
        >=R^2/2-R/sqrt(2)-1/4
        >7/4-sqrt(2)>9/28>(9/16)^2.                  (7)

The strict middle step follows by factoring the difference
at R=2 as
(R-2)*((R+2)/2-1/sqrt(2))>0.
For the next comparison use sqrt(2)<10/7; the final
rational reserve is 9/1792. Therefore

    a>9/16.                                          (8)

These bounds use a real corner of the unchanged T and
the actual unit diameter, not a virtual circle load.

## 3. Every actual T circle corner is strictly left of the U/V wall

Let Z be any physical circle corner of T. Suppose Z_x>=-a
and put w=Z-P. The actual T minimum-n support and (3) give

    mu_W*w_x+mu_V*w_y<=0.

Thus w_x>=0 implies w_y<=0. With a>0, b<2 and |w|<=sqrt(2),

    P dot w=-a*w_x+(b-2)*w_y
               <=sqrt(2)*(2-b).

It follows that

    |Z|^2<=|P|^2+2+2sqrt(2)*(2-b)
           =R^2+(4+2sqrt(2))*(1+1/sqrt(2)-b)
           <R^2.                                    (9)

The final comparison uses
b>sqrt(3)>1+1/sqrt(2);
squaring the latter reduces to sqrt(2)<3/2.
This contradicts |Z|=R. Hence

    Z_x<-a for every actual physical circle corner of T. (10)

Both corners in the physical two-circle mask are included,
irrespective of either individual zero force coefficient.

## 4. The actual T center has a complete strict angle bound

Let c_T be the actual center of T, r_T=|c_T| and
sigma=1/sqrt(2). Since P belongs to T and T is boundary,

    |c_T-P|<=sigma,
    r_T>=R-sigma>31/24,                              (11)

using sigma<17/24. From b>sqrt(3)>173/100 and b<2,

    |(c_T)_y|<=2-b+sigma<587/600,
    (c_T)_x<=-a+sigma<5/24.                           (12)

The center abscissa is in fact negative. If it were
nonnegative, (11)--(12) would contradict

    (31/24)^2-(5/24)^2-(587/600)^2
          =240431/360000>0.

Define theta_T=arg(c_T) in (pi/2,3pi/2).

We will use the following exact forty-degree estimates:

    cos(2pi/9)>19/25,
    77/120<sin(2pi/9)<13/20.                         (13)

For the cosine bound, the cubic 4z^3-3z is increasing
for z>1/2, and

    -1/2-[4(19/25)^3-3(19/25)]=753/31250>0.

The upper sine bound follows since

    (13/20)^2-[1-(19/25)^2]=1/10000>0.

For the lower sine bound put s0=77/120. The cubic
3z-4z^3 is strictly decreasing for z>1/2, and

    3s0-4s0^3=375067/432000
             >13/15>sqrt(3)/2.

The first rational reserve is 667/432000; the second
uses (26/15)^2-3=1/225>0. Both s0 and sin(2pi/9)
are in (1/2,sqrt(3)/2), where the decreasing branch
applies, and sin(2pi/3)=sqrt(3)/2. This proves (13).

If (c_T)_y>=0, then theta_T<=pi and all three bounds
below hold immediately. Otherwise

    theta_T=pi+arcsin(|(c_T)_y|/r_T).

Equations (11)--(13) give the complete matched bounds:

| Entire height range used | Bound for the negative center-height ratio | Resulting strict bound |
| --- | --- | --- |
| All b>sqrt(3) | less than 587/775<19/25<cos(2pi/9) | theta_T<23pi/18, or 230 degrees |
| b>=37/20 | less than 103/155<7/10<1/sqrt(2) | theta_T<5pi/4, or 225 degrees |
| b>=47/25 | less than 497/775<77/120<sin(2pi/9) | theta_T<11pi/9, or 220 degrees |

For the middle row,
2-b+sigma<103/120 before dividing by 31/24.
For the last row the corresponding numerator is 497/600.
The last rational comparison has reserve
77/120-497/775=7/18600>0. All endpoints of the displayed
height intervals remain.

## 5. Three actual V interior points cover the entire height domain

Set rho=9/8. In each row below the radius-rho point
at angle phi belongs to the actual open interior of V:

| Entire actual height interval | phi |
| --- | --- |
| b<=37/20 | 13pi/18, or 130 degrees |
| 37/20<=b<=47/25 | 25pi/36, or 125 degrees |
| b>=47/25 | 2pi/3, or 120 degrees |

Here are the full coordinate checks. All points have
negative x, which is strictly below 1-a because a<1.
All their y coordinates are at most rho<b, so only
the lower and left V sides need comparison.

In the first row the point is

    (-rho*sin(2pi/9),rho*cos(2pi/9)).

Since R^2>4 and b<=37/20,

    a^2>231/400>(117/160)^2,
    rho*sin(2pi/9)<117/160,
    rho*cos(2pi/9)>171/200>17/20>=b-1.

The squared reserve is 219/5120, and the height
reserve at the last rational comparison is 1/200.

In the second row the point is

    (-rho*sin(7pi/36),rho*cos(7pi/36)).

The elementary comparison 35 degrees<36 degrees,
together with cos(pi/5)=(1+sqrt(5))/4>4/5,
gives cos(7pi/36)>4/5 and sin(7pi/36)<3/5.
The displayed golden-ratio bound uses sqrt(5)>11/5.

Now

    a^2>291/625>(27/40)^2,
    rho*sin(7pi/36)<27/40,
    rho*cos(7pi/36)>9/10>22/25>=b-1.

The squared reserve is 399/40000, and the last
height reserve is 1/50.

In the third row the point is

    (-9/16,9sqrt(3)/16).

Its abscissa is strictly above -a by (8). Its
height is strictly above b-1 by (6) and

    9sqrt(3)/16>1557/1600>97/100.

The last rational reserve is 1/320. Thus all
three interval statements are strict, including
their shared interval endpoints.

In every row, its matched bound in Section 4 is

    theta_T<phi+5pi/9.                               (14)

The quantity 5pi/9 is exactly 100 degrees.

## 6. The actual occupied closing crosscut is confined to the left cap

The V-to-W original normal is East and every actual
VW mean has height at least b-1>0. Its directed
moment is strictly negative. Hence the boundary
path V,W,...,T has clockwise circular order, by
the boundary-pair moment theorem and the actual
angular-neighbor contact rule. Its closing gap
through U is counterclockwise from V to T.

Use the actual gap-facing physical contact extremes
only for the occupied crosscut. The UV gap extreme
is (-a,b-1), and the UT contact is the forced unique
point P=(-a,b-2). The entire vertical segment

    Z_V=(-a,b) to P=(-a,b-2)

is occupied by the actual left sides of V and U.
It is therefore a valid physical barrier, even
though it lies on their boundaries.

Choose T's actual gap-facing circle corner Z_T.
By (10), Z_T lies strictly left of x=-a. The
segment from P to Z_T lies in T and has x<-a
except at P. It can be perturbed within T, if
needed, preserving this strict half-plane.
The full unloaded-three-force touching-return
theorem makes T closed-disjoint from V; T meets
U only at P because n strictly exposes that U
vertex. The occupied crosscut is consequently
simple.

The closing circle arc from Z_V to Z_T in the
actual counterclockwise gap lies wholly in x<=-a:
(10) places Z_T on that circle cap, and the actual
boundary path has the complementary clockwise
order. All other core circle-corner intervals
remain on the boundary-path side. Completion
corners on the closing arc are not removed.

Thus the entire actual Jordan boundary, and
therefore its bounded region, lie in

    x<=-a.                                           (15)

Every extra assigned to this closing pocket is a
whole unit in this cap. It has actual center c_E
satisfying

    (c_E)_x<=-a-1/2<-1.                              (16)

The halfwidth bound is at least 1/2 for every
square orientation.

We also need the exact angular upper routing at
T. Let the last boundary-path predecessor of T
be B. The T-to-B pair has strictly positive
moment in counterclockwise order. The full true
degree-two T torque, retaining its UT pair and
all radial circle forces, therefore gives

    det(P,n)>0.                                      (17)

The local proper-concurrence theorem applies at T
because B is an actual boundary neighbor. It gives

    q=P+ell*n=tau*F_T,
    ell>=0, tau>0,                                   (18)

where F_T is the full actual circle resultant,
including the physical two-corner case and any
outside concurrence.

By (3),(4),(6), both P and n are in the strict
third quadrant. Equation (17) puts the direction
of n strictly counterclockwise from that of P
within this quadrant. Hence (18) gives

    arg(P)<=arg(F_T)<theta_T+pi/12.                   (19)

The last bound is the full physical circle-corner
and resultant cone of halfwidth pi/12. The same
bound holds for arg(Z_T).

The occupied vertical wall from Z_V down to P
has monotonically increasing argument, ending
at arg(P). The T path can be kept in the convex
angular interval between its endpoint directions.
The actual closing circle arc ends at arg(Z_T).
Thus the entire actual Jordan boundary also lies
in the convex pointed cone

    arg(Z_V)<=theta<=theta_T+pi/12.                  (20)

Its aperture is below pi: arg(Z_V)>pi/2 and the
global Section 4 bound gives theta_T+pi/12<49pi/36.
The bounded Jordan region inherits both defining
half-planes of this cone, as well as the cap (15).

The original V--U--T center/contact crosscut deforms
to this wall and P--Z_T path within the actual closed
U,V,T union, sliding its UV junction only along their
real common side for this homotopy. It therefore
preserves winding at every point of every extra's
open interior. Original force means are unchanged.

This is actual occupied routing. Original means
remain in every force and torque equation. An
extra's connected open interior cannot cross the
closed occupied crosscut. Additional zero-weight
contacts only subdivide the region. At weak
junctions the usual compact-inner-subset routing,
followed by closure, retains the whole unit on
the same bounded side.

## 7. One V interior point and the actual centered arcs exclude two extras

Every contained unit center has norm less than
91/60, from its actual farthest-corner inequality

    |c|^2+|c|+1/2<=Q,
    (91/60)^2+91/60+1/2-Q=31/57600>0.

Combining this with (16), every exterior extra
center has angle theta_E satisfying

    13pi/18<theta_E<23pi/18.                          (21)

Indeed its center is in the left half-plane and

    cos(theta_E)<-60/91<-13/20<cos(13pi/18).

The middle rational reserve is
60/91-13/20=17/1820>0; the last comparison is
sin(2pi/9)<13/20 from (13).

Its center radius is greater than one by (16).
The centered-forty-degree arc theorem therefore
puts the entire closed radius-rho arc of halfwidth
pi/9 about theta_E in the actual open interior
of E. The same theorem applies to the boundary
unit T, whose center radius exceeds 31/24.

From (20), theta_E<=theta_T+pi/12. If theta_E
were at or above theta_T, the two minor center
directions would differ by at most pi/12, contrary
to their strict separation greater than 2pi/9.
Thus

    theta_E<theta_T.                                 (22)

Choose the Section 5 point appropriate to the
actual b. Its angle phi is at most 13pi/18,
whereas (21) puts theta_E strictly above that
angle. If theta_E-phi<=pi/9, that physical point
of int V would belong to the closed centered
arc contained in int E. This contradicts disjoint
open interiors. Therefore

    theta_E-phi>pi/9.                                (23)

Suppose two extras E_1,E_2 occupied the actual
closing pocket, ordered by their center angles.
By (21)--(22), all ordinary successive differences
below are minor gaps. Equations (22)--(23) and
the strict forty-degree center separation give

    theta_(E_1)-phi>pi/9,
    theta_(E_2)-theta_(E_1)>2pi/9,
    theta_T-theta_(E_2)>2pi/9.

Their sum gives theta_T-phi>5pi/9, contradicting
the complete matched estimate (14). This proves
closing pocket capacity at most one.

The proof retains every actual original unit,
mask, mean and weak contact. It does not need
the quarter-disk pocket theorem or an assumption
that either concurrence lies inside its unit.

## 8. Literal original chart caller and its precise boundary

For M6.B6.HEXAGON.D02.L01345, set

    U=2, V=1, W=0, B_3=5, B_4=4, T=3.

The original path is 1,0,5,4,3. All true degrees
match Section 1 and every original positive
chord remains. Once the actual adjacent-share
frame cover gives (1)--(2), the entire closing
pocket has capacity at most one.

The original central triangle and pentagon
have combined unit capacity at most one by
CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md.
Every other exterior pocket is a direct
touching-boundary-pair pocket and is empty.
The complete occupied face/pocket partition
therefore allocates at most two of the three
unchanged extras. Hence this entire chart is
excluded in the original family.

This manuscript does not itself classify all
adjacent shared-face layouts, nor the original
VW singleton endpoint of that separate cover.
It also does not exclude nonparallel original
UV or UW contacts or the remaining W-owned
same-axis interface. Those domains require their
own complete joins, so the original D02 row
and its parents remain open here.

## 9. Frozen operative sources

| Source | SHA-256 | Exact role |
| --- | --- | --- |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full U3 makes T closed-disjoint from both touching returns; no normal owner restriction |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Degree-free physical boundary-pair moment sign |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Local proper-concurrence Lemma 2.1 with one actual boundary neighbor |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only: full physical corner/resultant cone and actual center bound |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Whole centered arcs for actual exterior extras and boundary T |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Actual physical path and center order |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Physical circle-corner order and direct-pair pocket emptiness |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Exact central capacity and full actual face routing |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load/degree substitution |

All scalar bounds above are displayed exact hand
inequalities on their entire stated intervals.
No pose sampling, angle mesh, numerical certificate,
Lean compilation, CI, workflow, ledger edit, commit,
push or merge is used.

