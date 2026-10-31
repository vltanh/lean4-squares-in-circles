# Three genuine leaves in a diamond: complete nonparallel and two-owned parallel tip interfaces

Date: October 27, 2026.

**Status: fresh complete hand exclusions of the two stated original
interfaces, submitted for full independent and root review.** The
parallel-tip cases with a tilted hub remain explicit. This source does
not yet claim a whole A8 or C1.4.b3 closure.

Keep all nine actual contained unit squares and the compatible selected
physical certificate in 79/40<=R<=sqrt(1105)/16. The original diamond
has hubs H,K and tips B,D, with positive edges

    HK, HB, KB, HD, KD.

There is one genuine leaf at each of H,K,B. Their true degrees are
H4,K4,B3,D2, and the three leaves have degree one. The two other
physical squares stay arbitrary and present. Every original force,
application mean, normal owner, physical circle mask and individual
zero weight is retained.

Write

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,       Q=1105/256.

The low/critical domain and every D-leaf assignment have their complete
degree-free exits in THREE_GENUINE_LEAF_ROOTS_LOW_RADIUS_EXCLUSION.md
and D_LEAF_ROOT_TWO_NEAR_ORIGIN_UNITS_EXCLUSION.md. Here all three
actual leaves are S. The two conclusions proved below are:

1. The two original B-to-H and B-to-K forces cannot be nonparallel.
2. If they are parallel, the two hubs cannot both own their actual
   contacts with B.

Neither conclusion shortens a hub to degree three or deletes HK.

## 1. The actual near points, D load, and full B3 cover

For each genuine S root T, its actual point d*e_T and the complete
inward unit-normal segment give epsilon*e_T in T. Thus each of H,K,B
meets the closed D_epsilon and is physically circle-clear. In
particular, both actual nonleaf supports of B are at most epsilon.
GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md makes B aligned with its
genuine S leaf. Rotate the complete packing to write

    B=[epsilon,d] times [-b,a],  a,b>=0, a+b=1,
    L_B=[d,d+1] times [-1/2,1/2].                       (1)

The actual D is positively loaded. Otherwise its true two-force
equations make it a transmitter of width w>=1 between H and K.
In its channel direction, H's genuine near point gives its outgoing
support at least -epsilon, and K's genuine near point bounds its
incoming support by epsilon. The unchanged channel would therefore
give w<=2epsilon<1. This contradiction proves the positive load;
in particular D physically touches the containing circle.

The complete physical triangle H-B-K permits the radius-free facts in
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md and Section 2 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md. At B, an owned North or
South normal would make the other triangle normal nonobtuse to it,
contradicting the full zero vertical force sum. East similarly
contradicts horizontal balance. If one normal is West, the other is
horizontal by balance and must also be West: opposite parallel
triangle supports would make H and K physically disjoint.

If neither is a B axis, the strict vertex normals have opposite
vertical signs. Opposite vertices cannot serve two touching neighbors;
two right vertices cannot supply the required negative horizontal
sum; and one vertex cannot give the opposite vertical signs. Thus
the entire nonparallel case has actual points and normals

    P_H=(epsilon,a),     n_BH=(-cos(phi),sin(phi)),
    P_K=(epsilon,-b),    n_BK=(-cos(psi),-sin(psi)),    (2)

where phi,psi are strictly between zero and pi/2. The original full
B3 vertical and origin-moment equations give

    mu_H*sin(phi)=mu_K*sin(psi),
    mu_H*a*cos(phi)=mu_K*b*cos(psi).                   (3)

In particular a,b>0, including exclusion of both initial slider
endpoints. Put

    z=tan(phi)/a=tan(psi)/b>0,       theta=phi+psi.     (4)

These are equations of the unchanged actual forces and means.

### 1.1. The original compatible singleton selector

Both points in (2) are distinct actual B vertices, and neither is
collinear with its real East leaf direction. The finite pre-extraction
selection in Section 4 of ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md
therefore applies at this literal true B3, with arbitrary degrees at
H and K. For completeness, if the other singleton normal is m and
the candidate free normal is n at q, the necessary full B3 identity is

    det(e,n)*det(p,m)-det(e,m)*det(q,n)=0.

For fixed m not parallel to e this is det(W,n)=0, where
W=det(p,m)*e-det(e,m)*q is nonzero by the stated noncollinearity.
It excludes only finitely many directions in the actual strict free
interval. If both contacts are free, the two distinct physical
junction parameters give a nonzero polynomial on their product
interval. The complete finite pose prelist is imposed before
multiplier extraction, compatibly with the matched-junction and
uncrossing conditions. No actual side mean is selected or reset.

Consequently each nonparallel contact in (2), being nonaxis at B,
must be owned by its other endpoint. Define the actual hub axes

    w_H=(cos(phi),-sin(phi)),   v_H=(sin(phi),cos(phi)),
    w_K=(cos(psi), sin(psi)),   v_K=(-sin(psi),cos(psi)). (5)

Each w is its hub's own outward normal toward B. Their actual support
values are

    p_H=epsilon*cos(phi)-a*sin(phi),
    p_K=epsilon*cos(psi)-b*sin(psi),
    -epsilon<=p_H,p_K<=epsilon.                       (6)

The lower bounds use the real near points of the hubs; the upper
bounds also follow from the actual near point of B. No artificial
nearby application is substituted for P_H or P_K.

## 2. Both actual facing hub corners are near O

First obtain a uniform small angle from the original B3 equation.
Equation (6) gives a*sin(phi)<2epsilon and b*sin(psi)<2epsilon.
At least one of a,b is at least 1/2. For that index its sine is
less than 4epsilon<1/15, so its tangent is less than 1/sqrt(224).
Using (4) and the same index gives

    z<1/sqrt(56)<7/50,
    0<theta=atan(z*a)+atan(z*b)<z<7/50,
    cos(theta)>99/100.                                (7)

The last inequality follows from cos(theta)>1-theta^2/2.

Let g be the actual H-to-K normal. The physical triangle and both
actual owned B normals give g.w_H>=0 and g.w_K<=0. Therefore g
lies in the complete downward cone from -v_H to -v_K. In the H
frame it is sigma*w_H-tau*v_H with

    0<=sigma<=sin(theta),       tau>=cos(theta)>0.

Thus the actual HK support uses H's lower-right corner, except
at the endpoint g=-v_H, when it retains an arbitrary actual bottom
mean. At K the reverse normal uses its upper-right corner, except
at g=-v_K, when it retains an arbitrary actual top mean.

Write the actual boxes using those facing corners as

    H=[p_H-1,p_H] w_H + [h,h+1] v_H,
    K=[p_K-1,p_K] w_K + [k-1,k] v_K.                  (8)

The original HK support value lies in [-epsilon,epsilon], since
both H and K have their actual near points on opposite sides.
If its H point is the corner, this and (6) give

    |h|<=epsilon*(1+sin(theta))/cos(theta)<6epsilon/5.

If it is an H bottom mean, g=-v_H gives |h|<=epsilon directly.
The reflected K calculation gives the identical bound for k.
Hence, throughout both owned endpoint cases and the strict cone,

    |h|,|k|<6epsilon/5<1/50.                          (9)

No HK mean has been identified with a different corner. The two
facing corners have the small coordinates in (6),(9), even when
only one of them is the original HK application.

## 3. Complete genuine hub-leaf features in the facing frames

For H in (8), East and South own-axis leaf supports are too small.
Its facing corner is too near O to have norm d. Its opposite corner
(p_H-1,h+1) has squared norm greater than

    (59/60)^2+(49/50)^2 > (61/60)^2 > d^2,

so cannot be a genuine S application either. The actual radial
normal signs and all remaining own-side endpoints leave exactly:

* **West type:** the owned West leaf or the strict lower-left leaf.
  Here p_H<0 and h<=0. In the strict case its actual point is
  (p_H-1,h), with (p_H-1)^2+h^2=d^2; in the owned case p_H=-epsilon
  and its actual tangential coordinate is zero.
* **North type:** the owned North leaf or the strict upper-right
  leaf. Here p_H>=0 and h>epsilon/2. In the strict case
  h=sqrt(d^2-p_H^2)-1; in the owned case h=epsilon and the actual
  leaf's w_H component is zero.

For the West strict case, p_H<0 follows from
d^2-h^2>1, using (9). For the North strict case, p_H>=0 is
required by the actual outward corner cone, and
sqrt(d^2-p_H^2)-1>=sqrt(1+2epsilon)-1>epsilon/2.
The owned cases include all side endpoints. In particular one
does not treat a zero radial component as a strict vertex normal.

Reflecting the vertical coordinate gives the exact K alternatives:
West with p_K<0,k>=0, or South with p_K>=0,k<-epsilon/2.

### 3.1. Both vertical types cannot touch

If H is North type, every actual H point has world height at least

    h*cos(phi)-p_H*sin(phi)
       >epsilon*((99/100)/2-7/50)=71epsilon/200>0.

If K is South type, every actual K point has world height less
than -71epsilon/200. Their physical HK contact is impossible.

### 3.2. Both West types make the two real leaves overlap

Each West leaf direction differs from its own negative w axis by
less than atan((6/5)*epsilon/(1-epsilon))<6/295. Thus the smaller
angle between the two actual West leaves is less than

    7/50+12/295<1/4.

Both actual S-leaf centers have radius d+1/2<91/60. Their mutual
distance is less than (91/60)/4=91/240<1. The two open radius-1/2
incircles would overlap, contradicting the distinct actual leaves.
No circle force at either leaf is redistributed in this comparison.

Only a mixed West/vertical assignment remains. Reflecting the entire
packing vertically and exchanging H,K if necessary makes it

    H West type,       K South type.                  (10)

## 4. The mixed assignment forces the real HK owner

Let Q_H=p_H*w_H+h*v_H and Q_K=p_K*w_K+k*v_K be the two
facing corners in (8). Their signs from (10) are

    p_H<0, h<=0,       p_K>=0, k<0.

They satisfy

    Q_H.w_K=p_H*cos(theta)+h*sin(theta)<0<=p_K,
    Q_K.w_H=p_K*cos(theta)-k*sin(theta)>0>p_H.          (11)

The strict interior of the HK normal cone would require the same
point to be both Q_H and Q_K, excluded by (11). The endpoint
g=-v_H would require K's actual corner Q_K to lie in H, whereas
its w_H coordinate exceeds the actual H maximum p_H. It too is
excluded, including every H bottom mean.

Consequently the only possible original HK normal is

    g=-v_K.

K owns its actual top contact with H, whose unchanged application
is Q_H. It may be any allowed actual point on that K top side;
it is not reset to Q_K. Its full K-to-H force is a positive
multiple of v_K.

Now use the **entire K4** equation. Its actual K-to-B force is
a positive multiple of w_K; its K-to-H force is a positive
multiple of v_K; and its real South-type leaf direction has
nonnegative w_K component. Thus its remaining actual K-to-D
force has strictly negative w_K component. The physical triangle
K-H-D, with the actual K-owned KH axis v_K, additionally gives
that force a nonnegative v_K component. Its full feature cover is
therefore exactly

    K-to-D West, or strict Northwest

in the K frame. The real HK force is essential to the latter
nonobtuse fact and is retained throughout the K4 equation.

## 5. A sharper angle and two complete physical D/leaf caps

The mixed signs give a stronger angle without any changed means.
From p_K>=0 in (6), b*tan(psi)<=epsilon. From (6) and (7),
a*tan(phi)<2epsilon*sec(phi)<(101/50)*epsilon, because
sqrt(1+z^2)<101/100. Using (4) and a^2+b^2>=1/2 gives

    z<151/1500<1/9,       theta<1/9.                  (12)

In K coordinates the actual H West leaf's signed angular deviation
from West is alpha-theta, where
0<=alpha<=atan((6/5)*epsilon/(1-epsilon))<6/295. Its absolute
angular deviation from West is consequently less than 1/9. Let ell be
the actual center of that real leaf. Its radius is d+1/2, so

    -91/60<ell_x<-161/108,
    |ell_y|<91/540<1/5.                               (13)

Here cos(1/9)>1-1/162=161/162 and d+1/2>3/2 supply the
upper x bound. No boundary-resultant direction is substituted
for this actual physical leaf center.

### 5.1. The entire West own-side contact

If KD is West, every point of D is in x<=p_K-1. Its actual
center satisfies c_x<=p_K-3/2<-89/60. The universal center
bound |c|<91/60 gives |c_y|<sqrt(1/10)<1/3. Both this
center and ell have x in (-91/60,-7/5), and their vertical
difference is less than 1/3+1/5=8/15. Hence

    |c-ell|^2<(7/60)^2+(8/15)^2<1.

Their actual incircles contradict nonoverlap. This treats every
original West-side mean and every orientation of D.

### 5.2. Every strict Northwest contact, with every D owner

Its original point is the actual K upper-left vertex

    P=(p_K-1,k)=(-X,Y),
    59/60<X<=1,       -epsilon<=Y<0.                 (14)

The bounds on k here sharpen (9) by the genuine South leaf:
k=1-sqrt(d^2-p_K^2) in the strict case and k=-epsilon in
the owned case. In both, -epsilon<=k<0. Let c be the actual
boundary D center and v=c-P. The real square gives |v|<=1/sqrt(2).
Every boundary center in this high radius domain satisfies

    |c|^2>11/6.                                       (15)

Indeed |c|>=R-1/sqrt(2)>sqrt(17)/2-1/sqrt(2), whose squared
value is 19/4-sqrt(17/2)>11/6; the last radical comparison is
17/2<(35/12)^2. Every physical circle mask obeys this bound.

Since |P|^2<3601/3600 and |v|^2<=1/2, (15) gives

    P.v>1199/7200.

Using |Y|<1/60 and |v_y|<71/100, one obtains

    -X*v_x>1199/7200-71/6000>3/20,
    v_x<-3/20.                                       (16)

The exact final reserve before division by X<=1 is 169/36000.

Put w=ell-P. Equations (13)--(14) give

    -8/15<w_x<-53/108,       |w_y|<5/27.

Together with (16), this yields the actual dot-product bound

    v.w>(3/20)*(53/108)-(71/100)*(5/27)=-25/432.

Therefore the distance between the unchanged D center and the
unchanged real H leaf center satisfies

    |c-ell|^2=|v-w|^2
       <1/2+(8/15)^2+(5/27)^2+25/216
       =136247/145800<1.                              (17)

The exact positive reserve is 9553/145800. Again the actual
incircles overlap, a contradiction. This proof uses only that D
is physically boundary and contains its actual point P. It keeps
every D orientation, contact owner, circle mask and weight; no D2
concurrence or D circle direction has been presumed.

Sections 1--5 exclude the entire original nonparallel B interface.

## 6. The complete parallel B interface with both hub sides owned

Return to the other B3 alternative from Section 1: both original
B normals are West, with their full unchanged weighted-height
equation. Suppose both hubs own their contacts with B. Their
actual horizontal intervals are then both

    [epsilon-1,epsilon].

The hubs have disjoint interiors and physically touch each other.
Their two unit vertical intervals therefore abut. Label the upper
one H and write their exact frames as

    H=[epsilon-1,epsilon] times [q,q+1],
    K=[epsilon-1,epsilon] times [q-1,q].               (18)

H's genuine near point gives q<=epsilon, and K's gives q>=-epsilon.
Every original HB,KB,HK mean remains arbitrary; no weighted mean
has been used as a new physical contact.

On the upper H, the East and West own-axis supports have heights
epsilon and 1-epsilon, both below d. South has height -q<=epsilon.
The lower-right corner is too near O; the lower-left has squared
norm at most (1-epsilon)^2+epsilon^2<d^2. The upper-left has norm
strictly greater than d, since

    (1-epsilon)^2+(1+q)^2
       >=2*(1-epsilon)^2>(1+epsilon)^2.

The remaining genuine S possibilities are North, giving q=epsilon>0,
or the upper-right radial vertex, giving

    q+1=sqrt(d^2-epsilon^2)=sqrt(1+2epsilon)>1.

Thus every genuine S leaf of the upper hub requires q>0. Reflection
of the same complete feature cover at the lower hub requires q<0.
This is impossible. It includes q=0 and both near-point endpoints,
and uses no hub force equation or load condition on D.

## 7. Exact completed and uncompleted original scope

Both conclusions in the introduction are whole interface exclusions
at the original H4/K4/B3/D2 graph. The preselection is only the
existing finite true-B3 singleton choice, before extraction. No
normal is rotated afterward, no force is deleted, and no original
side mean, pose or physical circle mask is changed.

The remaining high A8 domain is precisely a parallel pair at B with
at least one hub not owning its B contact. Those genuine hubs may
have tilted frames and keep all four of their forces. This source
does not claim those cases closed. The whole A8 assembly, every
coarse/fine ledger and all remote files remain unchanged.

No numerical pose, sampled angle, interval certificate, Lean
compilation or CI is used. All displayed estimates are uniform
hand inequalities in the original complete domains.
