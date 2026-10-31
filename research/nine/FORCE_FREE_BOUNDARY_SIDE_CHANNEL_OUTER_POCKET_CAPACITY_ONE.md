# A width-one boundary channel has outer capacity one at arbitrary endpoint degrees

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed geometric hand theorem, submitted for full independent review.** The theorem retains every actual endpoint mask, aligned application mean and exposed vertex. Neither endpoint is assumed to have degree two or a proper concurrence. It supplies a whole exterior capacity statement, not an occupied-transmitter proximity statement.

Put Q=1105/256, r=5/4 and t=r/sqrt(2). Retain the actual closed unit squares X,H,Y in D_R, 2<=R<=sqrt(Q), with pairwise disjoint open interiors. The two boundary endpoints physically touch the containing circle. Their unchanged applications have the complete width-one chart

    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h), P_Y=(b,h), v<=h<=v+1,
    P_X in X intersect H, P_Y in Y intersect H,
    X subset {x<=-a}, Y subset {x>=b}.                 (1)

No force equation or endpoint degree is imposed in the geometric theorem.

The independently reviewed force-free channel theorem gives h!=0. Reflect the entire actual chart if necessary so h>0. It then gives

    a,b>7/100, a+b=1,
    h>3/10,
    (c_X)_x<-29/60, (c_Y)_x>29/60,
    (c_X)_y>0, (c_Y)_y>0.                             (2)

Choose any actual physical circle corner z_X of X and z_Y of Y. Define the occupied crosscut

    z_X -- P_X -- P_Y -- z_Y.                         (3)

Close it by the containing-circle arc through (0,R), rather than the one through (0,-R). Call its bounded Jordan region Omega.

**Theorem.** Every additional whole actual unit in the closed bounded side of this loop, with open interior disjoint from X,H,Y, has distance strictly greater than 3/10 from O. There can be at most one such unit.

The result applies in particular to a genuine outer positive side channel whose endpoints are consecutive positively loaded boundary units: global circle-force balance selects exactly this upper closing arc. Section 8 supplies that join without any endpoint concurrence or deletion of an original chord.

## 1. Two complete force-free endpoint estimates

The preceding channel theorem proves, for every actual boundary endpoint with right support P=(-a,h), a,h>0,

    R^2 >= (a+1)^2+h^2,                              (4)

and, whenever h>=a,

    R^2 <= (a+1)^2+(h+1)^2.                          (5)

Its proof includes every axis mean and every exposed vertex and does not assume nonnegative center height. Its complete strict-center proof then supplies all of (2). We use (4) below; (5) is already part of that established entry.

A convenient fixed comparison is

    Q < r^2+1+sqrt(2)r = r^2+1+2t.                   (6)

After multiplication by 256 this is 449<320sqrt(2). Squaring positive sides gives the exact reserve

    2*320^2-449^2=3199>0.

Every boundary center has norm at least R-1/sqrt(2)>5/4 and below 91/60. Therefore the complete annular-center theorem applies to both X and Y: their entire closed r-circle intersections are connected closed arcs, their open intersections are the corresponding nonempty open arcs, and each radial-center point lies in the relative interior of its arc.

Because X is strictly left and Y strictly right, write their center lifts as

    pi/2<theta_X<pi, 0<theta_Y<pi/2.

The gap-facing endpoints of those actual closed arcs have angles

    alpha_X=pi/2+phi, alpha_Y=pi/2-psi,
    0<phi,psi<pi/2.                                  (7)

These definitions are physical intersections of the original endpoint squares with the same r-circle. They do not select a new application or alter a normal.

## 2. A below-port circle strand has a strict lateral margin

Consider the original left endpoint. An axis-owned horizontal support gives

    X=[-a-1,-a] times [B-1,B],
    B>1/2, B-1<=h<=B.

The strict center height in (2) gives B>1/2. Its physical circle corner is (-a-1,B), which has height at least h. Every original mean is retained.

For an oblique endpoint use its actual orthonormal axes

    u=(c,s), w=(-s,c), c,s>0, c^2+s^2=1,
    X=P_X+[-1,0]u+[0,1]w.

Put

    k=P_X.u=-ac+hs,
    j=P_X.w=as+hc>0.                                 (8)

The center's w-coordinate is j+1/2>0. Consequently its actual farthest physical circle corners are exactly

    P_X-u+w if k<=1/2,
    P_X+w   if k>=1/2.                               (9)

The equality k=1/2 retains both physical corners and any individual zero coefficient.

The adjacent corner in (9) has height h+c>h. The opposite corner has height h+c-s. Thus a chosen circle corner below h can occur only in the opposite alternative with s>c. Its physical farthest-corner condition k<=1/2 gives

    h <= (1/2+ac)/s < 1/sqrt(2)+a.                    (10)

Its exact radius is

    R^2=a^2+h^2+2+2a(c+s)+2h(c-s)
        <=a^2+h^2+2+2sqrt(2)a
        <2a^2+3sqrt(2)a+5/2.                         (11)

If a<=3/10, the increasing last expression gives

    R^2 < 9/50+(9/10)sqrt(2)+5/2
        < 9/50+9/7+5/2
        =694/175<4,                                  (12)

using sqrt(2)<10/7. The final reserve is 6/175. This contradicts R>=2.

Hence every chosen below-h circle strand satisfies a>3/10. Its complete segment z_X--P_X lies in x<=-a<-3/10. Every other chosen strand lies in y>=h>3/10. The reflected statement holds at Y with x>=b>3/10 in its below-h alternative.

This argument covers every physical corner individually. At a two-corner tie one may choose either actual corner; no positive coefficient is required at the geometric corner.

## 3. The actual loop is proper and excludes the central disk

The endpoint supports have a positive horizontal gap of one, so X and Y are closed-disjoint. Also P_X,P_Y lie strictly inside D_R. For completeness, two distinct interior-disjoint contained unit squares cannot share a containing-circle point: both actual right-angle interior tangent sectors there lie strictly inside the same inward tangent half-plane, and two such open right angles cannot have disjoint interiors in that strict half-plane. This is the same physical circle-point exclusion used by the boundary-order source.

The segments z_X--P_X and P_Y--z_Y therefore meet the containing circle only at z_X and z_Y, by strict convexity of the disk. Their interiors stay in their respective actual endpoint units. Their horizontal coordinates lie on opposite sides of the middle segment, and each is strictly monotone in x. Thus (3) is a simple proper occupied disk crosscut. The upper circle arc closes it to an ordinary Jordan loop.

Section 2 puts every point of its endpoint strands strictly outside the closed disk D_(3/10). The middle segment has height h>3/10, and the outer circle has radius R>=2. The entire loop therefore misses that closed central disk with a strict compact margin.

The downward vertical ray from O avoids the loop: the two endpoint segments have x<=-a<0 and x>=b>0, the middle segment has positive height, and the chosen outer arc omits (0,-R). Hence O lies in the unbounded side. The connected closed disk D_(3/10) misses the loop and contains O, so all of it lies in that same unbounded side. The closed bounded Jordan region is compact and disjoint from D_(3/10). Every whole unit in it therefore has distance strictly greater than 3/10.

This proves the claimed clearance without asserting that the entire pocket lies above y=h. A below-h endpoint strand is permitted and is controlled by its strict lateral margin.

## 4. Every additional unit has a connected inner arc longer than 45 degrees

Let E be an actual unit in the stated bounded side. By Section 3 it has distance d_E>3/10 from O. Let q_E be its nearest point to O. Elementary convexity gives the actual geometric half-plane

    E subset {z:(q_E/d_E).z>=d_E}.

This is only a support half-plane used to estimate the unchanged unit; it does not reselect a stress normal or create a new contact.

The force-free cap-arc theorem in Section 1 of GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md applies because d_E>1/4 and E is contained in D_(sqrt(Q)). Its entire open-interior intersection with |z|=r is one connected open arc of length strictly greater than pi/4. It includes E's actual radial-center point.

Different open units have disjoint such arcs. It remains to route all of them into a single interval of length at most pi/2. That routing is supplied in Section 7 after a complete endpoint-angle bound.

## 5. Low port heights: the full endpoint scalar applies without properness

Assume

    3/10<h<t=r/sqrt(2).                               (13)

First every original endpoint application lies strictly inside the r-circle. Indeed, if a^2+h^2>=r^2, then a>t by (13). The universal lower estimate (4) would give

    R^2>=a^2+h^2+1+2a>r^2+1+2t>Q,

contrary to (6). Reflection gives the same strict conclusion at Y.

### 5.1. The exact pure scalar input

For |k|<r write A(k)=sqrt(r^2-k^2) and

    f(k,j)=((j-k)A(k)+k^2+jk)/r.                      (14)

Sections 2.1--2.3 of GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md prove, by complete polynomial and radical comparisons on the displayed continuous domains,

    -7/8<=k<=1/2,
    j>=sqrt(4-(k-1)^2)-1  => f(k,j)>71/100>1/sqrt(2),

    1/2<=k<=1,
    j>=sqrt(4-k^2)-1      => f(k,j)>41/50>1/sqrt(2).   (15)

These are pure scalar lemmas. Their proofs contain no degree, component, concurrence or physical properness premise. We import only these fully printed local inequalities, not that source's simple-cycle theorem or its earlier proper-port entry.

### 5.2. Every oblique physical circle mask has that exact scalar entry

Use (8)--(9). In the opposite-circle alternative,

    R^2=(k-1)^2+(j+1)^2, k<=1/2, j>0.

Since R^2<=Q and j+1>1,

    k>1-sqrt(Q-1)>-7/8.

The last comparison follows from (15/8)^2-(Q-1)=51/256>0.

Also j+1>r. Otherwise j<=1/4, and the circle equation with R>=2 and k<=1/2 would force

    k<=1-sqrt(4-r^2)<-1/2.

But h=ks+jc<j<=1/4, contradicting h>3/10. No sign comparison between c and s was used.

Thus the actual opposite-circle pair (k,j) satisfies the first complete domain in (15), for every tilt, including the formerly improper c<s alternative.

In the adjacent-circle alternative,

    R^2=k^2+(j+1)^2, k>=1/2.

Because a,c>0 and s<1, we have k<h<t<1. Therefore j+1>sqrt(3)>r, and the second domain in (15) applies. The physical two-corner tie k=1/2 is included in both calculations, with its original complete circle-resultant interval untouched.

Because the actual port is strictly inside the r-circle and j+1>r, the edge P_X+[0,1]w crosses that circle at exactly

    k u+A(k)w.

It is the gap-facing endpoint of X's connected upper inner-circle arc. Its angle is gamma+arccos(k/r)=pi/2+phi, where gamma is the actual angle of u. Rotating (8) into these coordinates gives the exact identity

    F_X:=a(sin(phi)+cos(phi))
             +h(cos(phi)-sin(phi))=f(k,j)>1/sqrt(2).   (16)

This is an identity for the unchanged original point and mean, not a comparison contact.

### 5.3. Every aligned support and original mean

For an axis support write X=[-a-1,-a] times [B-1,B], with B>1/2 and B-1<=h<=B. Its physical radius is

    R^2=(a+1)^2+B^2.

Section 4 of the same scalar source proves (16) for all four actual possibilities: gap endpoint on the right or upper face, with phi<=pi/4 or phi>=pi/4, including the face join. Here is the precise inheritance of its hypotheses:

* For the right-face phi<=pi/4 branch, its inequalities use a>0, h>0, the original lower mean bound h>=B-1, and the first pure scalar domain in (15).
* For the upper-face phi<=pi/4 branch, its comparison uses R>=2, h>3/10 and B<=r.
* For the upper-face phi>=pi/4 branch, it uses the unchanged upper mean bound h<=B and the second domain in (15).
* For the right-face phi>=pi/4 branch, it uses exactly h<t, a<1 and the negative sign of cos(phi)-sin(phi).

All those premises were established here geometrically. Its weak B=1/2 endpoint is retained by that proof, although the present channel entry makes B>1/2. No degree-two equation or proper concurrence occurs in those four scalar arguments.

Reflection gives the corresponding inequality at the actual right endpoint:

    F_Y:=b(sin(psi)+cos(psi))
             +h(cos(psi)-sin(psi))>1/sqrt(2).         (17)

### 5.4. The full low-height free interval

If phi+psi>=pi/2, put delta=phi-pi/4 and epsilon=psi-pi/4. Then delta,epsilon belong to (-pi/4,pi/4), delta+epsilon>=0, and

    sin(delta)+sin(epsilon)
      =2sin((delta+epsilon)/2)cos((delta-epsilon)/2)>=0.

Since a,b>0 and a+b=1,

    F_X+F_Y
      =sqrt(2)[a cos(delta)+b cos(epsilon)
                    -h(sin(delta)+sin(epsilon))]
      <=sqrt(2).

This contradicts (16)--(17). Therefore

    alpha_X-alpha_Y=phi+psi<pi/2                    (18)

throughout the entire low-height domain, for all original endpoint masks and means.

## 6. High port heights: one closed own-frame comparison handles all features

Now assume

    h>=t=r/sqrt(2).                                  (19)

We prove alpha_X<=3pi/4. Reflection will give alpha_Y>=pi/4, hence a free interval of length at most pi/2.

First a<t. If a>=t, (4) and (19) would imply

    R^2>=(a+1)^2+h^2>=r^2+1+2t>Q,

contradicting (6).

Set q=(-t,t), an actual point of the fixed r-circle at angle 3pi/4. We are not moving any unit or application.

### 6.1. Axis support with the full mean

Write X=[-a-1,-a] times [B-1,B], B-1<=h<=B. Since 0<a<t<1, the horizontal coordinate of q lies strictly between the two vertical faces.

We also have t<=h<=B. If t>=B-1, q belongs to the actual closed square and therefore to its connected closed r-circle arc. Its gap-facing endpoint has angle at most 3pi/4.

If t<B-1, every point of the square has height greater than t. Its upper inner-circle arc lies entirely between angles pi/4 and 3pi/4, and the conclusion is strict. These cases retain every mean endpoint and the equality t=B-1.

### 6.2. Oblique support: all four own-face alternatives

Use (8). In its actual own frame the square is the rectangle

    [k-1,k] times [j,j+1], j>0.

The point q has own coordinates

    k_q=t(s-c), j_q=t(s+c), k_q^2+j_q^2=r^2.

Since a<t and h>=t,

    k-k_q=(t-a)c+(h-t)s>0.                            (20)

Thus q cannot violate the upper u-face. The other three faces and their closed complement are exhaustive.

If k_q<k-1, then for every upper-circle angle theta in [3pi/4,pi] its u-coordinate is

    r cos(theta-gamma)<=r cos(3pi/4-gamma)=k_q<k-1,

where 0<gamma<pi/2 is the angle of u. No such point belongs to X. Its connected arc has center angle in (pi/2,pi), so its gap-facing endpoint is strictly below 3pi/4.

If j_q>j+1, then j+1<r. The opposite-circle alternative k<=1/2 is impossible: the same circle calculation as in Section 5.2 gives k<-1/2 and h=ks+jc<j<1/4, contradicting (19). Hence the actual radius is k^2+(j+1)^2=R^2 and

    k>sqrt(4-r^2)>3/2.

The actual center's two own coordinates consequently obey

    k-1/2>1, 0<j+1/2<3/4.

Its angle relative to u is less than pi/4. Since gamma<pi/2, its actual upper-left center angle is less than 3pi/4. The gap-facing endpoint precedes the radial-center point of its connected arc and is smaller still.

If j_q<j and gamma<=pi/4, then for every theta in [3pi/4,pi],

    r sin(theta-gamma)<=r sin(3pi/4-gamma)=j_q<j.

Again there is no square point in that angular interval, so alpha_X<3pi/4.

The remaining subcase j_q<j and gamma>=pi/4 is impossible. Here k_q>=0, and (20) gives k>k_q>=0. Therefore

    k^2+j^2>k_q^2+j_q^2=r^2, j>j_q>=t.

For both physical masks in (9) the exact radius satisfies

    R^2>=k^2+j^2+1+2j.

For k>=1/2 this is equality. For k<=1/2 it follows from
R^2=k^2+j^2+2+2j-2k. Thus R^2>r^2+1+2t>Q, a contradiction. The common gamma=pi/4 endpoint is included.

Finally, if none of the three strict face violations occurs, (20) and the remaining weak bounds place q in the actual closed square. Its angle belongs to the connected closed intersection, so alpha_X<=3pi/4.

This exhausts the full actual oblique support, including every physical two-corner tie. No assumption that the original port lies inside the r-circle was made in this high-height proof.

Reflection proves alpha_Y>=pi/4. Hence

    alpha_X-alpha_Y<=pi/2                            (21)

for every h>=t, with equality retained.

## 7. Complete actual inner-circle routing and capacity

Let z be an r-circle point in the open interior of an additional unit in Omega. It avoids both closed endpoint squares. We prove

    alpha_Y<arg(z)<alpha_X                            (22)

on the upper lift. This is a winding argument for the actual loop (3), not a radial-visibility assertion.

First no free lower-semicircle point belongs to Omega. On the left lower quadrant, X's connected closed r-circle arc is an interval contained in (pi/2,3pi/2) and contains theta_X<pi. A point in [pi,3pi/2) outside that interval can follow the r-circle toward 3pi/2 without meeting X. The whole path has negative x, so it avoids Y; its nonpositive height avoids the middle segment. The endpoint strands lie in X and Y, so it avoids them too. From (0,-r) the downward vertical ray reaches infinity without meeting the upper outer arc or any other part of the loop.

The reflected argument handles the right lower quadrant. Thus every free r-circle point in the bounded region has angle in (0,pi).

Next suppose its angle exceeds theta_X. The actual radial-center point of X lies in its open interior, so its x-coordinate is strictly less than -a. Monotonicity of cosine on the upper semicircle shows that the path toward angle pi stays strictly left of x=-a and avoids the middle segment. Connectedness of X's circle intersection, which contains theta_X, means this path avoids X once it begins outside X on the increasing-angle side. It avoids Y by its negative x-coordinate. Continuing along the lower left quadrant and then the downward ray again reaches infinity without crossing the loop.

The reflected argument excludes angles below theta_Y. Hence every such bounded-region point lies strictly between theta_Y and theta_X. Since it avoids the two complete closed endpoint arcs, it must lie strictly between their gap-facing ends, which is (22).

This argument uses only actual connected endpoint arcs, the occupied crosscut, and a path in the complement of that crosscut. The auxiliary escape path is not a physical motion of any packing square. Additional obstacles may be crossed by this topological test; only avoiding the defining Jordan loop is relevant to its winding label.

Section 4 gives each complete extra one connected open r-circle arc longer than pi/4. By (22), every point of every such arc lies in the same free interval (alpha_Y,alpha_X). Its length is less than pi/2 in (18) and at most pi/2 in (21). Two disjoint open units would therefore occupy a combined angular length strictly greater than pi/2 in an interval of length at most pi/2. This contradiction proves the whole geometric capacity-one theorem.

At weak contacts, the open interior of each extra avoids the entire occupied loop; its connectedness fixes its bounded-side label. Closure then places the whole unit on that closed side. All original shared means, physical contacts and zero-weight subdivisions are retained.

## 8. Genuine outer-channel joins at arbitrary endpoint degrees

Consider an actual positive component with at least three positively loaded boundary units, retaining every force and its complete circle resultant. Suppose a genuine width-one unloaded degree-two channel X-H-Y occurs on its outer face, and X,Y are consecutive positively loaded units in the corresponding circular order.

The full H force and torque give exactly the unchanged chart (1). The preceding force-free entry yields (2). Thus the upper center gap is

    gamma=theta_X-theta_Y in (0,pi).

It is in fact strictly less than 5pi/6. The actual center distance satisfies

    |c_X-c_Y|
       <=|c_X-P_X|+|P_X-P_Y|+|P_Y-c_Y|
       <=1+sqrt(2).

Each boundary center radius is strictly greater than 5/4. If gamma>=5pi/6, the cosine law instead gives

    |c_X-c_Y|^2
       >25(2+sqrt(3))/16>(1+sqrt(2))^2,               (23)

a contradiction. The last comparison is the exact local metric inequality printed in Section 4 of FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md; it uses only these two radii and the stated angle, not a four-body path.

Every actual physical circle corner and every full nonzero circle resultant is strictly within pi/12 of its own center direction. The positive resultants are distinct and sum to zero by the full component force equations. With at least three such directions, each consecutive circular gap is strictly less than pi: a gap at least pi puts all vectors in a closed half-plane with at least one strictly positive inward projection.

If the original channel used the complementary, lower center arc, that gap would exceed 7pi/6 by (23). Its corresponding resultant gap would still exceed pi after both strict pi/12 endpoint corrections. This is impossible. Hence the genuine consecutive loaded gap uses the upper arc of Section 1.

The physical plane embedding and its actual exterior circle spokes give precisely this circular order. For this caller choose z_X and z_Y to be exactly the unchanged physical circle corners used by those original spokes; the geometric theorem allows these choices, so no circle corner is moved and no physical corner interval is swept. Replace the original center/contact boundary path through X,H,Y by (3) only in the geometric winding construction. These paths deform within the actual chain X union H union Y; X and Y are closed-disjoint and each meets the original H at its actual contact. Every extra's open interior avoids that whole occupied union, so its winding label is unchanged.

Thus the actual exterior channel pocket, including all its zero-weight contact subdivisions, is contained on the upper bounded side counted above. The whole capacity-one result applies. An endpoint retains any other actual positive forces and its true degree; no degree-two equation is used there.

For the original D02.L0134 row, take

    X=W=0, H=5, Y=B=4.

Its positive rim is 01,12,23,34,45,50 and its original chord is 02. The loaded set is {0,1,3,4}; X has true degree three, H true unloaded degree two, and Y true loaded degree two. The four positive boundary directions follow the original outer order 1,0,4,3. The same component balance and the actual outer 0-5-4 chain therefore meet the preceding hypotheses literally.

For D02.L0135 the literal channel is 3-4-5, with 4 genuinely unloaded and 3,5 physically boundary. The same reasoning applies regardless of their other-neighbor properness. No original chord is removed in either application.

The theorem proves the entire side-channel outer capacity at those interfaces and at the displayed broader arbitrary-degree scope. It does not claim the diagonal channel alternative, a hub-closing-pocket bound, or a joint central/exterior allocation. In particular central capacity one, another closing-pocket capacity one and this capacity one would still permit the allocation (1,1,1). Neither original four-load row is declared closed here.

The stronger occupied-side-channel implication dist(O,H)<1/60 remains a separate obligation at a higher-degree endpoint. It is not inferred from the new capacity theorem.

## 9. Complete direct sources and verification boundary

| Source | SHA256 | Exact operative use |
| --- | --- | --- |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md | 1a40004509d14eaa228ab52a4eb3280ed0f96df60e3891666f380124b5cacf9c | Entire actual width-one entry, strict center heights, port margin and the universal force-free endpoint radius estimate |
| GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md | 9b13cab840002bddc77ccdba962fa3c833b111a9d9f373f476ea2a37d0fd8a1e | Only the complete pure scalar lemmas in Section 2 and all-mean aligned endpoint comparisons in Section 4, at their explicitly verified local hypotheses |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Force-free Section 1: each actual unit in a supporting half-plane of distance greater than 1/4 has one connected open r-circle arc longer than pi/4 |
| ANNULAR_CENTER_ARC_AT_23_25.md | 7628a82b3639f1e75680fec3e85baf62368a611d397b2ac01ae936ec07a14290 | Complete actual closed endpoint arc and its radial-center point; applied to physical boundary centers, whose radii exceed 5/4 |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Only its degree-free corner/resultant-to-center angle bound in Section 1 and the exact two-center metric comparison in Section 4 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original physical embedding, occupied center/contact routes and exterior circle spokes in the positive-channel caller |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Physical circle-point exclusion and consistent actual boundary/circle order |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | The unchanged two original D02 graph/load substitutions and their true degrees |

The geometric proof has no unproved higher-degree concurrence premise. The old simple-cycle capacity or proximity conclusion is never imported as an arbitrary-degree theorem. Every new endpoint-entry, high-height, actual-loop, winding, and all-mask step is printed above. All imported scalar and annular results are used at their complete proved scopes.

Only exact algebra and fixed rational comparisons were used. There is no numerical pose search, angle mesh, finite pose certificate, normal reselection, mean replacement, circle-mask reduction, deleted edge, invented physical transmitter, Lean compilation, CI, remote action or shared-ledger mutation.

