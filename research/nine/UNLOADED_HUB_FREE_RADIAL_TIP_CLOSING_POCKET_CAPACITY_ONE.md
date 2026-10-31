# A free contact to a radial two-circle tip has closing-pocket capacity at most one

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed whole free-contact pocket theorem and literal original D02 physical-two-circle feature exclusion, submitted for full independent review.** The proof has no own-axis premise at the unloaded hub. It exhausts every actual owner and physical feature of both remaining triangle edges, retains every original third-side mean, and uses the true endpoint two-force equation only at the actual loaded endpoint T.

The local triangle calculation first forces a single complete W-side chart. The full hub force and its actual support geometry then put the original T port in a short part of the opposite hub side. A genuine occupied crosscut places the whole closing pocket in one fixed half-plane and angular interval. Two exact inner-circle points give the final uniform capacity bound.

No original row is declared closed by this feature alone.

## 1. Complete unchanged physical theorem

Put

    Q=1105/256, sigma=1/sqrt(2), rho_c=9/8,
    2<=R<=sqrt(Q).

Keep actual pairwise interior-disjoint closed unit squares in the unchanged disk D_R, with their original complete physical equations. Suppose the entire positive component is an unloaded U and the loaded boundary path

    V,W,B_3,...,B_(k-1),T, 3<=k<=6,

together with exactly the three original spokes UV,UW,UT. Its actual exterior-face order is U,V,W,...,T,U. U has true positive degree three; V and T have true positive degree two; W has true positive degree three; every remaining path body has its original degree two. All other actual physical units remain.

Assume V has two physical circle corners. Assume the original UV normal is free: it strictly exposes the original common vertex in both U and V. No owner, frame, application, mean or physical circle mask is prescribed at UW, VW, UT or any other edge. Every individual circle coefficient, including zero coefficients at physical corners, remains unchanged.

**Pocket theorem.** The actual closing exterior pocket through U between V and T has capacity at most one whole additional unit square.

**Original consequence.** In M6.B6.HEXAGON.D02.L01345, the entire feature with a physical-two-circle V and a free original UV normal is impossible, for every remaining owner, mean, mask and orientation.

The general local geometry below uses only the true U3,V2 equations and physical boundary status of W,T. W is never made a two-force body. True T2 is used only for the actual closing-pocket routing. If k=3, the full unloaded-three-force return separator already makes T closed-disjoint from W, contrary to the path edge WT; that endpoint of the stated k range is thus included directly.

## 2. The actual V chart and all original VW features

A unit with two physical circle corners in this radius range has exactly one zero own center coordinate. Rotate and, if necessary, reflect the complete physical data about the unchanged origin. Since a circle corner cannot belong to a second contained square, the free UV contact is an inner vertex. We may write

    V=[-1/2,1/2] x [d,d+1],
    d=sqrt(R^2-1/4)-1,
    P=(-1/2,d),
    n=n_UV=(xi,zeta), xi,zeta>0,
    j=zeta/xi.                                             (1)

Both physical outer corners and their full original weights remain. The exact radius comparisons give

    187/200<d<61/60.                                       (2)

Indeed

    15/4-(387/200)^2=231/40000>0,
    (121/60)^2+1/4-Q=31/57600>0.

Let mu>0 be the original UV magnitude, nu>0 the original VW magnitude, M its actual application and m the original V-to-W unit normal. The full V force and torque are

    F_V=mu*n-nu*m,
    nu*det(M,m)=mu*det(P,n)
                 =mu*(-zeta/2-d*xi)<0.                    (3)

The full all-owner common-point theorem applies to true V2 and physical-boundary W, since R^2>=4>13/4. Consequently

    P does not belong to W.                               (4)

We now exhaust the V-owned normals.

- For West, det(M,West)=M_y>=d>0, contrary to (3).
- For South, W lies wholly in y<=d and contains an actual point M with |M_x|<=1/2 and M_y=d. Unit width gives min_W y<=d-1. The full radial half-strip theorem instead gives min_W y>d-1 for every physical boundary unit meeting this actual strip.
- For East, W lies in x>=1/2. At the strict U vertex P, both inward U axes have negative scalar product with n. At most one has positive horizontal component, and that component is strictly below one: equality would be the East axis, with positive scalar product with n. Thus max_U x<P_x+1=1/2, so UW cannot physically touch.
- For North, W would have min_W y=d+1 and width at least one, hence max_W y>=d+2>R, impossible.

If m is not a V own axis, it exposes a V vertex. Neither physical outer corner can be shared, and P is excluded by (4). Therefore the actual VW point and original normal satisfy

    M=Q_V=(1/2,d),
    m is strict Southeast.                                (5)

Suppose Q_V were a vertex of W. Its inward right-angle tangent sector must avoid V's open Northwest tangent quadrant. Every right-angle sector with that property is wholly in the closed East half-plane or wholly in the closed South half-plane: otherwise its angle interval would meet the open Northwest quadrant. The whole unit W lies in the same half-plane. The East alternative cannot touch U by the strict horizontal reach just proved. The South alternative has min_W y<=d-1 and is excluded by the same radial half-strip theorem at Q_V.

Thus Q_V is in the relative interior of a W side. The original m is its unique inward side normal. Write the actual square, without changing Q_V, as

    f=(gamma,eta), g=(eta,-gamma),
    gamma,eta>0, gamma^2+eta^2=1,
    m=g,
    W=Q_V+[-beta,1-beta]f+[0,1]g,
    0<beta<1, tau=1-beta in (0,1).                         (6)

This covers every possible initial VW feature. Side endpoints at W were excluded by the preceding complete tangent-sector argument; they were not assumed absent.

## 3. The full W physical mask and two uniform support bounds

The force-free radial inner-corner theorem applies literally to (6), with d>11/12. It gives

    beta*gamma<1/4,                                        (7)

forces W's unique actual physical circle corner to be

    Z_W=Q_V+tau*f+g,

and gives its exact circle equation

    d=F(gamma,tau)
      :=(tau^2+tau*gamma+eta)/
           [2*(1+gamma-tau*eta)],
    eta=sqrt(1-gamma^2).                                  (8)

Every initially possible W mask is covered by that theorem. No W3 equation or individual circle weight is discarded.

For use below, F increases strictly with tau, decreases strictly with gamma along the actual quarter circle, and increases with an independent algebraic comparison value of eta when the denominator stays positive. The continuous derivative numerators, after positive factors are removed, are respectively

    (2tau+gamma)*(1+gamma-tau*eta)
       +eta*(tau^2+tau*gamma+eta)>0,

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma<0.

These are the complete monotonicities proved in the radial inner-corner theorem; they do not replace an actual W orientation.

We also have

    gamma<5/6, eta>1/2.                                   (9)

Otherwise monotonicity, tau<1 and sqrt(11)/6<5/9 give

    d<F(5/6,1)<43/46<187/200,

contrary to (2). The last exact reserve is 1/4600.

In the fixed V coordinates, (7) gives

    min_W x=1/2-beta*gamma>1/4.                           (10)

The radial half-strip theorem at the actual Q_V also gives

    min_W y>d-1.                                          (11)

Both are strict statements about the entire actual closed W.

## 4. The complete U frame and all U-owned UW normals

Because U touches W, it has a point to the right of 1/4. Its strict maximum-n vertex is P. Thus one inward U axis has positive horizontal component; name the actual inward axes

    u=(c,-s), v=(-s,-c),
    c,s>0, c^2+s^2=1,
    U=P+[0,1]u+[0,1]v.                                   (12)

Strict UV exposure and (10) give

    j>c/s,
    c-1/2=max_U x>=min_W x>1/4.
                                                               (13)

Consequently c>3/4, s<sqrt(7)/4<2/3 and c>s.

We first exclude every original UW normal owned by U, including all possible original means. The radius-free unit-triangle side-normal theorem applies to the actual triangle U,V,W. Every U-owned UW axis must have nonnegative scalar product with n. The axes u and v have negative scalar product with n and are excluded. The support side for -u has x<=-1/2 and cannot meet W by (10).

The only remaining U-owned normal would be -v, with its unchanged actual application P+t*u, 0<=t<=1. Write omega>0 for the UW magnitude. In the basis u,v, both components of mu*n+omega*(-v) are strictly negative. Full unloaded U force therefore makes the third normal strictly positive in both own components, and its actual application is

    B=P+u+v.

Taking the entire original U torque about P yields

    omega*(t-1)
       -mu*[(c-s)*zeta+(s+c)*xi]=0.                        (14)

The left side is strictly negative because 0<=t<=1 and c>s. This contradiction includes both actual side-mean endpoints. Thus UW is not U-owned.

The actual UW application is now a strictly exposed U vertex. P and P+v have x<=-1/2 and cannot meet W. The bottom vertex B has

    B_y=d-c-s<d-1,

and cannot meet W by (11). Hence the original UW application is exactly

    P_W=P+u.                                              (15)

This deduction uses every possible original support feature of U.

## 5. Complete W feature cover at the actual P_W

Put L_W=Q_V-beta*f. The other three actual W vertices satisfy

    (L_W+f)_x=1/2+tau*gamma>1/2,
    (L_W+g)_x=1/2-beta*gamma+eta>3/4,
    (L_W+f+g)_x>1/2.

Here (7),(9) were used. But max_U x=c-1/2<1/2. Thus neither a point on either far W face nor any of those three vertices can be the actual UW application.

There remain exactly the two sides from L_W:

    L_W+[0,1]f, the minimum-g side;
    L_W+[0,1]g, the minimum-f side,

including their common vertex L_W. This list includes a free UW normal at L_W; no W ownership has yet been assumed.

### 5.1. The whole minimum-g side, including its free vertex endpoint, is impossible

If P_W lies on the minimum-g side, then

    (c-1)*eta+s*gamma=0.

Since c,s,gamma,eta are positive, this is exactly

    c=1-2gamma^2,
    s=2gamma*eta,
    Q_V-P_W=2gamma*f,
    beta>=2gamma.                                        (16)

It includes P_W=L_W. Also c>3/4 implies gamma<1/(2sqrt(2)), so eta>gamma.

The original two pair lines at V meet at

    q=P+ell*n=Q_V-r*g,
    q=(-1/2+k,d+j*k),
    k=gamma/(gamma+eta*j)>0.                              (17)

The q height is positive. Its full circle resultant is

    F_V=Lambda*(z,d+1),
    Lambda>0, -1/2<=z<=1/2.

Torque about q makes q parallel to F_V. Their positive second coordinates make the proportionality positive. In particular the original lower circle-weight endpoint z>=-1/2 gives

    gamma*(2d+1)>=j*(eta-gamma).                         (18)

This keeps both physical circle corners and either zero individual coefficient. No assertion that q lies inside V is used.

By (13),(16), j>(1-2gamma^2)/(2gamma*eta). Equation (18), together with d<61/60, would require

    [1-(121/15)*gamma^2]*eta-gamma+2gamma^3<0.             (19)

If gamma<=3/10, the coefficient of eta is at least 137/500, eta>19/20, and gamma-2gamma^3<=123/500; the last function is increasing on this interval. The left side of (19) is therefore strictly greater than

    (137/500)*(19/20)-123/500=143/10000>0.

If gamma>3/10, (16) gives tau<=1-2gamma<2/5. Monotonicity in (8), followed by eta<1 at the comparison parameters, gives instead

    d<F(3/10,2/5)<32/45<187/200,

whose last reserve is 403/1800. Both continuous ranges contradict the actual equations.

Thus the whole minimum-g side, its endpoints, and the possible free normal at L_W are excluded.

### 5.2. The only remaining actual UW feature

The actual P_W is in the relative interior of the minimum-f side. Its original UW normal is necessarily f. Its position is exactly

    P_W=Q_V-beta*f+t*g,
    beta=(1-c)*gamma+s*eta,
    t=s*gamma-(1-c)*eta in (0,1).                        (20)

Because the original normal is not U-owned, it strictly exposes P_W in U. Therefore

    c*gamma-s*eta>0,
    gamma>s.                                             (21)

Equations (6),(20) are conclusions about the actual original contacts. No normal or application has been reselected.

## 6. A uniform upper bound on the entire U tilt

We prove

    0<s<2/5, c>9/10.                                     (22)

Suppose s>=2/5. Then c<=sqrt(21)/5<11/12, and (20) gives

    beta>gamma/12+(2/5)*sqrt(1-gamma^2),
    2/5<gamma<5/6.                                       (23)

The function on the right is concave in gamma. Three closed intervals cover this entire alleged domain.

For 2/5<=gamma<=1/2 its two endpoint lower bounds give beta>19/50. At gamma=2/5 use eta>9/10; at gamma=1/2 use eta>17/20. The latter, smaller comparison has reserve 1/600. Hence tau<31/50, and

    d<F(2/5,31/50)
       <11618/12475<187/200,                             (24)

using sqrt(21)/5<11/12 in the algebraic eta comparison. The final reserve is 369/99800.

For 1/2<=gamma<=13/20, concavity gives beta>7/20. At the second endpoint eta>3/4 gives the lower value 17/48, with reserve 1/240 above 7/20. Hence tau<13/20, and

    d<F(1/2,13/20)
       <649/745<187/200,                                 (25)

using sqrt(3)/2<7/8. The final reserve is 1903/29800.

For 13/20<=gamma<5/6, we have eta>11/20 and

    beta>13/240+11/50=329/1200>1/4.

Thus tau<3/4. At gamma=13/20 the comparison eta<4/5 gives

    d<F(13/20,3/4)<37/42<187/200,                        (26)

with final reserve 227/4200. All denominators in these comparisons are positive. Every interval contradicts (2), proving (22).

## 7. The actual third port is on a short part of the opposite U side

Both original U-to-V and U-to-W normals n,f have strictly positive horizontal and vertical components. Full unloaded U force makes the original U-to-T normal n_T strictly Southwest:

    (n_T)_x<0, (n_T)_y<0.                               (27)

In the U basis, n_T.v>0. Its entire support feature is consequently on the side from P+v to B=P+u+v, including either vertex. Keep its unchanged original application or side mean:

    P_T=P+v+rho*u, 0<=rho<=1.                           (28)

A point of a physical boundary unit must have norm at least R-sqrt(2), by the actual unit diameter. We use this at the actual P_T, without changing its force location.

First B cannot belong to a boundary unit. Its exact norm identity is

    R^2-|B|^2=2d*(1+c+s)+(c-s)-1.

For 0<=s<=2/5, the function
(2d+1)*sqrt(1-s^2)+(2d-1)*s is concave. At s=0 it is 2d+1; at s=2/5 it is strictly greater than (13/5)*d+1/2, which exceeds 2d+1 because d>5/6. Therefore

    (2d+1)*(1+c)+(2d-1)*s>=4d+2>2sqrt(2)*R.             (29)

The last strict comparison follows from
(2d+1)^2-2R^2=2d^2-3/2>0. Equation (29) is precisely

    |B|<R-sqrt(2).                                       (30)

At rho=s/c, the point on (28) is

    P_E=(-1/2,d-1/c).

By (2),(22), |d-1/c|<1/5. Consequently

    |P_E|^2<29/100<49/144<(R-sqrt(2))^2.                (31)

Here sqrt(2)<17/12, R>=2, and
49/144-29/100=181/3600>0.

Squared norm is convex along the segment from P_E to B. Equations (30),(31) exclude every rho in [s/c,1] as an actual boundary-T application. Hence

    0<=rho<s/c,
    P_T=(-a,b),
    1/2<a=1/2+s-rho*c<9/10,
    -1/5<b=d-c-rho*s<7/60.                            (32)

The lower height follows from b>d-1/c, the upper from b<=d-c. The possible endpoint rho=0 remains. No original side mean was set equal to a vertex.

## 8. A positive angular derivative along the entire closing U arc

We also have

    s>1/20.                                             (33)

Otherwise c>99/100 and the left vertex P+v has

    |(P+v)_x|<=11/20,
    |(P+v)_y|<13/200.

Thus

    |P+v|^2<(11/20)^2+(13/200)^2
              <49/144<(R-sqrt(2))^2,

with middle reserve 12079/360000. The other endpoint B satisfies (30). Convexity would put every possible port in (28) strictly inside the boundary annulus, impossible.

Combining (2),(33) gives the useful strict determinant

    det(P+v,u)=1+s/2-d*c>1/120.                         (34)

Also

    det(P,v)=c/2+d*s>0.                                (35)

These are signs for the actual U boundary segments. They do not substitute a concurrence polygon for the original occupied geometry.

## 9. Every physical T circle corner is left of V, and the actual center is left

Let Z be any actual physical circle corner of T, regardless of its individual coefficient. Suppose Z_x>=-1/2 and put w=Z-P_T. Equation (32) gives w_x>0. The original T minimum support and (27) give

    n_T.w>=0,

so w_y<0. The unit diameter, sqrt(2)<3/2 and (32) yield

    -1/2<=Z_x<1,
    -17/10<Z_y<1/4.

Consequently

    |Z|^2<1+289/100=389/100<4<=R^2,

a contradiction. Thus

    Z_x<-1/2 for every actual physical circle corner of T.   (36)

Let c_T be the actual center, r_T=|c_T|. Its actual port and boundary corner give

    |c_T-P_T|<=sigma,
    r_T>=R-sigma>5/4.                                  (37)

If (c_T)_x>=0, (32), sigma<3/4 and the port distance give
0<=(c_T)_x<1/4 and |(c_T)_y|<1. This contradicts
|c_T|^2>25/16 while the coordinate box gives |c_T|^2<17/16.
Therefore its angular lift is well defined by

    theta_T=arg(c_T) in (90,270) degrees.                 (38)

All owners, original means, one- and two-circle T masks and zero-weight physical T corners remain in (36)--(38).

## 10. Uniform T angle bounds over the whole port domain

We prove the two exact matching estimates

    theta_T<216 degrees;
    theta_T<215 degrees whenever d>=24/25.               (39)

The elementary angle inequalities imported from Sections 8 and 13 of the pinned two-circle pocket source are

    sin(36 degrees)>47/80,
    29/36<cos(36 degrees)<5/6,
    sin(36 degrees)<3/5,
    sin(35 degrees)>4/7,
    cos(35 degrees)>29/36,
    cos(35 degrees)<7/8.

The last two follow from monotonicity and cos(30 degrees)=sqrt(3)/2<7/8. Also sigma<99/140, so

    r_T>r_0:=181/140.                                    (40)

If the center height is nonnegative, both claims in (39) are immediate. The arguments below cover the remaining negative-height domain continuously, with the shared threshold s=1/5 included.

### 10.1. The entire range 1/5<=s<2/5

Suppose theta_T>=216 degrees, and write
psi=theta_T-180 degrees in [36,90), c=cos(phi), s=sin(phi).
Then

    c_T.v=r_T*sin(psi+phi).

The minimum of sine on this interval is at an endpoint. The first endpoint is the smaller one, because

    sin(36 degrees)*c+cos(36 degrees)*s
      <[(3/5)+(5/6)*(4/9)]*c
       =(131/135)*c<c.

The estimate s/c<4/9 follows from (22). Since P_T.v=1+s/2-d*c, it follows that

    (c_T-P_T).v
      >=c*(d+r_T*sin(36 degrees))
          +s*(r_T*cos(36 degrees)-1/2)-1
      >(169/100)*c+(27/50)*s-1.                         (41)

The two coefficient reserves are respectively 51/11200 and 37/25200. The final concave expression has its minimum at an endpoint of [1/5,2/5]. Using c>97/100 at the first and c>9/10 at the second, its endpoint values exceed

    7473/10000 and 737/1000.

Both are strictly above sigma<17/24; the smaller reserve above 17/24 is 43/1500. This contradicts (37).

For the stronger claim, let d>=24/25 and suppose theta_T>=215 degrees. Then

    R>101/50, r_T>r_1:=919/700,

because (49/25)^2+1/4-(101/50)^2=7/625>0.
For psi in [35,90), the sine endpoint argument is unchanged: now

    sin(35 degrees)*c+cos(35 degrees)*s
      <[(3/5)+(7/8)*(4/9)]*c<c.

The projection comparison is

    (c_T-P_T).v>(17/10)*c+(11/20)*s-1.                 (42)

The coefficient reserves are 1/98 and 191/25200. At s=1/5 and 2/5 the concave lower expression exceeds 759/1000 and 3/4. Both exceed sigma<17/24, the smaller reserve being 1/24. This contradicts (37) again.

### 10.2. The entire range 0<s<=1/5

Here c>97/100, and the unchanged port (32) satisfies

    1/2<a<=7/10,
    -1/10<b<7/150.                                      (43)

For the lower height,
187/200-100/97+1/10=79/19400>0.
The equality a=7/10 at a possible original endpoint is retained.

Its argument lies in (90,210) degrees, and |P_T|<1<r_0.
Suppose theta_T>=216 degrees. For angles from 216 to theta_T<270, the squared distance from P_T increases with angle: the angle difference from arg(P_T) stays in (0,pi). It also increases with radius above r_0, since |P_T|<r_0.

The radius-r_0 point at 216 degrees is strictly left of and below the entire port box (43). Therefore

    |c_T-P_T|^2
      >[r_0*(29/36)-7/10]^2
         +[r_0*(47/80)-1/10]^2
       =1/2+524405689/10160640000
       >1/2,                                            (44)

contradicting (37).

If d>=24/25, the stronger lower height is b>-2/25, with reserve
24/25-100/97+2/25=22/2425>0.
Now r_T>r_1. The same monotonicity at 215 degrees gives

    |c_T-P_T|^2
      >[r_1*(29/36)-7/10]^2
         +[r_1*(4/7)-2/25]^2
       =1/2+479428421/6223392000
       >1/2.                                            (45)

This proves both claims (39) on the entire remaining interval. No value of an actual pose or original side mean was sampled.

## 11. Two actual open-V inner points cover the entire radius interval

The following radius-rho_c points lie in the unchanged open V:

| Entire d range | Point angle phi_0 |
| --- | --- |
| d<=24/25 | 116 degrees |
| d>=24/25 | 115 degrees |

For the first point, the exact inequalities

    sin(26 degrees)<4/9,
    cos(26 degrees)>64/75

give -1/2<-rho_c*sin(26 degrees)<0 and
rho_c*cos(26 degrees)>24/25>=d.
Its height is below rho_c<d+1.

For the second, the exact half-angle inequalities

    sin(25 degrees)^2<43/240,
    cos(25 degrees)^2>197/240

give

    1/4-rho_c^2*(43/240)=119/5120>0,
    rho_c^2*(197/240)-(61/60)^2=1211/230400>0.

Thus its first coordinate is strictly between -1/2 and 0, and its height is strictly between d and d+1. These elementary inequalities are the printed exact comparisons from Sections 8 and 10 of the pinned two-circle pocket source; no physical port or force assertion from that source is imported.

The common threshold d=24/25 is included in both comparisons. Equations (39) give exactly

    theta_T<phi_0+100 degrees.                          (46)

The point at phi_0 belongs to the actual open V. It is not used as a new force application.

## 12. The actual closing crosscut places every whole extra in one cap

The actual VW moment is

    det(Q_V,g)=-gamma/2-d*eta<0.                         (47)

The degree-free boundary-pair moment theorem and angular-neighbor rule orient the whole actual loaded path V,W,...,T clockwise. Its closing exterior gap through U is counterclockwise from V to T. There is no additional physical edge among nonconsecutive path bodies: it would make a physical boundary cycle of length at most six.

The actual U ports have the boundary order V,W,T. In the clockwise U boundary order the vertices are P, P+u, B, P+v; the VW-side port is the actual P_W=P+u, while the original T port is on the side from B to P+v. Thus the closing U arc from P toward T omits the UW port and passes through P+v.

The full unloaded-three-force return separator makes T closed-disjoint from V and W, since V,W physically touch. Also U is physically circle-clear: otherwise U,V,W would be three mutually touching physical boundary squares, forbidden by the full physical boundary-contact graph theorem.

Choose V's actual gap-facing circle corner

    Z_V=(-1/2,d+1).

For the barrier construction only, let A_T be the first, gap-facing extreme of the actual intersection U cap T on the U arc coming from P+v. Write

    A_T=P+v+rho_*u, 0<=rho_*<=rho<s/c.                  (48)

The original application P_T, original normal, and every equation remain unchanged. If UT is a singleton then A_T=P_T. If it is a shared side, (48) uses only its actual first endpoint for the occupied barrier, not for any force.

Use the occupied path

    Z_V down V's left side to P,
    P along U's side to P+v,
    P+v along U's side to A_T,
    A_T through T to its gap-facing physical circle corner Z_T.
                                                               (49)

The V/U parts have x<=-1/2. Both A_T and every physical T circle corner have x<-1/2 by (32),(36),(48). Convexity gives a T segment in that strict half-plane; if necessary it can be perturbed arbitrarily slightly through int T while keeping the same endpoints and the strict half-plane.

This is a simple crosscut. U cap V={P} by strict UV exposure; the gap-facing choice A_T avoids entering T earlier on the U arc; its open path through T avoids closed U and V. T is closed-disjoint from V. The circle endpoints cannot be shared, and U has no circle point.

The actual closing circle arc from Z_V to Z_T also lies in x<=-1/2. Z_V is the upper endpoint of that circle cap, every physical T circle corner lies in its open cap, and the clockwise core path occupies the complementary boundary order. The physical circle-corner order keeps every other core corner interval on that path side.

The crosscut and its actual closing circle arc consequently bound a Jordan region wholly in

    x<=-1/2.                                             (50)

It preserves every whole extra originally assigned to this closing exterior pocket. Indeed the original center/contact V-U-T barrier deforms inside the actual closed V,U,T union to (49), using the genuine closing U boundary arc. Moving the barrier contact to A_T changes no original force application. Every point of an extra's open interior avoids that closed occupied union, so its winding number is unchanged. At a weak contact junction apply the argument first to a compact inner subset of the extra, then take closure. Additional zero-weight contacts only subdivide the occupied regions.

It follows that every whole actual extra E in the closing pocket lies in (50). Every unit has horizontal halfwidth at least 1/2, so

    (c_E)_x<=-1, |c_E|>=1.                              (51)

## 13. The full true T2 equation supplies the angular upper routing

Let B_T be T's actual predecessor on the loaded boundary path. The T-to-B_T boundary moment is strictly positive in counterclockwise order. The complete T torque, with all circle atoms radial about the unchanged origin, gives

    det(P_T,n_T)>0.                                     (52)

The true loaded degree-two proper-concurrence lemma applies with the actual boundary neighbor B_T. It gives

    q_T=P_T+ell*n_T=lambda_T*F_T,
    ell>=0, lambda_T>0.                                 (53)

This is the full physical one- or two-circle statement. Either individual circle coefficient may vanish, and q_T may be outside T.

Both P_T and n_T have negative first coordinate. Their arguments are in the common left-half-plane lift, and (52) orders n_T strictly counterclockwise from P_T. Thus (53) and the full physical circle-corner/resultant cone give

    arg(P_T)<=arg(F_T)<theta_T+15 degrees.              (54)

Every physical T circle corner, including Z_T, also has argument strictly below theta_T+15 in this lift.

The V/U part of (49) has increasing argument. Its V side has positive determinant; its first U step has determinant (35); its second U step has determinant (34). In particular

    arg(Z_V)<=arg(A_T)<=arg(P_T).

The T path may be kept in the convex angular sector between A_T and Z_T. Physical corner order puts Z_T strictly after Z_V on the actual closing lift. Therefore the whole closing boundary, including its circle arc, lies in the pointed cone

    arg(Z_V)<=theta<=theta_T+15 degrees.                 (55)

Its aperture is below pi because arg(Z_V)>90 degrees and theta_T+15<231 degrees. The bounded Jordan region inherits both defining half-planes of this cone. Hence every original closing-pocket extra has the same angular lift and upper bound (55).

No internal degree-three boundary body is treated as a two-force tip. All arguments involving the original side mean use P_T; A_T is only a geometric crosscut endpoint.

## 14. Closed centered arcs exclude two actual extras

Every contained unit center has norm strictly below M=91/60, since its farthest corner has squared norm at least r^2+r+1/2 and

    M^2+M+1/2-Q=31/57600>0.

Together with (51), this puts each actual extra center at an angle

    130 degrees<theta_E<230 degrees.                    (56)

Indeed cos(theta_E)<-60/91<-13/20 and sin(40 degrees)<13/20. The latter exact comparison follows from cos(40 degrees)>19/25 and
(13/20)^2-[1-(19/25)^2]=1/10000>0; the rational gap 60/91-13/20 is 17/1820.

The full all-units centered-forty-degree theorem applies to every E by |c_E|>=1, and to T by (37). Each actual unit contains its complete closed radius-9/8 arc of halfwidth 20 degrees in its open interior. Thus the minor center-direction gap between any two of these units is strictly greater than 40 degrees.

Equation (55) gives theta_E<=theta_T+15. If theta_E>=theta_T, its minor gap from T would be at most 15 degrees. Hence

    theta_E<theta_T.                                    (57)

Choose the actual open-V point at phi_0 from Section 11. Since theta_E>130 degrees and phi_0<=116 degrees, if theta_E-phi_0<=20 degrees that point would lie in the closed centered arc inside int E. This contradicts interior-disjointness. Therefore

    theta_E-phi_0>20 degrees.                           (58)

If two extras have theta_1<theta_2, (57),(58) and their strict forty-degree separations give

    theta_1-phi_0>20 degrees,
    theta_2-theta_1>40 degrees,
    theta_T-theta_2>40 degrees.

All three are actual minor gaps, since the total interval is below 100 degrees by (46). Their sum contradicts (46). This proves the complete closing-pocket capacity-one theorem.

## 15. Literal whole original D02 feature

Retain the original positive rim

    01,12,23,34,45,50,

the positive chord 02, the complete load set {0,1,3,4,5}, and all three actual extras. Set

    U=2, V=1, W=0, B_3=5, B_4=4, T=3.

The loaded boundary path is 1,0,5,4,3. The true degrees are U3,V2,W3,5_2,4_2,T2. The actual exterior order is U,V,W,5,4,T,U. The same-nine analytic lower-radius theorem gives R>2 on these original retained nine squares.

Whenever V has two physical circle corners and UV is originally free, every hypothesis of the theorem is literal. No initial U-axis, W owner, UW mean, T mask, T owner or internal path condition is added.

The central triangle 012 and pentagon 02345 have combined capacity at most one by the complete positive-chord central theorem. Each direct exterior boundary-pair pocket on 10,05,54,43 is empty. The only remaining exterior pocket is the closing one through U, which has capacity at most one by Section 14.

The original occupied graph and boundary spokes allocate every extra's connected open interior among these actual bounded faces and exterior pockets, with the compact-interior weak-junction convention. Thus at most two of the three actual extras can be allocated. This excludes the entire stated free-UV physical-two-circle V feature.

Together with a separately proved unique-circle free-UV theorem, this can cover all physical V masks of that same original free-contact feature. Such an assembly must retain the unique-circle theorem's actual selector premises. This manuscript alone makes no claim that an incoming U-owned or V-owned contact, the full D02 row, or its parent is closed.

## 16. Exact operative sources and verification boundary

| Source | SHA-256 | Exact operative use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force, moment, actual normal and complete mean conventions |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Original UV point P does not belong to physical-boundary W |
| RADIAL_HALFSTRIP_FULL_RADIUS_BOUNDARY_SUPPORT_COROLLARIES.md | e8cb01fa67033056433ce210ae0c286700606533cae5db18fc641e8d568804f8 | Entire actual W has y>d-1; all V inner-side and South-quadrant boundary-neighbor exclusions |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Complete actual W mask, beta*gamma<1/4, exact circle equation and continuous scalar monotonicities |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Every actual U-owned UW normal has nonnegative scalar product with the original UV normal |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full true U3 makes T closed-disjoint from V,W, all original means retained |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Lemma 1.1 only: actual boundary-edge moment sign |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 only: full proper concurrence at true T2, with its actual boundary predecessor |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only: actual all-mask corner/resultant cone of halfwidth 15 degrees and center-radius upper bound |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Actual closed centered forty-degree arcs in every whole extra and T |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Only its printed exact elementary angle inequalities and actual V inner-point comparisons; no physical force or port premise is transferred |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Actual boundary-path orientation and absence of physical boundary triangles or cycles of length at most six |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Full physical corner order and emptiness of every direct boundary-pair exterior pocket |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual selected embedding and compatible weak-junction/whole-extra routing |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole original central triangle/pentagon union has capacity one |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph, load set and true degrees |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | R>2 for the same original nine-square caller |

The complete original VW and UW feature cover, all physical masks, actual U port bounds, continuous tilt exclusions, full T angular estimates and occupied closing-pocket join are printed above. The only selected free-normal premise is the originally given UV feature; no subsequent normal choice is made.

All exact rational checks confirm displayed identities and strict margins. No pose search, numerical optimization, angle mesh, new computational exclusion certificate, mean substitution, force deletion, artificial two-force internal body, Lean compilation, CI, workflow, ledger edit, commit or remote action is used.

