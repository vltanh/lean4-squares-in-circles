# A perpendicular W-owned two-circle tip has closing-pocket capacity at most one

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed hand pocket theorem and complete original D02 physical-two-corner feature exclusion, submitted for fresh independent review.** The proof retains the entire true U3,V2,W3,T2 equations, every original UW mean when W is aligned, every physical T circle mask and all completion units. It permits the W-owned contact to be an endpoint of the actual W side; that endpoint is included in the scalar cover.

The new proof combines a complete two-circle-tip chart, uniform bounds on the actual W side parameter, an occupied crosscut in a fixed half-plane, and two exact inner-circle points covering the full radius interval. No pose sample or approximate scalar certificate is used.

## 1. Exact complete component and theorem

Put Q=1105/256 and work in

    2<R<=sqrt(Q).

Keep actual pairwise interior-disjoint closed unit squares in the unchanged disk D_R and their original full physical equilibrium. Suppose the complete positive component consists of an unloaded U and the positively loaded boundary path

    V,W,B_3,...,B_(k-1),T, 3<=k<=6,

together with exactly the original three spokes UV,UW,UT. Its actual outer-face order is U,V,W,...,T,U. Thus U is true degree three, V and T are true loaded degree two, W is true loaded degree three, and every remaining path body is true loaded degree two. Every other actual physical unit remains.

Assume the original U-to-V and U-to-W normals are perpendicular own side axes of U. Assume V is nonparallel to U and has two physical circle corners. Assume the original V-to-W normal is owned by W and is not an own side axis of V.

The last condition makes the actual V application a unique support vertex. On W it may be a relative side-interior point or a side endpoint. Its original location and magnitude remain unchanged.

**Pocket theorem.** The actual closing exterior pocket through U between V and T contains at most one whole additional unit square.

**Original D02 consequence.** In M6.B6.HEXAGON.D02.L01345 this entire feature is impossible: the central triangle and pentagon have combined capacity one, every other exterior pocket is empty, and the closing pocket has capacity one, insufficient for the three actual extras.

This source does not by itself exclude a unique physical-circle mask at V, a parallel V, or a return normal owned by V. The separately accepted owner results remain separate. No whole original D02 row or parent is declared closed.

## 2. Actual perpendicular supports and the original W-owned contact

Rotate and, if necessary, reflect the entire physical data about the unchanged circle origin so that U-to-V is North and U-to-W is East. Write

    U=[L-1,L] x [H-1,H],
    P=(L-p,H), 0<=p<=1.

Because V is nonparallel to U, its actual UV intersection is the singleton P, its unique bottom vertex. Its actual inward axes are

    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (1)

The force-free perpendicular-neighbor direction lemma gives Southeast signs for the original V-to-W normal. The complete all-owner common-point theorem applies at true loaded V2 with physical-boundary W, since R^2>4>13/4, and gives

    P does not belong to W.                         (2)

The Southeast normal has negative e_2 component. Its e_1 component is nonzero because it is not a V own axis. A negative component would expose P itself, contrary to (2). Thus the actual VW point is

    M=P+e_1.                                        (3)

Since W owns this normal, name its inward normal and side tangent as

    g=(S,-C), f=(C,S),
    S>0, C>=0, C^2+S^2=1.

The South endpoint S=0 is impossible: its e_1 component would be -s<0. If C>0, W has a unique left vertex Q_W and inward axes f,g. If C=0, W is aligned with U; let Q_W be its lower-left corner. In both cases its entire actual square and unchanged VW point have the form

    W=Q_W+[0,1]f+[0,1]g,
    M=Q_W+beta*f, 0<=beta<=1.                       (4)

The actual UW support lies on x=L. The point M has height H+s>H. When C>0, Q_W is the actual original UW singleton and has height at most H. When C=0, an original UW mean at height at most H implies the actual lower-left corner Q_W has height at most H. Therefore

    Q_W=(L,H-delta),
    p=c-beta*C,
    delta=beta*S-s>=0.                              (5)

In particular beta>0. The strict positive e_1 component of g is

    eta=c*S-s*C>0,

and consequently C<c and S>s. Hence

    0<p<=c<1, 0<=delta<1, 0<beta<=1.                (6)

The endpoint beta=1 has not been discarded.

For C>0, the unchanged original UW mean is Q_W, so its height is H-delta. For C=0, (5) gives Q_W,y=H+s-beta>H-1. Thus Q_W itself lies on the actual U right side, and the entire original UW mean has the form

    M_UW=(L,H-delta_0), 0<=delta_0<=delta.            (7)

For C>0 set delta_0=delta. In every case (7) retains the original mean; Q_W is not substituted for it in a force equation.

Define

    gamma=c*C+s*S>0,
    eta=c*S-s*C>0,
    gamma^2+eta^2=1,
    r=C/S>=0,
    alpha=s/S=gamma-r*eta,
    kappa=c/S=eta+r*gamma,
    tau=1-beta in [0,1).                            (8)

Then

    alpha>0, alpha<=beta, alpha<=gamma,
    gamma*alpha+eta*kappa=1,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.                            (9)

All these are exact identities or consequences of the actual supports. The aligned W frame C=0,S=1 is included.

## 3. The full physical V mask and its full two-force inequality

Write A_V=P.e_1 and B_V=P.e_2. With original pair magnitudes mu,nu>0, V's full outward circle resultant is

    F_V=mu*North-nu*g,
    F_V.e_2=mu*c+nu*gamma>0.                        (10)

Thus B_V>=-1/2: below that value every physical farthest corner has negative e_2 coordinate.

If B_V=-1/2, the first own center coordinate is nonzero because R>2. If it is positive, M=P+e_1 is a physical circle corner; if negative, P is a physical circle corner. Both are impossible because those actual points are shared with another contained square. A containing-circle point cannot be shared: containment puts each of the two inward side directions strictly in the inward radial half-plane, and two open right-angle tangent sectors cannot fit disjointly there.

Therefore B_V>-1/2. A unit with two physical circle corners at R>2 has exactly one zero own center coordinate. Its full actual mask is consequently

    A_V=-1/2,
    B_V=d=sqrt(R^2-1/4)-1,
    V=[-1/2,1/2]e_1+[d,d+1]e_2,
    P=(-1/2,d), M=(1/2,d) in the V frame.            (11)

Both physical outer corners and every individual zero coefficient remain. The exact radius bounds give

    187/200<d<61/60.                                 (12)

For the lower comparison,
15/4-(387/200)^2=231/40000>0.
For the upper comparison, the radius squared at d=61/60 exceeds Q by 31/57600.

The original two pair lines at V meet at

    q_V=P+(gamma/S)*North,
    q_V=(-1/2+gamma*alpha,d+gamma*kappa)
        in V coordinates.                          (13)

Indeed (q_V-M).f=0. Full torque about q_V gives det(q_V,F_V)=0. Both vectors have strictly positive e_2 coordinate, so q_V is a positive multiple of the full F_V. This conclusion does not assert q_V lies inside V.

Normalize only the positive total circle coefficient:

    F_V=Lambda*(xi,d+1), Lambda>0,
    -1/2<=xi<=1/2.

The lower endpoint xi>=-1/2 in (13) yields the complete necessary inequality

    gamma*[2(d+1)*alpha+kappa]>=1.                  (14)

This keeps both individual circle-weight endpoints. No positive coefficient on either particular outer corner has been assumed.

## 4. Every physical W mask is forced to its actual right corner

The actual W from (4) is

    W=M+[-beta,1-beta]f+[0,1]g.

Its center has f coordinate

    c_W.f=d*eta-(1-gamma)/2+tau>0.                  (15)

Here eta>1-gamma for positive gamma,eta on the unit circle, and d>1/2.

Its center's g coordinate is

    c_W.g=(1+eta)/2-d*gamma.

Suppose this were nonpositive. A physical farthest corner would then be the top corner Z_top=M+tau*f. Its exact deficit is

    R^2-|Z_top|^2
      =2d+1-tau*(gamma+2d*eta)-tau^2.
                                                               (16)

Because tau<1, the right side is strictly greater than its value at tau=1,

    2d(1-eta)-gamma.

The assumed nonpositive g-center coordinate gives
2d*gamma>=1+eta, so

    2d(1-eta)>=((1+eta)(1-eta))/gamma=gamma.

Thus (16) is strictly positive. The top corner cannot be on the circle, contradicting W's physical boundary status. This argument includes the zero g-center tie and both initially possible W circle corners.

Both W own center coordinates are therefore positive, and its unique actual circle corner is

    Z_W=M+tau*f+g.

Expanding |Z_W|^2=R^2 gives

    d=F(gamma,tau)
      :=(tau^2+tau*gamma+eta)/
           (2*(1+gamma-tau*eta)),
    eta=sqrt(1-gamma^2).                            (17)

The denominator is positive for 0<gamma,eta<1 and 0<=tau<1. No W equation, circle coefficient or degree has been reduced to obtain this exact scalar identity.

## 5. Two uniform bounds on the actual side parameter

On the whole domain 0<gamma<1, 0<=tau<=1, the function F in (17) is strictly increasing in tau and strictly decreasing in gamma. The first derivative has positive numerator

    (2tau+gamma)*(1+gamma-tau*eta)
       +eta*(tau^2+tau*gamma+eta).

For the gamma derivative, multiply its numerator by eta>0. The result is

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma<0.      (18)

Indeed tau(1-tau)*eta<=1/4 while 1+tau^2>=1. When eta is temporarily enlarged independently with gamma,tau fixed and the denominator positive, F increases with eta as well.

We first prove

    beta<2/5.                                       (19)

If beta>=2/5, then tau<=3/5. If gamma>=3/8, monotonicity and sqrt(55)/8<149/160 give

    d<=F(3/8,3/5)<1213/1306<187/200,

contrary to (12). The final reserve is 811/130600.

Thus gamma<3/8. Now eta>9/10, alpha<=gamma, and (9) gives kappa<=1/eta<10/9. Using d<61/60, the left side of (14) is strictly below

    (3/8)*[(121/30)*(3/8)+10/9]
      =5667/5760
      =1-31/1920.

This contradicts (14), proving (19). In particular

    s=alpha*S<2/5, c>9/10.                          (20)

We next prove

    beta*gamma<1/4.                                 (21)

Otherwise (19) gives gamma>5/8, while gamma<1 gives beta>=1/4 and tau<=3/4. Since sqrt(39)/8<25/32, (17)--(18) imply

    d<F(5/8,3/4)<116/133<9/10,

again impossible. The final reserve is 37/1330. Consequently

    beta*C=beta*(c*gamma-s*eta)<c/4.                 (22)

Both bounds cover the entire continuous W frame, beta=1, the aligned W, and every physical V weight split. In particular any impossible endpoint is eliminated by the same full-domain inequalities.

## 6. The complete true U3 equations fix T's actual support and port

Write omega>0 for the original UW magnitude. Full unloaded U force gives the original UT normal strictly Southwest in the U frame, so its unchanged actual application is

    P_T=(L-1,H-1).

Set

    A=1-p=1-c+beta*C>0,
    B=1-delta_0>0.

Taking the entire U torque about P_T, with the original mean (7), gives

    mu*A-omega*B=0.

Thus the unchanged unit normal into T is

    n=-(A,B)/sqrt(A^2+B^2).                         (23)

For aligned W the actual delta_0 is still present in B. It has not been replaced by delta.

From (19)--(22) and (7),

    A<1-3c/4<13/40,
    B>1-beta>3/5.                                  (24)

In V coordinates, the exact original T port is

    P_T=(-a_T,b_T),
    a_T=1/2+s+c*A,
    b_T=d-c+s*A.                                   (25)

The original n has components

    n.e_1=-(A*c+B*s)/sqrt(A^2+B^2)<0,
    n.e_2=(A*s-B*c)/sqrt(A^2+B^2)<0.                (26)

The second strict sign follows from
A*s-B*c<13/100-27/50=-41/100.
The useful whole-domain bounds are

    a_T>1/2,
    -1/10<b_T<37/150<1/4.                          (27)

The lower bound uses d>9/10,c<=1. The upper bound follows from
b_T<61/60-9/10+(2/5)(13/40)=37/150.

## 7. All actual T circle corners lie strictly left of the V side line

Take any physical circle corner Z of T, including a corner with zero individual circle coefficient. Suppose its V-own first coordinate satisfies Z_x>=-1/2, and put w=Z-P_T.

By (25), w_x>0. T lies beyond its original minimum-n support at P_T. Equations (26) therefore force w_y<0. Its actual unit diameter gives |w|<=sqrt(2)<3/2.

Consequently

    -1/2<=Z_x<1,
    -8/5<Z_y<1/4.

The lower second-coordinate bound uses b_T>-1/10. Therefore

    |Z|^2<1+64/25=89/25<4<R^2,

a contradiction. Hence

    Z_x<-1/2 for every actual physical circle corner of T.
                                                               (28)

This proof is independent of every T owner, side mean, physical one- or two-circle mask and positive-weight pattern.

Let c_T be its actual center, r_T=|c_T|, and sigma=1/sqrt(2). Since P_T belongs to T and T is physically boundary,

    |c_T-P_T|<=sigma,
    r_T>=R-sigma>31/24.                             (29)

Using sigma<17/24 and (27),

    (c_T)_x<5/24, |(c_T)_y|<191/200.

Its first coordinate is actually negative. Otherwise these bounds contradict

    (31/24)^2-(5/24)^2-(191/200)^2
      =28519/40000>0.

Define its V-own angular lift

    theta_T=arg(c_T) in (pi/2,3pi/2).                (30)

## 8. Exact elementary angle comparisons

Angles in degrees below abbreviate the corresponding rational multiples of pi. All comparisons in this section are exact.

Put t=sin(10 degrees). The cubic 3t-4t^3 is strictly increasing for 0<t<1/2, and its value is sin(30 degrees)=1/2. Direct substitution gives

    3(11/64)-4(11/64)^3=1/2-307/65536,
    3(7/40)-4(7/40)^3=1/2+57/16000.

Therefore

    11/64<sin(10 degrees)<7/40,
    63/64<cos(10 degrees)<79/80.                    (31)

The two cosine squared reserves are respectively 39/102400 and 481/102400.

The exact golden-ratio formulas, with
20/9<sqrt(5), 38/17<sqrt(5)<161/72, give

    cos(36 degrees)>29/36>4/5,
    47/80<sin(36 degrees)<147/250.                  (32)

For the sine lower and upper squared comparisons the reserves are 19/57600 and 331/2125000.

Using sqrt(2)<99/70, (31) gives

    sin(35 degrees)
      =(cos(10 degrees)-sin(10 degrees))/sqrt(2)
      >1813/3168>4/7,                              (33)

with final reserve 19/22176. Also

    sin(26 degrees)
      =sin(36 degrees)cos(10 degrees)
         -cos(36 degrees)sin(10 degrees)
      <8863/20000<4/9,                             (34)

with final reserve 233/180000, and

    cos(26 degrees)>cos(30 degrees)=sqrt(3)/2>64/75.
                                                               (35)

The last squared reserve is 491/22500.

Finally,

    sin(40 degrees)>77/120.                        (36)

For completeness, the cubic 3z-4z^3 is strictly decreasing on the relevant interval above 1/2. At z=77/120 its value is 375067/432000, which exceeds 13/15 by 667/432000. Also 13/15>sqrt(3)/2 because (26/15)^2-3=1/225. Comparing with sin(120 degrees)=sqrt(3)/2 proves (36). The half-angle identities then give

    sin(25 degrees)^2<43/240,
    cos(25 degrees)^2>197/240.                      (37)

## 9. A complete uniform T angle bound

We prove first

    theta_T<216 degrees.                            (38)

If (c_T)_y>=0, then theta_T<=180 degrees and the claim is immediate. The following estimates cover negative center height, including every actual orientation.

Use the sharper constants

    d>18729/20000,
    sigma<99/140,
    r_T>181/140.                                   (39)

The first follows from
15/4-(38729/20000)^2=64559/400000000>0;
the second has squared reserve 1/19600.

### 9.1. The whole range s>=3/20

Since A>=1-c and 1-c=s^2/(1+c)>=s^2/2, (25) gives

    b_T>=d-1+s^2/2+s^3/2
       >18729/20000-1+(3/20)^2/2+(3/20)^3/2
       =:b_min.

The exact positive margin is

    (181/140)*(47/80)-(99/140-b_min)
      =1007/560000.

Thus if the center height is negative,

    |(c_T)_y|/r_T
       <(99/140-b_min)/(181/140)
       <47/80<sin(36 degrees).

Equation (30) now gives theta_T<180+36=216 degrees.

### 9.2. The whole range s<=3/20

Here c>247/250, because
1-(3/20)^2-(247/250)^2=339/250000>0.
From (22),

    c*A<c-3c^2/4
        =1/4+(1-c)/2-3(1-c)^2/4
        <1/4+3/500.

Consequently

    a_T<453/500<91/100,
    b_T>-1271/20000.                               (40)

Together with (27), these inequalities give |P_T|<1.

The angle of P_T is below 210 degrees: if b_T>=0 it is at most 180 degrees; otherwise |b_T|/a_T<(1/10)/(1/2)=1/5<tan(30 degrees). Its angle is always above 90 degrees.

Suppose theta_T>=216 degrees. For a point with argument in [216,270] degrees, its squared distance from P_T increases with its angle: the angle difference from P_T is in (0,pi). It also increases with its radius above 181/140, because |P_T|<1<181/140. Thus the nearest possible such center is bounded below by the distance to the radius-181/140 point at angle 216 degrees.

That point has both coordinates strictly below the corresponding lower coordinate bounds in (40), by (32). Therefore

    |c_T-P_T|^2
      >[(181/140)(29/36)-91/100]^2
        +[(181/140)(47/80)-1271/20000]^2
      =1/2+10826627041/6350400000000
      >1/2.

This contradicts (29). It proves (38) on the whole remaining tilt interval, including s=3/20.

### 9.3. A stronger bound for d>=24/25

On this entire range,

    b_T>=d-1>=-1/25,
    R>101/50,
    r_T>919/700.

For the radius comparison,
(49/25)^2+1/4-(101/50)^2=7/625>0.
If the center height is negative, (39) gives

    |(c_T)_y|/r_T
      <523/919<4/7<sin(35 degrees).

The rational reserve is 15/6433. Hence

    theta_T<215 degrees whenever d>=24/25.          (41)

Nonnegative center height again satisfies this automatically.

## 10. Actual V inner points cover every d

Put rho=9/8. In the V own frame, the following actual radius-rho points lie strictly inside V:

| Entire actual d interval | Point angle phi |
| --- | --- |
| d<=24/25 | 116 degrees |
| d>=24/25 | 115 degrees |

For the first point the coordinates are

    (-rho*sin(26 degrees),rho*cos(26 degrees)).

By (34)--(35), its first coordinate is strictly greater than -1/2 and its second strictly greater than 24/25>=d. It has negative first coordinate, so it is below the right bound 1/2, and its height is at most rho<d+1.

For the second point the coordinates are

    (-rho*sin(25 degrees),rho*cos(25 degrees)).

Equation (37) gives the exact strict reserves

    1/4-rho^2*(43/240)=119/5120>0,
    rho^2*(197/240)-(61/60)^2=1211/230400>0.

Thus it too lies strictly between V's left and right sides and above its inner side, for every d<61/60. Again its height is below d+1.

Every d is covered, including the common threshold. The matching angle conclusions (38),(41) are precisely

    theta_T<phi+100 degrees.                         (42)

These are points of the unchanged actual open V, not selected application points or new circle contacts.

## 11. The genuine closing crosscut and every whole extra lie in one cap

The actual VW moment is strictly negative:

    det(M,g)=-gamma/2-d*eta<0.                       (43)

The degree-free boundary-pair moment sign and angular-neighbor rule make the entire actual loaded path V,W,...,T clockwise. Its closing exterior gap through U is counterclockwise from V to T.

The U port locations are also unambiguous. P is in the relative interior of its top side by 0<p<1. The original UW mean lies on the right side, and P_T is the southwest vertex. Their actual cyclic order is therefore V,W,T, with the closing U boundary arc from P to P_T passing through the northwest vertex. No coincidence of a top or bottom mean is used to infer a false spoke order.

Choose the actual V circle corner facing the closing gap:

    Z_V=-e_1/2+(d+1)e_2.

In V coordinates, the following entire path is occupied:

    Z_V=(-1/2,d+1) down to P=(-1/2,d),
    P to the actual U northwest corner,
    that corner to P_T=(-a_T,b_T),
    a path inside T from P_T to its gap-facing circle corner Z_T.

The first part is V's left side. The next two parts lie on U's actual top and left sides. In V coordinates their first coordinate is at most -1/2. By (28), the last circle corner has first coordinate strictly below -1/2, as does P_T.

The full unloaded-three-force touching-return theorem makes T closed-disjoint from V and W, because V,W physically touch. The original strict U exposure makes U intersect T={P_T}, and U intersect V={P}. Thus the occupied crosscut is simple. A straight segment in T can be replaced, if necessary, by an arbitrarily close path through its interior; it remains strictly left of x=-1/2.

The actual closing circle arc from Z_V to Z_T lies in x<=-1/2. Z_V is the upper endpoint of that circle cap, every physical T circle corner is in its open cap, and the actual boundary path takes the complementary clockwise order. The physical circle-corner order keeps all other core corner intervals on the path side.

For completeness U itself is circle-clear in this chart. From (22),(20),

    -1/5<L<1/2, 61/100<H<21/20.

Indeed L=c/2-ds-beta*C>9/40-61/150=-109/600>-1/5 and H=dc-s/2>61/100. Every actual U point then has |x|<6/5, |y|<21/20, and squared norm below 1017/400<4. Thus no unaccounted circle spoke from U splits the asserted boundary-path gap.

The bounded Jordan region of this crosscut and its closing circle arc lies in

    x<=-1/2 in the V frame.                         (44)

This is the actual original closing pocket, with its whole extras preserved. Explicitly, the original V-U-T center/contact crosscut deforms to the displayed occupied path within the actual closed V,U,T union. The applications P and P_T stay fixed. The U center path is deformed to the genuine top-left boundary arc, without altering the original UW mean or any equation. Every point of an extra's open interior avoids that closed union, so its winding number is preserved by the homotopy.

At a weak junction, apply the same argument first to a compact inner subset of the extra, whose distance from the closed core is positive, then take closure. Additional zero-weight contacts only subdivide regions. They cannot move any part of a whole extra across the occupied crosscut.

Consequently every whole extra E assigned to this closing pocket satisfies

    (c_E)_x<=-1,                                   (45)

because every unit frame has horizontal halfwidth at least 1/2.

## 12. The true T2 equation gives the necessary angular upper routing

Let B_T be T's last boundary-path predecessor. The actual T-to-B_T moment is strictly positive in counterclockwise order. The full true degree-two T torque, with all radial circle moments zero, gives

    det(P_T,n)>0.                                  (46)

The all-mask proper-concurrence lemma applies because B_T is an actual physical boundary neighbor. It gives

    q_T=P_T+ell*n=lambda_T*F_T,
    ell>=0, lambda_T>0.                            (47)

This includes a physical two-circle T, either individual zero coefficient and a concurrence outside T. No inside-concurrence assertion is used.

In V coordinates, P_T is in the open left half-plane, while n is strictly Southwest by (26). Their lifted arguments lie in (90,270) degrees. Equation (46) orders n strictly counterclockwise from P_T. Hence (47), together with the physical corner/resultant cone of halfwidth 15 degrees, gives

    arg(P_T)<=arg(F_T)<theta_T+15 degrees.           (48)

Every physical T circle corner, including Z_T, has the same strict upper bound.

The occupied crosscut's argument increases from Z_V to P_T along its V and U parts. For the U top step its determinant sign is

    det(P,(-c,s))=dc-s/2=H>0;

for the U left step, starting at the northwest corner, it is

    c/2+ds+A>0.

The V side step also has positive determinant. The T path may be kept in the convex angular interval between its endpoint directions. Thus the whole actual closing boundary, including the circle arc, lies in the pointed cone

    arg(Z_V)<=theta<=theta_T+15 degrees.             (49)

Its aperture is below pi: arg(Z_V)>90 degrees and theta_T+15<231 degrees by (38). The bounded Jordan region inherits both defining half-planes of this cone. Therefore every actual closing-pocket extra center satisfies the same angular upper bound.

All force and mean arguments in this section concern the original T2 and U3 data. No degree-three internal path unit has been treated as an endpoint.

## 13. Closed centered arcs exclude two actual extras

Every contained unit center has norm strictly below 91/60, from the actual farthest-corner inequality and the exact reserve

    (91/60)^2+91/60+1/2-Q=31/57600>0.

Together with (45), each closing-pocket extra has V-own center angle

    130 degrees<theta_E<230 degrees.                (50)

Indeed cos(theta_E)<-60/91<-13/20, and sin(40 degrees)<13/20. The latter standard exact bound follows from cos(40 degrees)>19/25, whose triple-cosine cubic has reserve 753/31250; then
(13/20)^2-[1-(19/25)^2]=1/10000>0.
The rational comparison 60/91-13/20 has reserve 17/1820.

Every such extra has center radius at least one. The full all-units centered-forty-degree theorem puts its entire closed radius-9/8 arc of halfwidth 20 degrees inside its actual open interior. It also applies to T by (29). Thus two distinct such actual units have minor center separation strictly greater than 40 degrees.

Equation (49) gives theta_E<=theta_T+15 degrees. If theta_E>=theta_T, its minor separation from T would be at most 15 degrees. Hence

    theta_E<theta_T.                                (51)

Select the actual V point from Section 10 according to d. Its angle phi is at most 116 degrees, whereas (50) puts theta_E above 130 degrees. If theta_E-phi<=20 degrees, that fixed actual point of int V would lie in the closed centered arc contained in int E, contradicting interior-disjointness. Therefore

    theta_E-phi>20 degrees.                         (52)

If two extras E_1,E_2 occupied the closing pocket, order their angles increasingly. All successive differences are actual minor gaps by (38),(50),(51). Equations (51)--(52) and the strict forty-degree separation give

    theta_E1-phi>20 degrees,
    theta_E2-theta_E1>40 degrees,
    theta_T-theta_E2>40 degrees.

Their sum is greater than 100 degrees, contradicting (42). This proves the full pocket theorem.

## 14. Complete literal original D02 consequence

For M6.B6.HEXAGON.D02.L01345 retain the original rim

    01,12,23,34,45,50,

its positive chord 02, and the full positive circle-load set {0,1,3,4,5}. Set

    U=2,V=1,W=0,B_3=5,B_4=4,T=3.

The complete loaded path is 1,0,5,4,3. Its true degrees are U3,V2,W3,5_2,4_2,T2, and its actual outer cycle is U,V,W,5,4,T,U. The same-nine analytic lower-radius theorem supplies R>2 on the original retained nine units.

When the two original U normals are perpendicular own axes, V is nonparallel with two physical circle corners, and VW is W-owned but not V-owned, every premise of the pocket theorem is literal. Every W3 force, both V physical circle corners, every individual zero coefficient, every original side mean and all three arbitrary extras remain.

The central triangle 012 and pentagon 02345 have combined capacity at most one. Each of the four direct exterior boundary-pair pockets on 10,05,54,43 is empty. The remaining exterior pocket is precisely the closing one through U=2 between V=1 and T=3, and has capacity at most one by Section 13.

The original occupied plane graph and boundary spokes partition every extra's connected open interior among these actual central faces and exterior pockets, with the compact-interior weak-junction convention. Thus at most two of the three actual extras can be allocated. This contradiction excludes the entire stated original physical-two-corner W-owned feature.

The same proof applies after any graph-preserving relabeling or reflection of the complete physical data. It does not assert closure of the unique-circle V branches, the parallel V branch, the whole perpendicular interface, or the full original D02 load row.

## 15. Exact operative sources and verification boundary

| Source | SHA-256 | Exact operative use |
| --- | --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2 only: force-free complete Southeast neighbor-normal cone |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Original UV application P is not in W, with arbitrary U/W degrees and all original means |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full U3 and actual VW make T closed-disjoint from V,W |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Lemma 1.1 only: actual boundary-pair moment sign |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 only: full all-mask proper concurrence at true T2 with an actual boundary neighbor |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only: full physical corner/resultant cone and center upper bound |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Closed centered 40-degree actual inner arcs at every extra and T |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Actual boundary-path angular-neighbor and center order |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Physical circle-corner order and every direct-pair pocket's emptiness |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole central capacity and exact original face routing |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual selected embedding, boundary spokes and compatible weak-junction routing |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal D02 graph, load set, degrees and unchanged three extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 entry for the original caller |

All new physical mask, original-mean, force, scalar, angle and occupied-routing claims are proved above. In particular the proof does not depend on the new radial half-strip theorem, any unproved W-owned scalar exclusion, or a hypothesis placing the T concurrence inside T.

Exact rational arithmetic checks the displayed reserves only. No pose sampling, orientation mesh, numerical exclusion certificate, normal reselection, substituted mean, force deletion, artificial degree-two neighbor, Lean compilation, CI, workflow, shared ledger change, commit or remote action is used.

