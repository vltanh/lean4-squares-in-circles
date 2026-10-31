# A terminal port in a weak cap leaves room for at most one extra

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free matching theorem, submitted for independent review.** The actual port may lie on either side of V's left-side line, the cap clearance is allowed down to the closed value1/6, and the full Y range is retained. The physical cap and angular routing are explicit caller premises. They must be proved using the caller's actual occupied component, rather than inferred from this scalar theorem.

## 1. Actual units, closed radius range and precise routing premises

Put Q=1105/256 and rho0=9/8. Retain actual pairwise interior-disjoint closed unit squares in the unchanged disk D_R, where

    2<=R<=sqrt(Q).

Suppose an actual boundary unit has the unchanged chart

    V=[-Y,1-Y] x [X-1,X],
    X>=Y>=1/2, X^2+Y^2=R^2.                       (1)

Its actual upper-left circle corner is Z_V=(-Y,X). Let T be a distinct actual unit physically touching the same containing circle. It contains its actual port S=(-A,B), and it lies in an actual southwest support half-plane there: for some u,v>0,

    u*(Z_x+A)+v*(Z_y-B)<=0 for every Z in T.      (2)

Assume the complete scalar bounds

    1/6<=q<9/10, A>=q,
    -7/20<B<1/4,
    A-B<199/250.                                 (3)

Angles use degrees and the continuous lift containing arg(Z_V) in(90,135]. The theorem first proves that T's center lies in the left half-plane and its principal lifted angle theta_T is below215 degrees.

For a collection of other actual units E, assume each whole closed E satisfies the actual cap and center routing

    E subset {x<=-q},
    arg(Z_V)<=theta_E<=theta_T+15 degrees.         (4)

The upper and lower bounds in (4) are on this same lift. They are hypotheses about the original physical regions and unchanged center directions. They are not force or torque consequences supplied by this theorem.

**Theorem.** Under(1)--(3), every physical containing-circle corner of T satisfies Z_x<-q, theta_T<215 degrees, and there is an actual open-V point on the radius-rho0 circle at an angle phi>115 degrees that is earlier than every center routed by(4). Under all of(1)--(4), the entire collection contains at most one unit.

The theorem is valid for arbitrary actual frames, physical circle masks and individual zero circle coefficients. It has no load, degree, normal-owner, original-mean or graph premise. A caller proving(4) retains all its own forces and means unchanged.

## 2. Uniform center radii and elementary bounds

Every actual contained unit with center radius r has a farthest corner with squared norm at least r^2+r+1/2. The own-frame sum of absolute center coordinates is at least r, which proves that lower bound. At r=91/60 its excess above Q is31/57600>0. Monotonicity therefore gives

    r<91/60.                                      (5)

For T, put sigma=1/sqrt(2). An actual boundary corner is at distance sigma from its center, and S belongs to T, so

    |c_T-S|<=sigma,
    |c_T|>=R-sigma>=2-sigma>181/140.              (6)

Here sigma<99/140, with squared reserve1/19600. We also use sqrt(2)<99/70, with squared reserve1/4900.

The complete port bounds imply

    0<A<199/250+1/4=523/500<sqrt(2).              (7)

Only this upper bound, the actual support and the unit diameter will be used to locate all physical T corners.

## 3. Every actual T circle corner is strictly left of the weaker cap line

Suppose a physical T circle corner Z has Z_x>=-q. Put w=Z-S and d=A-q>=0. By(2),

    w_x>=d, w_y<=0, w_x^2+w_y^2<=2.              (8)

The last inequality is the true unit diameter, with no assumption about which corner is loaded. In particular d<=sqrt(2). We maximize the squared norm of S+w on the entire closed quarter-disk segment in(8). This larger domain contains the actual corner, so its upper bounds are valid without a selected T frame.

If d=sqrt(2), the domain consists of w=(sqrt(2),0). Its first resulting coordinate is-q, so its norm is q^2+B^2<81/100+49/400<4. Thus assume d<sqrt(2).

The boundary of the domain consists of a vertical interval, a horizontal interval and the circular arc w_y=-sqrt(2-w_x^2). Squared norm is convex on each straight interval, so their endpoints suffice. A maximum of the nonconstant convex squared norm on this compact convex domain occurs on its boundary.

If B<=0, the norm on the circular arc equals

    A^2+B^2+2-2A*w_x+2|B|*sqrt(2-w_x^2).

It is decreasing in w_x>=0. The vertical bottom endpoint consequently bounds the arc and both straight intervals. Thus

    |Z|^2<=q^2+(B-sqrt(2-d^2))^2
           <81/100+(7/20+99/70)^2
            =76885/19600<4.                       (9)

The last strict reserve is1515/19600.

If B>=0, the nonconstant part on the circular arc is

    -2A*w_x-2B*sqrt(2-w_x^2),

which is convex in w_x. Again its endpoints and the straight-interval endpoints suffice. At either vertical endpoint the norm is at most q^2+2<281/100<4. At the horizontal right endpoint it is

    (sqrt(2)-A)^2+B^2
       <(99/70-1/6)^2+1/16<4.                    (10)

The sign of sqrt(2)-A is positive by(7); hence its monotonic bound from A>=1/6 is legitimate. The vertical estimate uses0<=B<1/4 and0<=sqrt(2-d^2)<=sqrt(2), so the absolute second coordinate is at most sqrt(2).

Both signs of B, all support endpoints and every actual physical T corner have now been covered. Equations(9)--(10) contradict |Z|=R>=2. Therefore

    every physical T circle corner has Z_x<-q.   (11)

The line here is the actual weaker cap line-q. No stronger conclusion x<-Y or A>Y is assumed.

## 4. T's actual center is in the left half-plane and below235 degrees

Suppose (c_T)_x>=0. Since A>=1/6, (6) gives

    0<=(c_T)_x<99/140-1/6=227/420.

The full B interval likewise gives

    |(c_T)_y|<99/140+7/20=37/35=444/420.

Thus

    |c_T|^2<248665/176400
             <294849/176400=(181/140)^2,

contradicting(6). Its center is therefore strictly left, and its principal lift has90<theta_T<270.

If its center height is nonnegative, theta_T<=180. Otherwise put delta=theta_T-180 in(0,90). The same lower B bound gives

    sin(delta)=-(c_T)_y/|c_T|<148/181<9/11.       (12)

We need the exact elementary inequalities

    cos35>9/11, sin35>4/7.                       (13)

For the first, the cubic4t^3-3t increases on t>1/2 and

    4*(9/11)^3-3*(9/11)
       =-351/1331<-21/80
       <cos105=-(sqrt(6)-sqrt(2))/4.

The last inequality uses sqrt(6)<49/20 and sqrt(2)>7/5. The first strict reserve is129/106480. Since cos35>1/2, comparison on the stated branch proves the claim.

For the second, the cubic3t-4t^3 decreases on t>1/2 and

    3*(4/7)-4*(4/7)^3=332/343>541/560
       >sin105=(sqrt(6)+sqrt(2))/4.

Here sqrt(6)<49/20 and sqrt(2)<99/70; the first reserve is51/27440. Since sin35>1/2, this proves the second claim on the correct branch.

Because sin55=cos35>9/11, (12) and strict sine monotonicity on(0,90) give delta<55. The other height sign was already handled, so

    theta_T<235 degrees.                          (14)

This proof requires B>-7/20. It does not assume the stronger B>-3/20 or a preliminary center bound below225 degrees.

## 5. The full coordinate-sum bound improves the angle to215 degrees

Suppose215<=theta_T<235. Then delta=theta_T-180 lies in[35,55). On that complete interval, cos(delta)+sin(delta) is at least its equal endpoint values at35 and55. Consequently(6),(13) give

    -(c_T)_x-(c_T)_y
       > (181/140)*(9/11+4/7)
       >449/250,                                 (15)

with final strict reserve153/269500.

But -S_x-S_y=A-B<199/250. The absolute difference between the coordinate sums of c_T and S is therefore greater than1. Cauchy's inequality then gives |c_T-S|>1/sqrt(2), contradicting(6). Hence

    theta_T<215 degrees.                          (16)

This is a complete physical-center bound over all T frames and physical masks; no convenient circle weight or terminal orientation is chosen.

## 6. An actual open-V point above115 degrees over the entire Y range

Define the constant angle

    theta_* = acos(-40/91), 115<theta_*<120.      (17)

The upper bound follows from40/91<1/2. For the lower bound, use only the elementary inequality cos(25 degrees)^2>197/240 from the exact input in Section9. It gives

    sin(25 degrees)^2<43/240<(40/91)^2,

with final reserve27917/1987440. Positive first-quadrant signs give the lower bound in(17).

We prove that some actual radius-rho0 point lies in open V at

    115<phi<theta_*.                             (18)

First suppose Y<=1. At exactly115 degrees the point has coordinates

    (-rho0*sin25, rho0*cos25).

Because43/240<16/81, its first coordinate is strictly greater than-1/2>=-Y and strictly less than0<=1-Y. Also

    X-1<61/60,
    rho0^2*cos(25 degrees)^2
       >(9/8)^2*(197/240)>(61/60)^2,

where the last reserve is1211/230400. The X bound follows from X^2<=Q-1/4 and the strict31/57600 comparison at121/60. Both vertical quantities are positive. Finally X>=sqrt(2)>rho0, so this point is strictly below the top of V. It is thus in open V. Openness and theta_*>115 supply a nearby larger angle satisfying(18).

Now suppose Y>1. At exactly theta_* the point is

    P_*=(-45/91, (9/8)*sqrt(1-(40/91)^2)).        (19)

Its first coordinate is greater than-1>-Y. Since X>=Y,

    Y^2<=Q/2<(136/91)^2,

with reserve319447/4239872. Therefore -45/91<1-Y as well. For the vertical coordinate, Y>1 gives

    X^2<Q-1=849/256<(11/6)^2,
    X-1<5/6.

The squared vertical coordinate in(19) exceeds25/36 by1558049/4769856, so it is above X-1. Again it is below rho0<X. Thus P_* is in open V. A sufficiently small decrease of its angle retains this actual membership and yields(18).

Both complete Y intervals, their common endpoint and the allowed X=Y boundary are covered. No upper bound such as Y<9/16 or Y<1 is required by the matching theorem.

## 7. The actual cap orders every routed extra after that open V point

The whole-square cap in(4) puts each extra center at

    (c_E)_x<=-q-1/2<=-2/3.                       (20)

The half horizontal span of a unit is at least1/2 for every frame. In particular its actual clearance from the origin is at least q>=1/6.

Together with the strict center-radius bound(5), (20) gives

    cos(theta_E)<-(2/3)/(91/60)=-40/91.           (21)

The actual routing(4) and(16) place theta_E in the common lift(90,230). If theta_E<=180, cosine is strictly decreasing there and(21) implies theta_E>theta_*. If theta_E>180, that conclusion is automatic from theta_*<120. Therefore in every case

    theta_E>theta_*>phi.                         (22)

This uses the actual weaker cap and actual routing. It does not assume that an extra center follows V's left-side limiting ray. The constant-angle argument is why the theorem retains the whole Y range.

## 8. The strict20+40+40 contradiction

The one-sixth-clearance theorem gives each actual extra its entire closed centered radius-rho0 arc of halfwidth20 degrees in its open interior. The actual T has clearance at least R-sqrt(2)>=2-sqrt(2)>1/6: for any point of T, compare it to an actual T circle corner using the true unit diameter. Hence the same theorem also gives T this closed centered arc.

Any pair among T and the extras therefore has minor center gap strictly greater than40 degrees. In particular theta_E>=theta_T is impossible: the actual upper routing bound in(4) would make their gap at most15 degrees. Consequently

    phi<theta_E<theta_T,
    theta_T-phi<100 degrees.                     (23)

The actual radius-rho0 point at phi lies in open V. If theta_E-phi<=20, it would also lie in the closed centered arc contained in open E, contradicting their disjoint interiors. Thus each first gap is strictly greater than20 degrees.

If two extras were present, order their angles as theta_1<theta_2. All relevant differences are minor gaps because the full interval in(23) is shorter than100 degrees. The three successive gaps would satisfy

    theta_1-phi>20,
    theta_2-theta_1>40,
    theta_T-theta_2>40.

Their sum is strictly greater than100, contradicting(23). Thus at most one actual whole extra satisfies(4).

No connectedness of a completing unit's entire circle intersection is used. Only its actual center route, its actual whole cap and one closed centered arc in its open interior are needed.

## 9. Exact inputs, physical join boundary and accounting

| Complete operative source | SHA256 | Exact use |
| --- | --- | --- |
| ONE_SIXTH_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a | Entire all-center closed twenty-degree half-arc at actual clearance at least1/6 |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Only its proved elementary inequality cos(25 degrees)^2>197/240; none of its physical-two equations or graph premises |

This force-free theorem supplies no original owner classification, U3/T2 torque identity, actual occupied crosscut or topological pocket assignment. A physical caller must prove every actual premise in(1)--(4), particularly the entire cap and the lower as well as upper angular routing. The theorem then bounds the whole routed collection, with arbitrary actual units, orientations and physical masks retained.

In the stronger cap domain q>1/4, the earlier d575 center-radius theorem alone also supplies every required extra arc, because |c_E|>=q+1/2>3/4. The present smaller closed q threshold follows from the new one-sixth-clearance theorem, which requires separate complete independent review before adoption; it is not inferred from d575 outside that theorem's center domain.

No original fine or coarse gate is changed by this conditional capacity theorem alone. No force, degree, physical coefficient, actual side mean, application, selected normal or square is altered. No Lean compilation, CI, workflow dispatch, pose sample, optimization certificate, remote action or shared-ledger mutation is used.

