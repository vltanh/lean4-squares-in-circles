# A wide adjacent-circle strip has a matching inner arc and closing-cap capacity one

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed force-free geometric matching lemma and conditional physical-capacity corollary, submitted for independent review.** The local theorem covers the closed endpoint x=1/2 and the whole interval x<1, so it applies to both a physical two-circle corner pair and a unique adjacent-circle corner. It uses no force equation, degree, normal selection or circle-weight assumption.

The capacity corollary states its actual cap and angular-routing premises explicitly. A caller must derive those premises from its original occupied component; this source does not assume an original pocket has that routing. No original graph/load row is credited here.

## 1. Exact local geometric theorem

Put

    Q=1105/256, rho=9/8, sigma=1/sqrt(2),
    r_0=181/140, m_0=207/16000.

Work in the unchanged disk D_R with 2<R<=sqrt(Q). Let the actual unit square V be

    V=[-x,1-x] x [y-1,y],
    1/2<=x<1, y>0,
    x^2+y^2=R^2.                                   (1)

Thus (-x,y) is an actual circle corner. The assumptions imply

    sqrt(3)<y<121/60, y>x,
    0<y-1<rho<y.                                   (2)

The upper bound follows from
(121/60)^2-(Q-1/4)=31/57600>0.
At x=1/2 both upper V corners lie on the circle; at x>1/2 the left upper corner is the unique physical circle corner.

Let T be any other actual physical-boundary unit square in D_R. Suppose it contains a point

    P=(-a,b), a>x,
    y-2<=b<min(y-1,37/150),                          (3)

and that P is a minimum support point in a direction n whose two coordinates are strictly negative:

    n_x<0, n_y<0,
    n.(Z-P)>=0 for every Z in T.                    (4)

No force is attached to this direction in the theorem. If a caller uses an original normal and mean, those stay unchanged.

Impose only the following additional condition on the short interval x<=9/16:

    either b>=y-2+m_0, or a<=x+41/100.              (5)

For x>=9/16, no additional condition is needed. The equality x=9/16 is included in both comparisons, so the statement has no endpoint gap.

Let c_T be T's actual center. Then:

1. Every actual physical circle corner Z of T has Z_x<-x, regardless of its circle coefficient.
2. The center has a unique angular lift theta_T in (90,270) degrees, with theta_T<230 degrees.
3. There is an actual radius-rho point in the open V, at angle phi in (90,180) degrees, such that

       theta_T<phi+100 degrees.                     (6)

More precisely, define

    phi_L=acos(-x/rho),
    phi_B=180 degrees-asin((y-1)/rho).               (7)

Both theta_T-phi_L and theta_T-phi_B are strictly less than 100 degrees. Any phi chosen sufficiently close below min(phi_L,phi_B), and above 90 degrees, is the actual point required by (6).

## 2. Every T physical circle corner lies left of V

Take any physical circle corner Z of T, and suppose Z_x>=-x. Put w=Z-P. By a>x, w_x>0. The two negative signs in (4) force w_y<0. The unit diameter gives |w|<=sqrt(2). Consequently

    -x<=Z_x<sqrt(2)-x,
    y-2-sqrt(2)<=Z_y<y-1.                           (8)

If x>=sqrt(2)/2, then |Z_x|<=x. Since y>sqrt(3)>1+sqrt(2)/2, both bounds on Z_y give |Z_y|<y. This contradicts |Z|^2=R^2=x^2+y^2.

If x<sqrt(2)/2, then y^2=R^2-x^2>7/2, so y>9/5. Also y<R<21/10<(3+sqrt(2))/2. Equation (8) gives

    |Z_x|<=sqrt(2)-x,
    |Z_y|<2+sqrt(2)-y.

It follows that

    |Z|^2-R^2
      <8+4sqrt(2)-2sqrt(2)*x-(4+2sqrt(2))*y
      <=8+3sqrt(2)-(4+2sqrt(2))*y
      <4/5-(3/5)*sqrt(2)<-1/25,

using x>=1/2 and sqrt(2)>7/5. Again this is impossible.

Thus every physical T circle corner lies strictly in x<-x. The proof never chooses a circle load or an owner of a T contact.

## 3. The actual T center and exact angle constants

Because P belongs to T and T is physically boundary,

    |c_T-P|<=sigma,
    r_T:=|c_T|>=R-sigma>31/24.                      (9)

We use sigma<17/24 and the sharper sigma<99/140. From y>sqrt(3)>43/25, (3) gives b>-7/25. Its upper bound is b<37/150. Therefore

    (c_T)_x<5/24,
    -593/600<(c_T)_y<191/200.

In particular |(c_T)_y|<1. If (c_T)_x were nonnegative, these inequalities would contradict

    (31/24)^2-(5/24)^2-1=5/8>0.

Hence (c_T)_x<0, and theta_T=arg(c_T) has its specified lift in (90,270) degrees.

The exact elementary comparisons used below are

    47/80<sin(36 degrees),
    29/36<cos(36 degrees),
    4/5<cos(36 degrees)<13/16,
    sin(26 degrees)<4/9,
    4/7<sin(35 degrees),
    77/120<sin(40 degrees)<13/20,
    19/25<cos(40 degrees),
    cos(25 degrees)^2>197/240.                       (10)

They are the exact triple-angle, half-angle and golden-ratio inequalities proved in Sections 8 and 13 of the pinned two-circle pocket source. Only those elementary real inequalities are imported. No physical-two-circle equation or port inequality is used.

We also need the slightly sharper bound

    cos(40 degrees)>49/64.                          (11)

Indeed f(z)=4z^3-3z is strictly increasing for z>1/2, and

    f(49/64)+1/2=-111/65536<0,
    f(cos(40 degrees))=cos(120 degrees)=-1/2.

Since cos(40 degrees)>1/2, (11) follows.

If the actual T center has negative height, (9) and b>-7/25 imply

    |(c_T)_y|/r_T
      <(7/25+99/140)/(181/140)
       =691/905<49/64<sin(50 degrees).              (12)

The rational reserve is 121/57920. Therefore theta_T<230 degrees. Nonnegative center height satisfies this automatically.

## 4. The two genuine V inner-arc endpoints

The constants in (2) make both angles (7) well defined and in (90,180) degrees. Every radius-rho point at an angle

    90 degrees<phi<min(phi_L,phi_B)                 (13)

lies strictly in V: its negative first coordinate is above -x and below 1-x>0, while its height is above y-1 and below rho<y.

We next prove the matching estimate separately for each endpoint. Their minimum will then give an actual point (13) satisfying (6). These are points of the unchanged open V, not applications of a force.

## 5. The bottom-face endpoint over the whole height interval

Four closed height intervals cover every y in (2). When the center height is nonnegative, all the angle bounds below hold immediately, so consider negative center height in each ratio estimate.

### 5.1. The whole range y<=9/5

Equation (12) gives theta_T<230 degrees. By (11),

    rho*sin(50 degrees)=rho*cos(40 degrees)
      >rho*(49/64)=441/512>4/5>=y-1.

Thus phi_B>130 degrees, and theta_T-phi_B<100 degrees.

### 5.2. The whole range 9/5<=y<=19/10

Now b>=y-2>=-1/5. Consequently

    |(c_T)_y|/r_T<127/181<1/sqrt(2),

where
1/2-(127/181)^2=503/65522>0.
Hence theta_T<225 degrees. Also

    rho*sin(55 degrees)
      =rho*cos(35 degrees)
      >rho*cos(36 degrees)>9/10>=y-1.

Thus phi_B>125 degrees, proving the required strict difference.

### 5.3. The whole range 19/10<=y<=49/25

Here b>=-1/10, so

    |(c_T)_y|/r_T<113/181<77/120<sin(40 degrees),

with rational reserve 377/21720. Therefore theta_T<220 degrees. Since

    rho^2*sin(60 degrees)^2-(24/25)^2
      =4419/160000>0

and y-1<=24/25, we have phi_B>120 degrees.

### 5.4. The whole range y>=49/25

Here b>=-1/25 and

    R^2=x^2+y^2>=1/4+y^2
       >=1/4+(49/25)^2>(101/50)^2,
    r_T>919/700.

The strict squared radius reserve is 7/625. Thus

    |(c_T)_y|/r_T<523/919<4/7<sin(35 degrees),

with rational reserve 15/6433. It follows that theta_T<215 degrees. Meanwhile

    rho^2*(197/240)-(61/60)^2
      =1211/230400>0

and y-1<61/60 give phi_B>115 degrees.

Every shared interval endpoint is included. In all cases the two matching angle comparisons are strict. This proves

    theta_T-phi_B<100 degrees.                      (14)

## 6. The left-face endpoint over the whole coordinate interval

Put y_0(x)=sqrt(4-x^2). Since R>2, y>y_0(x). For any nonnegative constant m for which b>=y-2+m, define

    v_m(x)=(2-y_0(x)+99/140-m)/r_0,
    r_0=181/140.

When the center height is negative and v_m is positive, (9) gives

    theta_T<180 degrees+asin(v_m(x)).               (15)

The only constants used below are m=0 and m=m_0. Both v_m are positive on [1/2,1]. The largest is v_0, and throughout that interval

    y_0(x)>=sqrt(3)>43/25,
    v_0(x)<691/905<4/5.

Therefore sqrt(1-v_m(x)^2)>3/5. Since r_0>9/7 and x<=1,

    d/dx asin(v_m(x))
      =x/[r_0*y_0(x)*sqrt(1-v_m(x)^2)]
      <875/1161<8/9<=d/dx phi_L(x).                (16)

The last strict derivative reserve is 157/1161. Thus the comparison difference in (15) minus phi_L strictly decreases on the whole interval [1/2,1].

### 6.1. Whenever b>=y-2+m_0

At x=1/2,

    y_0=sqrt(15)/2>38729/20000,
    r_0*(47/80)
      -(99/140+1271/20000-m_0)
       =1007/560000>0.

Thus the comparison angle in (15) is below 216 degrees at this endpoint. The inequality sin(26 degrees)<4/9 gives phi_L(1/2)>116 degrees. The decreasing difference (16) proves theta_T-phi_L<100 degrees at every x where this branch is used.

### 6.2. The whole interval x>=9/16

Use m=0, which is available from (3) without an additional hypothesis. At x=9/16,

    y_0=sqrt(943)/16>19/10,
    v_0(9/16)<113/181<sin(40 degrees),
    phi_L(9/16)=120 degrees.

Equation (16) proves the required strict difference throughout [9/16,1).

### 6.3. The remaining short interval with a<=x+41/100

It remains to treat 1/2<=x<=9/16 under the second alternative of (5). We have

    a<=x+41/100<1,
    b>=y-2>y_0(x)-2,
    |b|<1/4.                                       (17)

For the last inequality use y_0(x)>19/10 and b<37/150. Hence |P|^2<17/16<r_0^2. Its angular lift lies in (90,210) degrees: if b<0 then |b|/a<(1/10)/(1/2)=1/5<tan(30 degrees).

Use radians for the derivative calculation, and set

    theta_0(x)=216 degrees+(8/9)*(x-1/2),
    a_0(x)=theta_0(x)-180 degrees.

Here 36 degrees<=a_0<40 degrees. Indeed the added term is at most 1/18 radians, below 4 degrees. Also phi_L'>=8/9 and phi_L(1/2)>116 degrees give

    theta_0(x)<phi_L(x)+100 degrees.                (18)

Let

    D_x=x+41/100-r_0*cos(a_0),
    D_y=2-y_0(x)-r_0*sin(a_0).                       (19)

These are the coordinate differences between the radius-r_0 point at theta_0 and the lower corner of the port box (17). Uniformly on the whole interval,

    -3/20<D_x<0, 0<D_x'<9/5,
    D_y<-2/3, D_y'<-1/2.                            (20)

For completeness, the exact continuous estimates are as follows. From (10),

    r_0*(19/25)-(9/16+41/100)=141/14000>0,

which proves D_x<0. Its derivative is 1+r_0*(8/9)*sin(a_0), between zero and 9/5 because r_0<13/10 and sin(40 degrees)<13/20. Thus D_x increases, and its initial lower bound follows from

    3/20-[r_0*(13/16)-91/100]=107/11200>0.

At x=1/2,

    r_0*(47/80)-1271/20000-2/3
      =24643/840000>0,

so D_y<-2/3. Finally, x/y_0<3/10, r_0>9/7 and cos(a_0)>19/25 yield

    D_y'=x/y_0-r_0*(8/9)*cos(a_0)
          <3/10-152/175<-1/2,

with final reserve 12/175. Hence D_y decreases, proving all of (20).

The squared comparison distance strictly increases:

    (1/2)*(D_x^2+D_y^2)'
      =D_x*D_x'+D_y*D_y'
       >-27/100+1/3=19/300>0.                     (21)

At the left endpoint, the exact angle comparisons give

    D_x^2+D_y^2
      >[r_0*(29/36)-91/100]^2
          +[r_0*(47/80)-1271/20000]^2
       =1/2+10826627041/6350400000000
       >1/2.                                       (22)

Suppose theta_T>=theta_0. Throughout the angular interval from theta_0 to theta_T<230 degrees, squared distance from P increases with angle, because arg(P)<210 degrees and their difference remains in (0,pi). It also increases with radius above r_0, because |P|<r_0.

The radius-r_0 point at theta_0 is strictly left of and below the entire port box (17), by D_x,D_y<0. Consequently

    |c_T-P|^2>=D_x^2+D_y^2>1/2,

contrary to (9). Thus theta_T<theta_0, and (18) proves the desired strict difference.

The three sections exhaust the whole domain, using only the stated alternative (5) on the short coordinate interval. We have proved

    theta_T-phi_L<100 degrees.                      (23)

Equations (14),(23) and the actual interior-point condition (13) establish the complete geometric theorem.

## 7. Conditional actual-capacity corollary

Keep the actual V and T above, and keep every other physical unit in the unchanged pairwise interior-disjoint packing. Suppose a collection of actual extra units E is known, from the original occupied embedding, to satisfy both:

    every whole E lies in {X: X_x<=-x};

    its actual center angle has a common lift
       arg((-x,y))<=theta_E<=theta_T+15 degrees.     (24)

The second premise is an actual routing conclusion, not a claim that an arbitrary geometric cap automatically has that order. A caller may establish it from its genuine closing crosscut and the full original T2 equation. No mean or force may be changed to obtain it.

Then this collection contains at most one unit.

Indeed every unit has horizontal halfwidth at least 1/2, so

    (c_E)_x<=-x-1/2,
    |c_E|>=x+1/2>=1.

Every contained unit center has norm strictly below 91/60, by the farthest-corner inequality and

    (91/60)^2+91/60+1/2-Q=31/57600>0.

Therefore

    cos(theta_E)<-(x+1/2)/(91/60)<-x/rho=cos(phi_L).

For the second inequality use rho/2>x*(91/60-rho), valid for x<1. The angular lift (24) is in (90,245) degrees, so theta_E>phi_L>phi for the actual open-V point chosen in (6),(13).

The actual centered-forty-degree theorem applies to E and to T by (9). Each contains its entire closed radius-rho arc of halfwidth 20 degrees in its open interior. Thus distinct such units have minor center separation strictly greater than 40 degrees.

If theta_E>=theta_T, (24) would make that difference at most 15 degrees, impossible. Hence theta_E<theta_T. Also theta_E-phi>20 degrees: otherwise the actual open-V point at phi would lie in E's centered closed arc, hence in its open interior.

If two extras have center angles theta_1<theta_2, these facts give

    theta_1-phi>20 degrees,
    theta_2-theta_1>40 degrees,
    theta_T-theta_2>40 degrees.

All three are minor gaps, since theta_T-phi<100 degrees. Summing contradicts that matching bound. This proves the whole conditional capacity statement.

## 8. A simple owner-free coordinate consequence of an actual W circle line

The following elementary scalar observation can supply the whole coordinate range x<1 without a refined force ratio.

Let 0<=gamma<1, eta=sqrt(1-gamma^2)>0, 0<=tau<1, and define

    A_1=1+eta+tau*gamma,
    B_1=1+gamma-tau*eta>0,
    N=A_1^2+B_1^2.

Suppose actual positive coordinates x,y satisfy y>x and the exact physical circle line

    2*A_1*x+2*B_1*y=N.                              (25)

Its height at x=1 is exactly

    y_1=(N-2*A_1)/(2*B_1)
        =1-(1-tau^2)/(2*B_1)<1.                    (26)

The equality follows by expanding eta^2+gamma^2=1. Since the line height decreases with x, x>=1 would imply y<=y_1<1<=x. Hence x<1.

This statement assumes that the caller has proved the actual W mask and (25). It does not select a W corner or infer an owner. It uses no V force equation and has no upper bound on a comparison radius.

## 9. Exact operative sources and scope

| Source | SHA-256 | Exact operative use |
| --- | --- | --- |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Sections 8 and 13 only: exact elementary trigonometric inequalities (10) |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Actual closed centered 40-degree arcs, only in the conditional capacity corollary |

All corner, center, port, continuous-angle, capacity and line identities are proved above. The local theorem is force-free; the capacity corollary retains and explicitly requires the caller's actual geometric routing. The true-degree and unchanged-mean obligations therefore remain with that physical caller.

Exact rational arithmetic verifies displayed reserves only. No numerical pose, orientation mesh, normal reselection, force deletion, mean substitution, Lean compilation, CI, workflow, shared-ledger change, commit or remote action is used. This source by itself credits no original graph/load row.

