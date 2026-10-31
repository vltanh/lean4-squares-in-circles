# Every occupied physical boundary side-channel pocket forces its actual transmitter into the one-fortieth disk

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed force-free geometric theorem, submitted for full independent review.** This proof covers arbitrary actual endpoint degrees, every physical circle mask and every original support mean. Its final small-port step uses the additional whole square and its actual incircle; it does not use the false endpoint-only merged-interval bound recorded separately.

## 1. Exact entire geometric statement

Put

    Q=1105/256, rho=43/40, alpha=pi/10,
    sigma=1/sqrt(2), m=2-sigma, M=91/60.

Retain the complete actual geometric setting of FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md:

    2<=R<=sqrt(Q),
    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h) in X intersect H,
    P_Y=(b,h) in Y intersect H,
    v<=h<=v+1,
    X subset {x<=-a}, Y subset {x>=b}.                 (1)

All three actual unit squares have disjoint open interiors and lie in the original disk D_R centered at O. X and Y are physically boundary, independently of which individual corner weights are positive.

Use the unchanged common reflection giving h>0. The upper pocket Omega is the bounded side of the original occupied crosscut

    z_X -- P_X -- P_Y -- z_Y

and its upper containing-circle closing arc. In a positive-channel caller, z_X,z_Y are the unchanged original exterior-spoke corners. The preceding capacity theorem proves that the actual outer arc is the upper one. No circle corner is moved and no radial face is swept.

Suppose an additional whole actual unit E lies on the closed bounded side of this occupied loop, with open interior disjoint from X,H,Y.

**Theorem.** The unchanged actual transmitter satisfies

    dist(O,H)<1/40.                                    (2)

The result includes and excludes the equality case dist(O,H)=1/40. It makes no force, torque, degree-two, proper-concurrence or contact-owner assumption at X or Y.

A reusable consequence is that at most two distinct actual side-channel transmitters can have occupied upper pockets under these hypotheses. If a third actual unit already meets the one-fortieth disk and all of its vertices have norm greater than 3/50, then at most one such transmitter can have an occupied pocket. These conclusions require distinct original units and retain all of them.

## 2. Complete current inputs and all arc premises

The complete force-free channel entry gives

    a,b>7/100, a+b=1,
    h>3/10,
    (c_X)_x<0<(c_Y)_x,
    (c_X)_y,(c_Y)_y>0,
    |c_X|,|c_Y|<M.                                  (3)

Every contained unit, including E, has center norm strictly less than M, from the actual farthest-corner formula. The exact reserve is

    M^2+M+1/2-Q=31/57600>0.

The preceding whole capacity theorem establishes, by its actual occupied loop and winding,

    dist(O,E)>3/10.                                  (4)

This statement includes an endpoint whose physical circle corner lies below the original port line. It does not presume that E lies in y>=h.

A square's actual incircle has radius one half. Hence (4) implies

    |c_E|>4/5.                                      (5)

Every physical boundary endpoint has center norm at least R-sigma>=m>4/5. The complete theorem ALL_UNITS_CENTER_RADIUS_FOUR_FIFTHS_CENTERED_THIRTY_SIX_DEGREE_ARC.md therefore supplies, in each of X,Y,E, the entire closed rho-circle arc of halfwidth alpha=18 degrees centered at that unit's actual center direction, inside its open interior.

The closed endpoints of these arcs remain interior points. No assumption is made that the chosen arc is the whole intersection of E with the rho-circle.

We will also use the independently derived one-sided comparison from FORCE_FREE_BOUNDARY_SIDE_CHANNEL_TENTH_HEIGHT_AND_SHORT_CIRCLE_ANGLE.md:

    theta_X-acos(-a/rho)<3pi/10,                     (6)

where theta_X=arg(c_X) in (pi/2,pi). It applies over the full actual force-free channel domain. Its reflected form holds at Y.

## 3. The complete endpoint circle intersections are connected at the new radius

We establish the needed connectedness at rho=43/40 directly, instead of transferring a fixed-radius theorem.

Take either actual boundary unit K and choose signs and order of its own orthonormal axes so its center coordinates are x>=y>=0. Its exact form is

    K=[A-1,A] times [B-1,B],
    A=x+1/2>=B=y+1/2>=1/2,
    A^2+B^2=R^2.

The equality holds because K is physically boundary. Since R>=2,

    A>=sqrt(2)>rho,
    A-1>0.                                         (7)

The outer first-coordinate inequality is automatic on the rho-circle. The inner first-coordinate inequality restricts the circle to one interval in the open positive-first-coordinate semicircle. On that semicircle the second coordinate is strictly increasing with angle. Its two inequalities B-1<=y_coord<=B therefore cut out another interval, retaining any redundant outer face and every equality endpoint. Their intersection is one closed interval.

The centered-arc theorem in Section 2 makes this interval nonempty with nonempty interior. Its open-interior intersection is the corresponding single open interval. In particular no isolated extra point is supplied by a redundant outer face. Alternatively, the radial-center point already lies inside the actual incircle, because

    m<=|c_K|<M,
    rho<m,
    M-rho=53/120<1/2.

Thus the complete closed intersections I_X,I_Y are connected closed arcs containing their actual radial-center points. In global coordinates, I_X lies in the left open semicircle and I_Y in the right open semicircle by the strict supports in (1).

Let alpha_X denote the gap-facing initial endpoint of I_X on the upper lift, and alpha_Y the gap-facing final endpoint of I_Y. The entire closed centered half-arcs lie in the open units, so

    alpha_X<theta_X-alpha,
    alpha_Y>theta_Y+alpha,                           (8)

where 0<theta_Y=arg(c_Y)<pi/2. Both inequalities are strict, including physical two-corner masks and every original mean.

Combining (6) with (8),

    alpha_X-acos(-a/rho)<pi/5.                       (9)

Reflection gives the same strict 36-degree bound for the right lateral free interval.

## 4. Full actual upper-pocket routing on the radius-43/40 circle

Every rho-circle point of int(E) lies on the upper lift and satisfies

    alpha_Y<arg(z)<alpha_X.                          (10)

Here is the complete winding justification at this radius.

A lower-left circle point outside I_X can continue along the circle toward (0,-rho) without crossing X: I_X is connected, is contained in the left semicircle, and contains theta_X<pi. After a lower-left point beyond that connected interval, no later part of I_X remains. The path avoids Y by its negative first coordinate and avoids the middle occupied segment by its nonpositive height. The remaining crosscut strands are inside X and Y. The downward ray from (0,-rho) reaches infinity without crossing the upper outer closing arc. Such a point is outside Omega. Reflection handles the lower-right quadrant.

For an upper point of angle greater than theta_X, its continuation toward angle pi has first coordinate strictly less than -a, because the radial-center point is already in open X and cosine decreases on the upper semicircle. It therefore avoids the middle segment. Starting outside X and continuing after the radial-center angle cannot encounter a later piece of its connected interval. The same lower exit path then reaches infinity. Reflection handles upper angles below theta_Y.

These escape paths prove the bounded-side label for every circle point under consideration. A point in int(E) cannot belong to either closed endpoint square: any neighborhood of a closed square point meets that square's interior. Avoiding the two complete intervals therefore gives (10).

There is one additional actual slab fact. On every vertical line with x in [-a,b], the occupied crosscut meets that line at height h; its other strands lie strictly outside this slab except for their endpoint applications. Its outer closing arc is the upper one. Hence

    z in int(E), |z|=rho, -a<=z_x<=b
       implies z_y>h.                               (11)

The weak bounded-side inequality is z_y>=h; equality would lie on the actual occupied segment in H and cannot be in int(E). This is a vertical-section statement about the actual loop, not a radial visibility assumption.

## 5. Reduce to the one-small-port merged interval

Assume for contradiction that dist(O,H)>=1/40. Because -a<0<b and the vertical interval of H contains h>0, this implies

    v=dist(O,H)>=1/40,
    w:=v+1>=w_0:=41/40.                             (12)

First suppose w>=rho. Any circle point of int(E) in the slab -a<=x<=b would, by (11), have

    v<=h<y<=rho<=w,

placing it in the actual closed H, a contradiction. Thus the entire closed centered arc of E stays strictly on one side of the slab. Connectedness of this specified arc fixes one side. Its angular length is pi/5, while (9) and its reflected counterpart give a strictly shorter lateral interval. This is impossible.

It remains to consider

    w_0<=w<rho,
    gamma=acos(w/rho),
    x_0=sqrt(rho^2-w^2)=rho sin(gamma).              (13)

We have

    0<gamma<alpha,
    0<x_0<=sqrt(42)/20<13/40<1/2.                  (14)

For the angular bound, cos(alpha)^2=(5+sqrt(5))/8<29/32 and

    (41/43)^2-29/32=171/59168>0.

Here sqrt(5)<9/4 follows from its squared reserve 1/16. Thus cos(alpha)<41/43<=w/rho, proving gamma<alpha. The final x_0 bound in (14) follows from

    (13/40)^2-42/400=1/1600>0.

If both a,b>=x_0, every free circle portion is in one of three separate open pieces: the left lateral portion, the central portion above H, or the right lateral portion. The central portion has angular interval

    (pi/2-gamma, pi/2+gamma)

and length 2gamma<pi/5. The lateral portions have lengths strictly below pi/5 by (9) and its reflection. At a=x_0 or b=x_0 the pieces touch only at an actual closed corner of H; a point of int(E) still cannot cross that point. Consequently E's entire connected closed centered pi/5 arc cannot fit any component, a contradiction.

Because a+b=1 and 2x_0<1, both ports cannot be smaller than x_0. After horizontal reflection, the only remaining case is

    7/100<a<x_0, b>x_0.                             (15)

The right lateral component is still too short by (9)'s reflection. Every point of E's centered arc must therefore lie in the remaining merged central-and-left interval, which is contained in

    (pi/2-gamma, alpha_X).                           (16)

For precision, the point at angle pi/2-gamma has coordinates (x_0,w) in the closed actual H, since b>x_0 and -a<0. Below that angular threshold, a free circle point in the slab would have y<w and, by (11), y>h>=v, so would be in H. Such a point must instead lie on the right lateral side. The closed centered arc cannot cross the forbidden point at the threshold. These facts prove (16) without asserting a false length bound for the merged interval.

Let theta=arg(c_E) on this actual upper lift. Its closed centered arc has endpoints theta-alpha and theta+alpha, both in int(E). Equations (8), (14), and (16) give

    theta>pi/2+alpha-gamma>pi/2,
    theta<alpha_X-alpha<theta_X-2alpha.              (17)

The following whole-square argument excludes (15)--(17). No endpoint-only estimate of the merged interval is used.

## 6. A complete scalar center-angle envelope for the small-port domain

Retain the enlarged closed interval

    7/100<=a<=13/40.                                 (18)

Define

    S(a)=sqrt(m^2-(a+sigma)^2),
    d(a)=3pi/10-acos((a+sigma)/m).                   (19)

Every expression is real on (18). The actual left center has horizontal support halfwidth at most sigma, so

    cos(pi-theta_X)<= (a+sigma)/m.

Combining this with (17), and setting delta=theta-pi/2, gives

    0<delta<d(a).                                   (20)

We prove on the entire closed interval (18) that

    0<d(a)<alpha,
    sin(d(a))<a,
    cos(d(a))>19/20,
    S(a)>3/4.                                      (21)

The elementary bounds 7/10<sigma<71/100 give

    129/100<m<13/10,
    (a+sigma)/m>=77/130>59/100>sin(pi/5).

The first strict comparison after 77/130 has reserve 3/1300. The bound sin(pi/5)<59/100 was proved by the exact sine-square formula in the endpoint-angle source. Since cos(3pi/10)=sin(pi/5), this proves d(a)>0.

On the other side,

    (a+sigma)/m<69/86<161/200<cos(pi/5).             (22)

The middle reserve is 23/8600. The final comparison follows from sqrt(5)>111/50, whose squared reserve is 179/2500. Thus acos((a+sigma)/m)>pi/5, proving d(a)<pi/10=alpha. The same radical bound gives cos(alpha)>19/20, hence the stated cosine bound.

Also

    S(a)^2>(129/100)^2-(207/200)^2
              =9/16+243/8000>9/16.                 (23)

To prove the sine bound in (21), consider the full continuous function

    G(a)=m[sin(pi/5)sqrt(1-a^2)+cos(pi/5)a]-a-sigma.

It is concave on (18). At its two endpoints use

    sin(pi/5)>29/50, cos(pi/5)>4/5,
    sqrt(1-(7/100)^2)>99/100,
    sqrt(1-(13/40)^2)>47/50.

These imply the exact positive estimates

    G(7/100)>
      (129/100)[(29/50)(99/100)+(4/5)(7/100)]
          -7/100-71/100
      =16479/500000>0,

    G(13/40)>
      (129/100)[(29/50)(47/50)+(4/5)(13/40)]
          -13/40-71/100
      =927/250000>0.                                (24)

All radical comparison directions are positive. For example the sine lower bound follows from sqrt(5)<9/4, giving sin(pi/5)^2>11/32>(29/50)^2. The cosine lower bound follows from sqrt(5)>11/5.

Concavity proves G(a)>0 on all of (18). Since

    cos(3pi/10-asin(a))
       =sin(pi/5)sqrt(1-a^2)+cos(pi/5)a,

and 0<3pi/10-asin(a)<pi/2 on (18), strict cosine monotonicity gives

    acos((a+sigma)/m)>3pi/10-asin(a).

Therefore d(a)<asin(a), proving sin(d(a))<a. This completes (21).

These are scalar bounds for the unchanged center. No physical unit is moved through the comparison interval.

## 7. A strict whole-interval corner-distance estimate

Define on (18)

    f(a)=M^2+a^2+w_0^2
            -2M[a sin(d(a))+w_0 cos(d(a))].          (25)

We prove

    f(a)<1/4                                         (26)

throughout this entire interval. Its exact derivative uses d'(a)=1/S(a):

    f'(a)=2a-2M J(a),

    J(a)=
      [a cos(d(a))+(S(a)-w_0)sin(d(a))]/S(a).        (27)

If S(a)>=w_0, the second term in the numerator is nonnegative. Equations (21) and S(a)<=m<13/10 give

    J(a)>19a/26,
    M(19/26)-1=13/120>0.

Thus f'(a)<0 on this part of the interval.

If S(a)<w_0, the coefficient of sin(d(a)) is negative. The strict bound sin(d(a))<a must therefore be substituted with its correct reversed direction. Equations (21), (23) yield

    J(a)>a[1-(w_0-19/20)/S(a)]
          =a[1-(3/40)/S(a)]
          >9a/10.

Again M(9/10)>1, so f'(a)<0. The equality S(a)=w_0 belongs to the first calculation. Thus f is strictly decreasing over the whole interval; no omitted orientation subinterval remains.

At a_0=7/100, put d_0=d(a_0). The identity

    a_0 sin(d_0)+w_0 cos(d_0)-w_0
      =sin(d_0)[a_0-w_0 tan(d_0/2)]

is strictly positive. Indeed

    tan(d_0/2)
       =sin(d_0)/(1+cos(d_0))
       <20a_0/39,

and w_0(20/39)=41/78<1. Therefore

    f(a_0)<(M-w_0)^2+a_0^2
             =1/4-1211/360000<1/4.                 (28)

Monotonicity proves (26) for all a in (18), including its two closed endpoints.

For use with actual smaller center radii, set

    F(r,delta)=r^2+a^2+w_0^2
                    -2r[a sin(delta)+w_0 cos(delta)].       (29)

For each fixed delta this is convex in r. For r=M its second angular derivative is

    F_delta_delta(M,delta)
        =2M[a sin(delta)+w_0 cos(delta)]>0            (30)

on the first-quadrant domain used below. Thus it is convex in delta there.

Whenever 0<=delta<=d(a), the same half-angle comparison gives

    a sin(delta)+w_0 cos(delta)>=w_0.                (31)

At delta=0 it is equality. At delta>0 use sin(delta)<=sin(d(a))<a and cos(delta)>19/20 in the preceding calculation.

The lower radial endpoint consequently satisfies

    F(4/5,delta)
        <=a^2+(w_0-4/5)^2
        <=(13/40)^2+(9/40)^2
        =5/32<1/4.                                 (32)

All convexity arguments below use these full continuous intervals and their displayed endpoint bounds.

## 8. Every remaining possible center is within one half of the actual transmitter

Use the unchanged actual extra center

    c_E=(-r sin(delta),r cos(delta)),
    4/5<r<M, 0<delta<d(a).                          (33)

The radial range follows from (5) and containment; the angle range is (20).

The current transmitter has bottom v=w-1<rho-1=3/40. Equations (21), (33) give

    (c_E)_y>(4/5)(19/20)=19/25>v.                   (34)

Thus the nearest point of H is never on its lower side for any case below. Its right boundary is positive while (c_E)_x<0, so there is no right-side case either.

### 8.1. Center horizontally within the transmitter slab

If (c_E)_x>=-a, its distance to H is at most the positive part of its vertical excess:

    dist(c_E,H)<=max(r cos(delta)-w,0)
                 <=M-w_0=59/120<1/2.              (35)

The final strict margin is 1/120. This includes equality at x=-a and equality at y=w.

### 8.2. Center left of the transmitter but no higher than its top

Suppose (c_E)_x<-a and (c_E)_y<=w. By (34), the center height lies inside the vertical interval of H. Hence

    dist(c_E,H)=r sin(delta)-a
       <(M-1)a
       <=(31/60)(13/40)
       =403/2400<1/2.                              (36)

Here sin(delta)<a from (21) and (33). The estimate retains every boundary equality except the deliberately strict actual left-side premise.

### 8.3. Center strictly above and left of the transmitter

Finally suppose (c_E)_x<-a and (c_E)_y>w. The nearest actual point of H is its upper-left corner (-a,w). Its squared distance decreases as w increases toward the center height. Since w>=w_0,

    dist(c_E,H)^2
       <=(r sin(delta)-a)^2+(r cos(delta)-w_0)^2
       =F(r,delta).                                (37)

This replacement changes only an upper bound, not the actual transmitter.

The left-side premise gives r sin(delta)>a, so

    delta>asin(a/r)>=asin(a/M).                     (38)

Thus the interval [asin(a/M),d(a)] is nonempty and contains the actual delta. At its first endpoint,

    F(M,asin(a/M))
       =[sqrt(M^2-a^2)-w_0]^2
       <1/4.                                       (39)

Indeed sqrt(M^2-a^2)>w_0 on (18), since

    M^2-(13/40)^2>w_0^2,

and sqrt(M^2-a^2)<=M. The positive difference in (39) is at most M-w_0=59/120<1/2.

At its other endpoint F(M,d(a))=f(a)<1/4 by Section 7. Angular convexity (30) therefore gives

    F(M,delta)<1/4

on the entire interval in (38), including its closed comparison endpoints.

Now use radial convexity of (29) on [4/5,M]. Its first endpoint is strictly below one quarter by (32), and its second has just been bounded. Hence

    F(r,delta)<1/4                                  (40)

for every actual r in (33). Equations (37), (40) prove dist(c_E,H)<1/2 in the final case.

These three alternatives exhaust all actual center positions under (33)--(34).

## 9. Whole-square contradiction and the strict proximity conclusion

The open disk of radius one half centered at c_E lies in int(E). Equations (35), (36), or (40) put an actual point of the closed H strictly inside that open disk.

This contradicts the disjoint open interiors of E and H: an open neighborhood of any closed point of a unit square meets its open interior. No assumption that the center itself lies in H is required.

The contradiction rules out the entire one-small-port merged interval. Section 5 already ruled out the full-slab and two-large-port alternatives. Thus the assumption dist(O,H)>=1/40 is impossible, proving (2).

All mean endpoints, both choices of physical circle mask, a=x_0 or b=x_0, v=1/40, w=rho, and all closed centered-arc endpoints have been retained. The actual extra's incircle is essential to Section 8; the proof never asserts that the separate endpoint interval has length below 36 degrees.

## 10. A reusable near-origin injection consequence

The complete force-free entry proves that every vertex of each actual side-channel transmitter has norm greater than 7/100. Therefore every occupied transmitter covered by this theorem satisfies

    dist(O,H)<1/40,
    every actual vertex of H has norm>7/100>3/50.    (41)

Section 4 of SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md is a radius-free geometric theorem: for 0<delta_0<d_0/2 and d_0<1/2, at most two pairwise interior-disjoint actual unit squares can each meet D_(delta_0) while all their vertices lie strictly outside D_(d_0).

Its exact constants delta_0=1/40 and d_0=3/50 obey delta_0/d_0=5/12<1/2. Thus three distinct occupied side-channel transmitters are impossible. If an additional distinct actual unit already meets D_(1/40) and has all vertices of norm greater than 3/50, two occupied side-channel transmitters together with it are impossible.

These statements require the actual distinct units and their established geometric premises. They do not delete graph edges, contract a channel, impose a two-force equation at an endpoint, or presume an unproved allocation of all completion units.

## 11. Literal original callers and remaining global work

At an actual unloaded degree-two side-normal transmitter, its two original positive forces are equal and opposite. Its complete original torque makes the two unchanged actual application means have the same transverse coordinate, giving exactly (1). All endpoint forces remain present.

For D02.L0134, the actual channel is

    W=0 -- H=5 -- B=4.

W keeps its true loaded degree three, H its true unloaded degree two, and B its true loaded degree two. The positive rim and original positive chord 02 remain unchanged. Whenever this actual side-channel exterior pocket is occupied, the original unit 5 obeys (41).

For D02.L0135, the same statement applies to the original side channel 3--4--5. The theorem also applies to larger graphs whenever the displayed actual boundary side-channel and original upper-pocket premises hold. Endpoint degree is unrestricted.

The diagonal-channel alternatives and the joint allocation involving the actual degree-three hub remain separate obligations. This source does not declare any whole original D02 load row or coarse/fine gate closed. It supplies a complete arbitrary-degree side-channel proximity theorem and the stated genuine multi-channel injection consequences.

## 12. Exact direct sources, review boundaries and verification

| Source | SHA256 | Exact use |
| --- | --- | --- |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md | 1a40004509d14eaa228ab52a4eb3280ed0f96df60e3891666f380124b5cacf9c | Entire actual geometric entry, strict center signs, true port/vertex margins, center-radius bound and original channel application |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 418229089de594515bbb60da5bdcdb4cd044bd4e9396aacfa47d27de96194055 | Actual occupied crosscut, arbitrary-degree whole-extra clearance greater than3/10, unchanged original spoke choice, upper outer-gap join and literal original channel callers |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_TENTH_HEIGHT_AND_SHORT_CIRCLE_ANGLE.md | 6cb29db695cb1e351c50aaedb5253825da24b7e280500147e7adcc88c2dd32be | Complete full-domain 54-degree center/vertical-side bound, all physical masks/means, exact elementary angle bounds |
| ALL_UNITS_CENTER_RADIUS_FOUR_FIFTHS_CENTERED_THIRTY_SIX_DEGREE_ARC.md | cd72561bd5221a47c8c47aa34d5913b988e83d895725d64529a3428181967ffc | Entire closed centered36-degree arc at rho43/40 for each actual endpoint and E, including all arc and center-threshold endpoints |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | Only its complete radius-free near-origin three-unit theorem, with exact original unit premises checked in Section10 |

The first two inputs have complete independent Pentagon reviews at 29d24ea50aad0d880ff5558862ef9ede551c3fd703478c66c65fdff1e844f6e1 and b03120174dad7f893b711c4e127fc9cb38614eff6bb931814ff93d0735101a34. The centered36 theorem has complete independent Pentagon review fe4276dd9a441cbfdb00e62a042dda716fb9b4e35fa9cf54246bccc32805b243. The new endpoint-angle source and this source require their own full independent reviews; no historical approval is transferred to these bytes.

The new short-radius connectedness/routing proof, the exact center envelope, all derivatives and the two continuous convexity comparisons are printed in full. The algebra was checked with exact fractions only. The false endpoint-only merged-interval assertion is deliberately absent: an exact obstruction is recorded in EXACT_OBSTRUCTION_TO_SEPARATE_SHORT_CIRCLE_MERGED_INTERVAL_BOUND.md, and the actual extra-square incircle closes precisely that missing premise here.

No pose sampling, angle mesh, optimizer, finite exclusion certificate, physical square replacement, force deletion, selected-normal change, mean movement, Lean compilation, CI, remote write or shared-ledger mutation is used.

