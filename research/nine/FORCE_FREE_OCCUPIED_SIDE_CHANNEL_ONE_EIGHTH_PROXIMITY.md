# An occupied boundary side-channel pocket forces its actual transmitter into the one-eighth disk

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed force-free geometric theorem, submitted for full independent review.** All actual endpoint degrees, physical circle masks, support features and original means remain arbitrary. This is a strict whole-domain proximity conclusion for the original transmitter, not for a virtual replacement.

Put Q=1105/256 and rho=9/8. Retain the entire actual geometric setup of FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md:

    2<=R<=sqrt(Q),
    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h), P_Y=(b,h), v<=h<=v+1,
    P_X in X intersect H, P_Y in Y intersect H,
    X subset {x<=-a}, Y subset {x>=b}.

X,Y are actual physical boundary units. The previous force-free entry permits the unchanged reflection h>0 and gives

    a,b>7/100, a,b<1,
    h>3/10,
    (c_X)_x<0<(c_Y)_x,
    (c_X)_y,(c_Y)_y>0.

The upper channel pocket Omega is the actual bounded side of the occupied crosscut

    z_X -- P_X -- P_Y -- z_Y

and its upper containing-circle arc. In a genuine positive-channel caller, z_X,z_Y are exactly the unchanged original exterior-spoke corners. The preceding capacity theorem proves the upper arc is the correct original one without requiring endpoint properness.

**Theorem.** If Omega contains an additional whole actual unit E with open interior disjoint from X,H,Y, then

    dist(O,H)<1/8.                                    (1)

No force equation at X or Y is added. In particular X may be the true loaded degree-three endpoint W=0 of D02.L0134. The conclusion includes every original application mean and the equality case v=1/8, which is excluded.

## 1. Complete current geometric inputs

The preceding whole capacity proof gives the stronger clearance

    dist(O,E)>3/10.                                  (2)

It proves (2) by the actual occupied loop and its winding, including a physical endpoint corner below the port line. The present source does not assume E lies in y>=h.

Each boundary endpoint has

    |c_X|,|c_Y|>=R-1/sqrt(2)>=m:=2-1/sqrt(2).

Also every physical point of a boundary unit has norm at least R-sqrt(2)>1/8. Therefore the complete nine-eighths connected-arc theorem applies to X and Y. Their entire closed intersections with |z|=rho are connected closed arcs; their open intersections are the corresponding open arcs and contain the actual radial-center points.

The center-direction theorem supplies to every actual unit with center norm at least 3/4 the complete closed angular arc of halfwidth 20 degrees on this same rho-circle, inside its open interior.

This applies to both boundary units. It also applies to E: the incircle centered at c_E has radius 1/2 and lies in E, so (2) implies

    |c_E|>=dist(O,E)+1/2>4/5>3/4.                     (3)

Thus E contains an entire connected closed 40-degree arc, centered at its actual center direction. This is a specified actual subset of E; no assertion about radial visibility is needed.

## 2. A uniform one-sided angular estimate for a boundary endpoint

We prove a force-free estimate at the original left endpoint. Let

    theta_X=arg(c_X) in (pi/2,pi),
    beta_a=acos(-a/rho) in (pi/2,pi).

Because a<1<rho, the latter angle is defined. Write

    A=-(c_X)_x=a+H_X,
    delta=pi-theta_X in (0,pi/2),

where H_X is X's actual horizontal support halfwidth. For a unit square,

    H_X<=sigma:=1/sqrt(2).

We claim

    theta_X-beta_a<pi/3.                             (4)

Equivalently,

    delta+asin(a/rho)>pi/6.                          (5)

If a>=rho/2, asin(a/rho)>=pi/6 and delta>0 already prove (5).

Now take the entire closed interval 0<=a<=rho/2 as an enlarged scalar comparison. The actual center-radius bound gives

    cos(delta)=A/|c_X|
        <=(a+sigma)/m, m=2-sigma.                    (6)

Define the full continuous function

    F(a)=(sqrt(3)/2)sqrt(1-a^2/rho^2)
              +a/(2rho)-(a+sigma)/m.                (7)

Its square-root term is strictly concave on [0,rho/2], and every other term is affine. Therefore F is concave, so its value is bounded below by the smaller of its two endpoint values.

At a=0,

    F(0)=sqrt(3)/2-sigma/m>0.

For example sigma<3/4 gives m>5/4 and sigma/m<3/5, while sqrt(3)/2>3/4. Hence F(0)>3/20.

At a=rho/2,

    F(rho/2)=1-(rho/2+sigma)/m>0,                    (8)

because rho/2+2sigma=9/16+sqrt(2)<2. The exact squared reserve for sqrt(2)<23/16 is 17/256.

Thus F(a)>0 over the entire closed interval. The first two terms of (7) are exactly

    cos(pi/6-asin(a/rho)).

The angle pi/6-asin(a/rho) lies in [0,pi/6]. Combining (6)--(8) and strict cosine monotonicity gives

    delta>pi/6-asin(a/rho).

This proves (5), and therefore (4), on the full domain. No actual endpoint orientation or height was varied in the scalar comparison.

Let alpha_X be the gap-facing endpoint angle of X's actual closed rho-circle intersection, on the upper lift. The actual centered 20-degree half-arc is in its open interior, so

    alpha_X<theta_X-pi/9.                            (9)

The inequality is strict because its closed centered-arc endpoint itself lies in the open square. Consequently (4) gives

    alpha_X-beta_a
       <pi/3-pi/9=2pi/9.                             (10)

Thus the complete possible free angular interval to the left of H's vertical side x=-a has length strictly less than 40 degrees. If alpha_X<=beta_a, that interval is empty, which only strengthens the statement.

Reflection proves the identical bound at the right endpoint, using b and the right side x=b.

This estimate has no endpoint force, concurrence, weight, owner or transverse-mean premise. It uses only the actual boundary-center annulus, its strictly positive height, its true horizontal support halfwidth, and the centered arc theorem.

## 3. The actual upper-pocket routing also holds on the nine-eighths circle

For completeness, we reproduce the necessary topological join on the new circle rather than silently transferring the old radius-5/4 argument.

Let I_X and I_Y be the complete closed rho-circle intersections of the endpoint squares. Since X lies in x<0 and Y in x>0, they are intervals in the left and right open semicircles respectively. They contain the actual radial-center directions

    pi/2<theta_X<pi, 0<theta_Y<pi/2.

Their radial-center points lie in the open endpoint units, hence strictly beyond their original supports: the X point has x<-a, and the Y point has x>b.

A lower-left rho-circle point outside I_X can follow that circle to (0,-rho) without meeting I_X: connectedness and theta_X<pi ensure there is no later piece of I_X after an outside point on that lower quadrant. The path avoids Y by its negative x-coordinate and avoids the middle crosscut segment by its nonpositive height. The two remaining strands lie in X and Y. The downward ray from (0,-rho) then reaches infinity without crossing the loop, whose outer closing arc is the upper one. Such a point is outside Omega. Reflection handles the lower-right quadrant.

For an upper point of angle greater than theta_X, continue toward angle pi. Its x-coordinate stays strictly left of -a, because the radial-center point is already strictly left and cosine decreases on the upper semicircle. Thus the middle segment is avoided. Connectedness of I_X and the starting point's avoidance of X show that the endpoint strand is avoided. Continuing through the lower quadrant and down the same ray again escapes. Reflection handles upper angles below theta_Y.

Therefore every rho-circle point in the open interior of E lies on the upper lift and, on avoiding both complete endpoint arcs, satisfies

    alpha_Y<arg(z)<alpha_X.                          (11)

The exit paths test only the bounded-side winding of the actual occupied loop. They are not proposed physical motions of any square, and no sector containment of a whole square was assumed.

## 4. A transmitter outside the one-eighth disk blocks the middle of the entire centered arc

Suppose, to the contrary, that dist(O,H)>=1/8. Because a,b>0, H's horizontal interval contains zero strictly. Its vertical interval contains h>3/10>0. If v<=0, H would contain O, contradicting the supposed positive distance. Hence

    v=dist(O,H)>=1/8,
    v+1>=9/8=rho.                                   (12)

On every vertical line x in [-a,b], the defining occupied crosscut meets that line at height h, and its upper circle closing arc lies above it. Thus a rho-circle point of Omega with such a horizontal coordinate must have y>=h; an open-interior point avoiding the crosscut has y>h.

If such a point also belongs to the open interior of E, then

    -a<=x<=b, v<=h<y<=rho<=v+1.

It would belong to the closed actual transmitter H, impossible for a point of the disjoint open unit E. This includes x=-a or x=b, and the equality v+1=rho at the north circle point: those are still actual closed points of H and cannot lie in int(E).

Consequently every point of E's entire closed centered 40-degree arc lies strictly outside H's horizontal slab:

    x<-a or x>b.                                    (13)

The arc is connected, so it stays on one of these two sides. It cannot switch sides without crossing the forbidden closed slab.

Suppose it is on the left. By (11) and x<-a, its entire angular interval lies in

    (beta_a,alpha_X).

Section 2 proves this interval has length strictly less than 2pi/9, while the actual centered arc has length exactly 2pi/9. This is impossible. The reflected estimate excludes the right side as well.

This contradiction proves (1). All equalities at dist(O,H)=1/8, the original means and every endpoint circle-mask tie were retained.

## 5. Exact original scope and limits

The original degree-two side-normal transmitter provides precisely the two-force/torque chart used by the preceding force-free theorem. No force at its endpoints is omitted.

For D02.L0134, the actual channel is

    W=0 -- H=5 -- B=4.

W keeps its true loaded degree three, H keeps its true unloaded degree two, and B keeps its true loaded degree two. All of the original positive edges, including chord 02, remain. If this actual side-channel exterior pocket is occupied by even one of the three original extra squares, then the unchanged unit 5 has dist(O,5)<1/8.

For D02.L0135 the same conclusion applies to the actual side-channel transmitter 4 between boundary units 3 and 5. These are complete side-channel implications over their full original endpoint owner and mask domains.

The theorem is broader than either caller: it holds for every geometric upper pocket satisfying the displayed actual boundary side-channel hypotheses, and the preceding global-balance join supplies the correct upper arc for genuine outer channels at arbitrary endpoint degrees.

This proof does not give dist(O,H)<1/40 or the older simple-cycle bound 1/60. It does not close a whole original four-load D02 row. A whole central/exterior injection must still account for the actual hub, transmitter, central extra and all remaining pockets together.

## 6. Exact sources and verification

| Source | SHA256 | Exact operative use |
| --- | --- | --- |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md | 418229089de594515bbb60da5bdcdb4cd044bd4e9396aacfa47d27de96194055 | Complete unchanged upper channel loop, all-mask arbitrary-degree entry, strict whole-extra distance greater than 3/10, original outer-gap selection and both literal D02 callers |
| NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md | 4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366 | Complete connected closed/open endpoint rho-circle intersections and their radial-center points; applied only with strict physical boundary clearance |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Entire actual closed centered 40-degree arc in each endpoint and in E, with all hypotheses explicitly checked |

The new one-sided concavity comparison, the actual new-radius routing and the whole closed-arc/slab argument are proved above. The earlier radius-5/4 capacity is not silently reused on a different circle. The source depends on the stated current capacity proof and requires its complete independent review; it transfers no old approval to new bytes.

No numerical pose, parameter sample, finite sign certificate, altered physical square, force deletion, new contact, mean replacement, selected-normal change, Lean compilation, CI, remote write or shared-ledger mutation is used.

