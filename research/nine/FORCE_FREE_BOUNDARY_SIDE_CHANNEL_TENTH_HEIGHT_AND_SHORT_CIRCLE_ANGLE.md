# A strict tenth-height bound and a shorter-circle endpoint angle for every physical boundary side channel

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed force-free geometric theorem, submitted for full independent review.** The two conclusions below hold over the entire actual side-channel endpoint domain, independently of endpoint degrees, force concurrence, contact owner, physical mask and shared-side mean. The conditional angular corollary states its additional actual-arc premise explicitly; it does not claim a new occupied-channel proximity threshold.

## 1. Unchanged actual setup and conclusions

Put Q=1105/256. Let X,H,Y be actual unit squares with pairwise disjoint open interiors, contained in the common disk D_R centered at O, with

    2<=R<=sqrt(Q).

X and Y physically touch the containing circle. Suppose the unchanged actual applications give

    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h) in X intersect H,
    P_Y=(b,h) in Y intersect H,
    v<=h<=v+1,
    X subset {x<=-a}, Y subset {x>=b}.                 (1)

A point in (1) may be any original weighted application on an actual shared side, including either endpoint. No point, force, normal, mean or unit is replaced.

The complete force-free entry FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md permits the common reflection h>0 and proves

    h>3/10,
    a,b>7/100, a+b=1,
    (c_X)_x<0<(c_Y)_x,
    (c_X)_y,(c_Y)_y>0,
    |c_X|,|c_Y|<M:=91/60.                            (2)

Here c_X,c_Y are the actual centers. We prove the stronger uniform height conclusion

    (c_X)_y>1/10, (c_Y)_y>1/10.                      (3)

Next put rho=43/40, and use the upper angular lift. Write

    theta_X=arg(c_X) in (pi/2,pi),
    beta_a=acos(-a/rho) in (pi/2,pi).

The strict port bound a<1<rho makes beta_a well-defined. We prove

    theta_X-beta_a<3pi/10.                           (4)

Thus the actual center direction differs from the left vertical-side crossing by less than 54 degrees. Reflection gives the corresponding right-endpoint bound.

For the conditional arc consequence, suppose the complete closed centered angular arc of halfwidth pi/10 on the rho-circle lies in int(X), and suppose X's complete closed rho-circle intersection is connected. Let alpha_X be its gap-facing endpoint on the upper lift. Then

    alpha_X-beta_a<pi/5.                             (5)

The possible free side interval has length strictly less than 36 degrees. The reflected assertion holds on the right. The actual centered-arc and connectedness premises in this final consequence are not supplied by an old theorem at a different radius.

## 2. The universal endpoint estimates used below

For any contained unit K with actual support point P=(-a,h), a,h>0, and K subset {x<=-a}, the complete entry proves

    R^2>=(a+1)^2+h^2.                                (6)

It also proves, if K physically touches the circle and h>=a,

    R^2<=(a+1)^2+(h+1)^2.                            (7)

For clarity, these are genuine geometric estimates: (6) uses only containment, while (7) uses an actual physical corner attaining R. Both cover all axis means, all exposed-vertex orientations, physical two-corner ties and zero individual circle coefficients. They do not impose a two-force equation at K.

We recall the exposed-vertex form used in their proof. If the right support is not an own side axis, the actual unit is

    K=P+[0,1]u+[0,1]w,
    u=(-c,s), w=(-s,-c),
    c,s>0, c^2+s^2=1.                                (8)

The directions in (8) are actual own side vectors, not proposed selected normals. If the support is an own axis, K is aligned, and the original mean may be anywhere on its right side.

The reflected forms of (6) and (7) apply to Y at P_Y=(b,h).

## 3. An aligned endpoint cannot have center height at most one tenth

Suppose, toward contradiction, that the actual left center has height

    0<y:=(c_X)_y<=1/10.                              (9)

First suppose its support is an own side axis. Then its complete actual placement is

    X=[-a-1,-a] times [y-1/2,y+1/2].

The original application condition supplies only

    y-1/2<=h<=y+1/2.

In particular h<=3/5. Since a>0 and y>0, the actual farthest corner is the upper left one, so physical boundary contact gives

    R^2=(a+1)^2+(y+1/2)^2<=(a+1)^2+9/25.

R>=2 implies

    a+1>=sqrt(91)/5>19/10,

where 91/25-(19/10)^2=3/100. Hence a>9/10 and b<1/10<h. The reflected upper estimate (7) therefore applies to Y and gives

    R^2<=(b+1)^2+(h+1)^2
       <121/100+64/25
       =377/100<4.                                  (10)

The final positive reserve is 23/100. This contradiction includes every original mean and its two endpoint choices. In particular, no mean has been moved to the upper or lower corner of X.

## 4. Complete exposed-vertex physical-mask cover for a small center height

Now suppose (8) is the actual left unit. Set

    D=c-s, C=c+s=sqrt(2-D^2).

Its center height is

    y=h-D/2.

The assumption (9) and h>3/10 give

    D=2(h-y)>2/5>0,
    D<1,
    h=y+D/2<3/5.                                    (11)

There are only two possible physical farthest corners: the upper adjacent corner P_X+u, and the opposite corner P_X+u+w. Indeed

    |P_X+u|^2-|P_X|^2=1+2ac+2hs>0,

    |P_X+u+w|^2-|P_X+w|^2=1+2ac+2hs>0.              (12)

Thus neither P_X nor P_X+w can be farthest. The two surviving corners may tie. We cover the entire first alternative whenever the upper adjacent corner is physical, including a tie; the second argument also permits the opposite physical corner and its tie. No individual circle weight is assumed positive.

### 4.1. The upper adjacent physical corner

If Z=P_X+u lies on the circle, then |Z-P_X|=1. The actual diameter comparison for this unit edge gives

    |P_X|>=R-1>=1.

Consequently

    a>=sqrt(1-h^2)>4/5,
    b<=1-sqrt(1-h^2)<1/5<h.                          (13)

The reflected (7) is available. Its right side increases with b, so

    R^2<=(b+1)^2+(h+1)^2
       <=(2-sqrt(1-h^2))^2+(1+h)^2
       =6-4sqrt(1-h^2)+2h.                           (14)

The last continuous function is strictly increasing for 0<h<1, with derivative

    4h/sqrt(1-h^2)+2>0.

Its value at h=3/5 is exactly four. Since (11) gives h<3/5, (14) is strictly below four, a contradiction. This uses a complete interval comparison and preserves the physical tie.

### 4.2. The opposite physical corner

Suppose Z=P_X+u+w lies on the circle. Its exact squared norm is

    R^2=a^2+h^2+2+2a sqrt(2-D^2)-2hD.                (15)

For fixed a,h>0, this expression strictly decreases as D increases on the relevant interval:

    d/dD [2a sqrt(2-D^2)-2hD]
        =-2aD/sqrt(2-D^2)-2h<0.

By (9) and (11),

    D=2(h-y)>=2h-1/5>h.

Comparing (15) with its value at D=h therefore gives

    R^2<(a+sqrt(2-h^2))^2.                           (16)

Put C_0=sqrt(2-h^2)>0. Taking positive square roots in (16) yields

    R<a+C_0,
    b<1+C_0-R<sqrt(2)-1.                             (17)

If h<=b, the actual point P_Y and an actual physical corner of Y would give

    R<=sqrt(b^2+h^2)+sqrt(2)
      <=sqrt(2)b+sqrt(2)
      <2+2sqrt(2)-sqrt(2)R.

This contradicts R>=2. Hence h>b, so (7) applies to the original right endpoint.

Using (17), with all quantities being squared positive,

    R^2<=(b+1)^2+(h+1)^2
       <(2+C_0-R)^2+(h+1)^2.                         (18)

Indeed 2+C_0-R>b+1>1. Subtract the final right side from the left. The exact identity is

    R^2-(2+C_0-R)^2-(h+1)^2
        =1-2h+(R-2)(4+2C_0).                        (19)

Equations (18), (19), and R>=2 imply h>1/2.

Also h<3/5 by (11). The inequality 4<=R^2<=(b+1)^2+(h+1)^2 therefore implies b>1/5: if b<=1/5, the right side is strictly less than (6/5)^2+(8/5)^2=4. Consequently

    0<a<4/5, 1/2<h<3/5.                             (20)

Return to (15) and use D>=2h-1/5 in the same decreasing function. We obtain

    R^2<=F(a,h),

    F(a,h)=a^2-3h^2+(2/5)h+2
              +2a sqrt(2-4(h-1/10)^2).              (21)

On the whole closed comparison rectangle

    0<=a<=4/5, 1/2<=h<=3/5,

F is strictly increasing in a, since

    F_a=2a+2sqrt(2-4(h-1/10)^2)>0,

and strictly decreasing in h, since

    F_h=-6h+2/5
          -8a(h-1/10)/sqrt(2-4(h-1/10)^2)<0.

The radical is positive throughout this rectangle. The strict actual inequalities in (20) thus give

    R^2<F(4/5,1/2)
       =209/100+(8sqrt(34))/25
       <209/100+28/15
       =1187/300<4.                                 (22)

Here sqrt(34)<35/6 has squared reserve 1/36, and the final reserve is 13/300. This is again a contradiction.

Sections 3 and 4 cover every actual support feature and physical circle mask under (9). Therefore (c_X)_y>1/10. Horizontal reflection proves the same assertion for Y, completing (3).

## 5. Convert the new height into a uniform short-circle angular estimate

Put

    rho=43/40, sigma=1/sqrt(2), m=2-sigma,
    delta=pi-theta_X in (0,pi/2).

Let H_X be the actual horizontal support halfwidth of X. For a unit square,

    -(c_X)_x=a+H_X<=a+sigma.                         (23)

Every physical boundary unit satisfies |c_X|>=R-sigma>=m. Consequently

    cos(delta)<= (a+sigma)/m.                        (24)

The new height bound (3) and the strict center-radius bound |c_X|<91/60 give

    sin(delta)>6/91,
    delta>asin(6/91).                                (25)

We shall prove

    delta+asin(a/rho)>pi/5.                          (26)

Since beta_a=pi/2+asin(a/rho), equation (26) is exactly (4).

The proof splits only the scalar interval for a; it changes no actual support or center.

## 6. The entire upper interval a>=7/12

If a>=7/12, then

    a/rho>=70/129.

Both arcsin(6/91) and arcsin(70/129) lie below pi/4, so their sum lies below pi/2. Its sine is

    (6/91) sqrt(11741)/129
        +(70/129) sqrt(8245)/91.

The exact comparisons

    sqrt(11741)>108,
    sqrt(8245)>454/5

have squared reserves 77 and 9/25 respectively. Therefore this sine is strictly greater than

    35020/58695>59/100,                               (27)

with final reserve 7799/1173900.

We also have sin(pi/5)<59/100. Indeed

    sin(pi/5)^2=(5-sqrt(5))/8<25/72<(59/100)^2.

The first strict comparison follows from sqrt(5)>20/9, with squared reserve 5/81. The second reserve is 79/90000.

Sine is strictly increasing on [0,pi/2]. Thus (27) proves

    asin(6/91)+asin(70/129)>pi/5.

Together with (25), this proves (26) for the entire upper interval.

## 7. The full lower interval by one strict concavity comparison

For the whole closed interval 0<=a<=7/12 define

    F_0(a)=cos(pi/5) sqrt(1-a^2/rho^2)
             +sin(pi/5) a/rho
             -(a+sigma)/m.                          (28)

The square-root term is strictly concave and its coefficient is positive; all remaining terms are affine. Hence F_0 is concave on this entire interval and is bounded below by the smaller of its two endpoint values.

At a=0,

    F_0(0)=cos(pi/5)-sigma/m>1/5.                     (29)

For example cos(pi/5)=(1+sqrt(5))/4>4/5, while sigma<3/4 and m>5/4 give sigma/m<3/5.

At a=7/12, a/rho=70/129 and the radical is sqrt(11741)/129. The following strict rational bounds hold:

    sigma<99/140,
    (7/12+sigma)/(2-sigma)<542/543,                  (30)

    cos(pi/5)>809/1000,
    sin(pi/5)>5877/10000,
    sqrt(11741)>21671/200.                           (31)

For (30), sigma^2=1/2 and (99/140)^2-1/2=1/19600. Substitution in the increasing ratio gives exactly 542/543.

For the cosine bound in (31), sqrt(5)>559/250 follows from

    5-(559/250)^2=19/62500>0.

For the sine bound, sqrt(5)<22361/10000 follows from

    (22361/10000)^2-5=14321/100000000>0.

Then the exact positive reserve is

    (5-22361/10000)/8-(5877/10000)^2
        =9621/100000000>0.

Finally

    11741-(21671/200)^2=7759/40000>0.

All square roots and sine quantities are positive, so these squared comparisons have the displayed directions. Combining them,

    [ (809/1000)(21671/200)+(5877/10000)70 ]/129
            -542/543
        =431553/1556600000>0.                        (32)

Equations (30)--(32) give F_0(7/12)>0. With (29), concavity proves F_0(a)>0 on the entire closed lower interval.

On that interval, a/rho<=70/129<5877/10000<sin(pi/5). Thus

    0<pi/5-asin(a/rho)<=pi/5.

The first two terms of (28) are exactly

    cos(pi/5-asin(a/rho)).

Together with (24) and F_0(a)>0, strict cosine monotonicity on [0,pi] gives

    delta>pi/5-asin(a/rho).

This is (26), completing the proof of (4) on the full actual domain.

## 8. Conditional actual-arc consequence and its precise limit

Assume now that X's complete closed intersection with the circle of radius rho is connected and contains the complete closed centered arc of halfwidth pi/10 in its open interior. Its gap-facing endpoint alpha_X then satisfies

    alpha_X<theta_X-pi/10.                           (33)

Strictness is essential and follows because the specified closed centered-arc endpoint is itself an interior point of X. Combining (4) and (33),

    alpha_X-beta_a
      <3pi/10-pi/10
      =pi/5.

This proves (5), including an empty side interval when alpha_X<=beta_a. Horizontal reflection gives the right-side assertion with the actual parameter b and its unchanged endpoint.

There is a genuine remaining distinction between this side-interval estimate and a stronger occupied-channel proximity theorem. If an actual transmitter has bottom v>=1/40, its top w=v+1 is at least 41/40 but can be smaller than rho=43/40. The circle portion above that top can then connect to a side portion. Two individually short portions do not automatically give a short connected union.

More precisely, if w<rho, put

    gamma=acos(w/rho),
    x_0=sqrt(rho^2-w^2).

Even when gamma<pi/10, if a<x_0, the central and left free portions can be connected. Their joint angular length requires a further actual endpoint bound such as alpha_X<7pi/10-gamma; (5) alone does not supply it. At the lowest possible w=41/40, x_0=sqrt(42)/20. The reflected small-b domain is analogous.

Accordingly this manuscript claims neither dist(O,H)<1/40 nor an original graph/load closure. Its established new statements are the complete strict tenth-height bound, the complete 54-degree center/side comparison, and the conditional 36-degree side-interval consequence.

## 9. Actual callers, sources and verification

At a genuine unloaded degree-two width-one channel, its two original positive forces are equal and opposite and its complete original torque puts the two unchanged means at the common height h. This gives exactly (1). The new proof adds no force equation at either endpoint. In particular it retains the true degree-three W=0 in the D02.L0134 channel 0--5--4, every other positive edge including chord 02, all physical circle masks and all original means.

The source is available more broadly at every actual boundary-to-boundary side channel satisfying its geometric radius and support hypotheses. It never contracts an edge or replaces a degree-three endpoint by a transmitter.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md | 1a40004509d14eaa228ab52a4eb3280ed0f96df60e3891666f380124b5cacf9c | Complete actual force-free entry, h>3/10, positive endpoint center heights, all means/masks, center-radius bound, the full lower/upper endpoint estimates and literal channel join |
| REVIEW_FORCE_FREE_BOUNDARY_SIDE_CHANNEL_PORTS_PENTAGON_2026_10_28.md | 29d24ea50aad0d880ff5558862ef9ede551c3fd703478c66c65fdff1e844f6e1 | Existing complete independent review of that exact entry; no review is transferred to the new arguments above |

Every new mask comparison, derivative, concavity argument, sign prerequisite and rational reserve is printed in full. Exact fraction arithmetic was used only to verify the displayed identities. There is no pose sampling, numerical optimizer, finite exclusion certificate, force deletion, altered physical corner, mean substitution, new selected normal, Lean compilation, CI, remote write or shared-ledger mutation.

