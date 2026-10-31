# Two adjacent hub vertices cannot feed the same boundary side through a nonparallel loaded tip

Date: October 28, 2026 UTC. Authors: pentagon continuation; house supplied the original same-W-side chart and its sole-UT interface.

**Status: complete proposed local hand theorem, submitted for independent review.** Every physical V circle mask and every original application in the stated strict-angle domain is included. The proof puts all four actual W corners strictly inside the containing circle. It does not use a force equation at U, W or T, a pocket estimate, or an extra-square allocation.

The endpoint n dot m=0 is explicitly outside this theorem: there VW may be a positive shared side and its original mean need not be the V endpoint M used below. This manuscript neither moves that mean nor claims that parallel endpoint closed.

## 1. Complete local theorem

Keep actual pairwise interior-disjoint closed unit squares in the unchanged disk D_R, with

    2<=R<=sqrt(1105/256).                              (1)

Let U be any actual unit, of arbitrary degree and load. In axes of U write its adjacent right vertices as

    P=(x,p), Q=(x,p-1).

The actual positive UV normal is a V own side axis

    n=(a,b), a,b>0, a^2+b^2=1,

and its unchanged application is P. The actual positive UW normal is a W own side axis

    m=(c,-d), c,d>0, c^2+d^2=1,

and its unchanged application is Q. The original positive V-to-W normal is the same m. Assume

    n dot m=ac-bd<0.                                 (2)

V is positively circle-loaded and its entire positive pair neighborhood is exactly U,W. W physically touches the containing circle; its degree, load and all other forces are arbitrary. Retain the original strict point-contact convention, all physical circle corners, all individual zero circle coefficients, and every original force/application.

**Theorem.** These hypotheses are inconsistent.

In particular this excludes the entire strict-angle part of the original sole-UT feature where UW and VW use the same W-owned side normal. It includes all original V physical masks. No U3, W3 or T2 equation is replaced by a smaller one.

## 2. Exact actual side geometry

Put

    k=J n=(-b,a), l=J m=(d,c),
    K=ad+bc>0, v=bd-ac>0,
    K^2+v^2=1.

In the n,k frame,

    l=(K,-v), m=(-v,-K).                              (3)

P is a U vertex and n is a V own axis. The strict original convention therefore makes P a relative-interior point of the actual V minimum-n side. Write

    V=P+[0,1]n+[-rho,1-rho]k,
    0<rho<1.                                        (4)

Both components of m in (3) are strictly negative. The actual VW application is consequently the unique V minimum-n,minimum-k vertex

    M=P-rho*k.

Because m is a W own axis, M is in the relative interior of its minimum-m side under the same strict convention. Q is also in the relative interior of this actual side.

The equality m dot (M-Q)=0 gives rho*K=d. The actual positive tangential displacement is

    M-Q=delta*l,
    rho=d/K, delta=b/K.                              (5)

Since both Q and M are in the relative interior of one unit side, the actual W has the full chart

    W=M+[-u,1-u]l+[0,1]m,
    delta<u<1.                                      (6)

Thus 0<delta<1. The minimum-m lower endpoint M-u*l is not identified with Q; their actual strict gap is retained.

From (5),

    (b,a)=rho*(0,1)+delta*(K,-v),
    b=K*delta, a=rho-v*delta,

and therefore

    rho^2+delta^2-2v*rho*delta=1,
    delta=v*rho+sqrt(1-K^2*rho^2).                    (7)

The other quadratic root is negative because rho<1. Since delta<1, squaring the positive comparison sqrt(1-K^2*rho^2)<1-v*rho gives

    rho>2v, v<1/2, K>sqrt(3)/2,
    z=v/K<1.                                        (8)

No equation at U or W was used.

## 3. Full V force, concurrence and every physical circle mask

Write P=(A,B) in the n,k frame. The unchanged positive V magnitudes mu at UV and nu at VW give its complete outward circle resultant

    F=mu*n-nu*m,
    F_n=mu+nu*v>0, F_k=nu*K>0,
    F dot l=mu*K>0.                                 (9)

The physical farthest-coordinate rule, including zero-center ties, gives

    A>=-1/2, B-rho>=-1/2,
    X=A+1>=1/2, Y=B+1-rho>=1/2,
    X^2+Y^2=R^2.                                    (10)

The two original pair-force lines meet properly at

    q=P+rho*z*n=(A+rho*z,B).                         (11)

Full torque makes q parallel to F. At least one of A,B is positive: otherwise X<=1 and Y<1 would contradict R^2>=4. The corresponding component of q is positive. Since both components of F are positive, q is a positive multiple of F. Hence

    B>0,
    q dot l=K*A-v*(B-rho)>0.                         (12)

### 3.1. The physical mask X=1/2

Here A=-1/2 and B-rho=Y-1=sqrt(R^2-1/4)-1>0. This makes the last expression in (12) negative. The entire radial-along-k mask is excluded, including every coefficient endpoint, without a T-boundary premise.

### 3.2. The unique physical circle mask

Now X,Y>1/2, and the complete outward resultant is a positive multiple of the actual unique circle corner (X,Y). Combining this with (11) gives

    X*(1-rho)/Y=1-rho*z.

Because rho<1 and z<1, this implies X>Y. With lambda=Y/X,

    rho=(1-lambda)/(1-lambda*z).                     (13)

### 3.3. The remaining physical two-circle mask Y=1/2

Here X=sqrt(R^2-1/4)>1/2. The full physical circle resultant has the form

    F=Lambda*(X,xi), Lambda>0, 0<xi<=1/2,

where all original weights are retained. The positivity xi>0 follows from (9); xi=1/2 is allowed. Equation (11) and positive concurrence give

    X*(rho-1/2)=xi*(X-1+rho*z)
                  <=(X-1+rho*z)/2.

Consequently X>Y=1/2 and

    rho<=(1-lambda)/(1-lambda*z),
    lambda=Y/X.                                     (14)

The possibility of both centers being zero is incompatible with (1).

Thus the entire surviving physical V domain, without selecting a circle coefficient, obeys

    X>Y>=1/2, X^2+Y^2=R^2,
    M=(X-1,Y-1),
    0<rho<1, 0<lambda=Y/X<1,
    rho<=(1-lambda)/(1-lambda*z).                    (15)

Equality is not imposed on the physical-two domain.

## 4. Uniform side-length bounds for the whole domain

Let r=X/Y. From the radius window and Y>=1/2,

    r^2<=4R^2-1<=1041/64<(33/8)^2,
    r<33/8.                                         (16)

Equation (15) is equivalent to

    r>=(1-rho*z)/(1-rho).

By (8), z<rho/sqrt(4-rho^2). Therefore

    r>f(rho),
    f(t)=(1-t^2/sqrt(4-t^2))/(1-t).                 (17)

This entire scalar function increases on 0<t<1. If S=sqrt(4-t^2), direct differentiation gives

    (1-t)^2*f'(t)
      =1-(2t-t^2)/S-t^3*(1-t)/S^3
      >1-2/3-8/27=1/27.

Here S>3/2, 2t-t^2<=1 and t^3*(1-t)<=1. At t=6/7,

    f(6/7)=7-9/sqrt(10)>33/8,

because 23^2*10-72^2=106>0. Equations (16)--(17) prove

    rho<6/7,
    v<3/7,
    K>2sqrt(10)/7>6/7,
    delta>sqrt(1-rho^2)>sqrt(13)/7>1/2.              (18)

These are whole-domain bounds, not sampled angles.

We shall also use

    R<25/12,
    X>=sqrt(2), Y<3/2,
    X+Y>12/5.                                       (19)

For the last inequality, at fixed R the sum sqrt(R^2-Y^2)+Y increases on Y<=R/sqrt(2), so it is at least (sqrt(15)+1)/2>12/5. The earlier strict comparisons use sqrt(15)>19/5 and sqrt(2)>7/5.

## 5. A continuous arc comparison used below

For fixed positive A_0,B_0, the function

    A_0*sqrt(R^2-Y^2)+B_0*Y

is concave for 1/2<=Y<=R/sqrt(2). Its minimum occurs at an endpoint. Both endpoint values increase with R>=2. Consequently positivity of an expression

    2A_0*X+2B_0*Y-C_0

throughout (15) follows from its two endpoint values

    A_0*sqrt(15)+B_0-C_0,
    2sqrt(2)*(A_0+B_0)-C_0.                          (20)

This is a comparison over the full continuous circle arc, not a pose test.

Put

    t=M dot l=K*(X-1)-v*(Y-1)>0.                     (21)

For the unique mask positivity follows from (12). For Y=1/2 it follows directly from X>1 and v>0. Also t<=|M|<R because M is a noncircle vertex of the actual V.

## 6. All corners of the comparison square u=1 are strictly inside

Consider M+[-1,0]l+[0,1]m.

M itself is strictly inside the disk. The corner M-l has deficit

    R^2-|M-l|^2
      =2X+2Y-3+2t>0.

For M-l+m the exact deficit is

    R^2-|M-l+m|^2
      =2[(1+K)*(X+Y-2)+v*(X-Y)]>0.                  (22)

For M+m use (20), with A_0=1+v, B_0=1+K and C_0=3+2v+2K. At the lower-Y endpoint the deficit is

    (1+v)*(sqrt(15)-2)-K>9/5-1=4/5.

At the diagonal endpoint it is

    2*(2+v+K)*(sqrt(2)-1)+1>0.

Thus all four corners of the comparison square u=1 are strictly inside. This comparison square carries no artificial forces and is not substituted into the actual configuration.

## 7. Three easy corners of the comparison square u=delta

The minimum-m lower corner is Q=M-delta*l. It is an actual U corner, so

    |Q|<=R.                                         (23)

Only this non-strict bound is needed; the actual u satisfies u>delta.

The minimum-m upper corner is

    N=M+(1-delta)*l.

Set s_0=1-delta in (0,1/2). Its deficit is

    R^2-|N|^2
      =2X+2Y-2-2s_0*t-s_0^2
      >24/5-9/4-25/12=7/15>0.                      (24)

We used (19),(21), not a circle condition on U.

For Q+m=M-delta*l+m, the squared norm is convex as a function of delta on [1/2,1]. The endpoint delta=1 was handled in (22). At delta=1/2 write

    M-l/2+m=(X-A_0,Y-B_0),
    A_0=1+v+K/2, B_0=1+K-v/2.

Equations (18) and v<1/2 give 7/5<A_0,B_0<=2. By (20), at the lower-Y endpoint its deficit is

    A_0*sqrt(15)+B_0-A_0^2-B_0^2
      >84/25-2=34/25>0.

Indeed A_0*(19/5-A_0)>=84/25 on [7/5,2], while B_0*(1-B_0)>=-2. At the diagonal endpoint it is

    A_0*(2sqrt(2)-A_0)+B_0*(2sqrt(2)-B_0)
      >16/5>0,

using u*(14/5-u)>=8/5 on [7/5,2]. Convexity therefore proves |Q+m|<R throughout the complete actual delta interval.

## 8. The remaining corner: exact setup

The only comparison corner still to check is

    N+m=M+(1-delta)*l+m=(X-A_1,Y-B_1),

where

    A_1=1+v-(1-delta)*K,
    B_1=1+K+(1-delta)*v.

The exact deficit is

    D=R^2-|N+m|^2
      =A_1*(2X-A_1)+B_1*(2Y-B_1).                   (25)

We have

    delta+v<=A_1<=1+v,
    1+K<=B_1<=2+v/2,
    0<v<3/7<1/2.                                    (26)

Also B_1>Y by (18)--(19). We shall prove D>0 over two exhaustive closed Y intervals, with their common endpoint included.

## 9. The whole interval Y>=3/4

Put alpha=1/2+v and beta=2+v/2. By (18),(26), A_1>=alpha. The concave function A*(2X-A) has its minimum on [alpha,1+v] at an endpoint, and

    (1+v)*(2X-1-v)-alpha*(2X-alpha)
       =(2X-3/2-2v)/2>0.

Thus its smaller endpoint value is the one at alpha. Since B_1>Y and B_1<=beta, the second summand in (25) is at least beta*(2Y-beta). Hence

    D>=alpha*(2X-alpha)+beta*(2Y-beta).

This last expression is concave in v on the entire comparison interval [0,1/2], so it suffices to check v=0 and v=1/2.

At v=0 it is X+4Y-17/4. Concavity in Y on [3/4,R/sqrt(2)] and increasing endpoint values in R>=2 reduce it to

    (sqrt(55)-5)/4>1/2,
    5sqrt(2)-17/4>0.

At v=1/2 it is 2X+(9/2)Y-97/16, whose two endpoint comparisons are

    sqrt(55)/2-43/16>13/16,
    (13/2)sqrt(2)-97/16>0.

Here sqrt(55)>7. This proves D>0 throughout the full high-Y interval.

## 10. The whole interval 1/2<=Y<=3/4

In this interval (15),(19) give

    49/200<lambda=Y/X<5/12.                          (27)

The lower comparison follows from lambda>=8/sqrt(1041)>49/200; the exact squared numerator reserve is 60559>0. For the upper one, X>=sqrt(55)/4>9/5.

Put

    rho_0=1-lambda,
    delta_0=sqrt(1-rho_0^2)=sqrt(lambda*(2-lambda)).

Then rho_0>=7/12 and delta_0>1/2. We claim the uniform improvement

    delta+v>=delta_0+3v/4.                           (28)

If rho<=rho_0, equation (7) gives delta>=v*rho+sqrt(1-rho^2)>=v*rho+delta_0, which proves (28).

If rho>rho_0, (15) gives

    rho-rho_0<=lambda*rho*v/K.

Write f_0=sqrt(1-rho^2)>1/2. Then (18),(27) imply

    delta_0-f_0
      =(rho+rho_0)*(rho-rho_0)/(delta_0+f_0)
      <(12/7)*(5/12)*(7/6)*v
       =5v/6.

Together with (7) and rho>rho_0>=7/12, this gives

    delta+v>=v*rho+f_0+v
              >delta_0+3v/4.

This proves (28) in both complete rho subdomains, including the inequality in the physical-two mask.

Now set alpha=delta_0+3v/4 and beta=2+v/2. We have A_1>=alpha and A_1<=3/2<X, so the first summand of (25) increases with A_1. The second decreases with B_1>Y. Therefore

    D>=alpha*(2X-alpha)+beta*(2Y-beta).

Again this is concave in v on [0,1/2]. Its endpoint expressions, after using X>=2/sqrt(1+lambda^2) and Y=lambda*X, are

    F_0(lambda)
      =4*(delta_0+2lambda)/sqrt(1+lambda^2)
          -delta_0^2-4,

    F_1(lambda)
      =4*(delta_0+3/8+(9/4)lambda)/sqrt(1+lambda^2)
          -(delta_0+3/8)^2-81/16.                    (29)

Both increase throughout the entire interval (27). More generally set

    F(lambda)=4*(delta_0+t_0+B_0*lambda)/sqrt(1+lambda^2)
                  -(delta_0+t_0)^2-B_0^2.

Using delta_0'=(1-lambda)/delta_0, direct differentiation gives

    F'(lambda)
      =4[(1-lambda-lambda^2)/delta_0+B_0-t_0*lambda]
           /(1+lambda^2)^(3/2)
        -2*(delta_0+t_0)*(1-lambda)/delta_0.          (30)

On [49/200,5/12], the first numerator term is positive and (1+lambda^2)^(3/2)<4/3. For F_0, (30) is greater than 6-2=4. For F_1, B_0-t_0*lambda>=67/32 and delta_0>1/2 give

    F_1'(lambda)>201/32-7/2=89/32>0.

It remains to evaluate the single common left endpoint lambda_0=49/200. Here

    delta_0^2=17199/40000,
    131/200<delta_0<21/32,
    sqrt(1+lambda_0^2)<103/100.

These rational comparisons yield the strictly positive exact reserves

    F_0(lambda_0)
       >458/103-4-17199/40000
        =68503/4120000>0,

    F_1(lambda_0)
       >1265/206-6273/1024
        =1561/105472>0.                             (31)

Equations (29)--(31) prove D>0 on the whole low-Y interval. No coordinate sample or computational sign certificate is used.

## 11. Return to the unchanged actual W

Sections 7--10 put three corners of the comparison square u=delta strictly inside D_R and its fourth corner Q in the closed disk. Section 6 puts all four corners of the comparison square u=1 strictly inside.

For each fixed corner choice, its actual position in (6) is affine in u. Since delta<u<1, the convexity of squared norm, or of the disk itself, now places every actual corner strictly inside D_R. The one non-strict comparison in (23) becomes strict because the other endpoint is strictly inside and the actual interpolation parameter is interior.

Thus every point of actual W has norm strictly less than R. This contradicts its physical boundary contact. The theorem is proved for all W physical masks simultaneously, without assuming which W corner is farthest and without using any W force equation.

## 12. Literal original interface and the parallel endpoint

For original D02.L01345 use

    U=2, V=1, W=0, T=3,
    loaded path 1,0,5,4,3,

with the complete rim, positive chord02, load set {0,1,3,4,5}, original degrees U3,V2,W3,5_2,4_2,T2 and all three extras retained. In the sole-UT branch, after reflection, the original UV and UW contacts occur at the two adjacent right U vertices P,Q with n Northeast and m Southeast. If the original VW normal is the same W-owned m and n dot m<0, Sections 1--11 apply literally.

The true U3 equations may still be retained in the form

    K=ad+bc,
    S=(x-1,p-bc/K),

for its unchanged West application, but this proof does not need that application, any T circle mask, or any equation at T. It does not infer a leaf or a two-force W.

At n dot m=0, V and W are parallel, and VW can have positive shared length. The actual original VW mean need not equal the endpoint P-rho*k. In that endpoint domain (13)--(15) need a different mean term. No conclusion about that entire shared endpoint, the whole sole-UT branch, or the original D02 row is claimed here.

## 13. Exact direct inputs and preservation

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Strict original vertex/vertex convention; full V2 force and torque; physical circle coefficients |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | The original same-W-side caller has n dot m<=0; this theorem separately assumes the strict part |
| D02_ALL_MASK_FREE_UV_EXCLUSION_AND_EXACT_SINGLE_HUB_AXIS_COVER.md | 214475cb4a6fe839b6589a346e12f2aea9be97b958a5229e1c1ff4344740e670 | Literal sole-UT owner interface only; no force or application reselection |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original D02 rim/chord/load set, true degrees and all three extras |

All new geometry, physical-mask reductions, and continuous scalar estimates are printed in full. House supplied the original interface chart; pentagon derived and owns the all-mask corner comparison above. Independent review is required against these complete bytes.

Exact rational checks verify only printed identities and reserves. There is no Lean compilation, CI, workflow, numerical pose sample, orientation mesh, numerical exclusion certificate, normal reselection, changed side mean, dropped force, shared ledger mutation, commit, remote write or whole original gate credit.

