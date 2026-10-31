# Both original tilted S123 root forces point away from the real leaf

Date: October 27, 2026.

**Status: complete necessary-domain theorem, submitted for root and separate
independent review.** This source removes an entire actual channel
half-plane in the surviving radial-C mask. It does not close the two
remaining direct-root features or the original S123 family.

## 1. Exact original domain

Keep the full original component

    A--B--M--C--U--A, A--L,

with its same nine physical units, true A3, true loaded B2,M2,C2,
true unloaded side transmitter U2, and genuine S leaf L. Retain all
physical circle corners, zero individual weights, actual owners and
side means.

Use the completely reviewed sources

    FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md,
    S_LEAF_C5_THREE_LOAD_TILTED_CHANNEL_DOMAIN.md,
    S_LEAF_C5_THREE_LOAD_UNIQUE_FAR_ENDPOINT_EXCLUSION.md,
    RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md.

Their separate full independent reviews are respectively the combined
REVIEW_S123_FAR_SUPPORT_AND_TILTED_CHANNEL_HEXAGON_2026_10_27.md,
REVIEW_S123_UNIQUE_FAR_ENDPOINT_HEXAGON_2026_10_27.md, and
REVIEW_RADIAL_SIDE_BOUNDARY_HALFPLANE_HEXAGON_2026_10_27.md.

The actual surviving strict-tilted coordinates are

    0<epsilon=d-1<1/60,
    L=[d,d+1] times [-1/2,1/2],
    A=(d,0)+[0,1]f1+[0,1]f2,
    f1=(-a,-b), f2=(-b,a), a>b>0, a^2+b^2=1,
    n=x f1-t f2, x>0,t>=0,x^2+t^2=1,
    m=u f1+v f2, u>=0,v>0,
    p_AB=(d,0)+Z f1+f2, 0<=Z<=1,
    q_A=(q,0), 0<q<=d, k=d-q>=0.

Here n is the original A-to-U normal, and m the original A-to-B
normal. The removed u<0 domain is exactly the complete caller of
RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md. The physical C is

    C=[d,d+1]n+[-1/2,1/2]f,
    f=t f1+x f2,
    h_A(n)=epsilon.

If u>0, Z=1 and original root properness gives

    u/v=(1-ka)/(1-kb)<=1.

If u=0, the actual unchanged side mean is Z=ka, and u<=v is
immediate. Therefore the complete direct-root range satisfies

    0<=u<=v,
    m_x=-au-bv<0,
    m_y=-bu+av>=(a-b)v>0.                              (1)

The actual channel always has n_y=-bx-at<0.

## 2. The whole channel half-plane n_x>=0 is impossible

Suppose n_x>=0. Then t>0, because x>0 and a>0. Its actual
root application is therefore the fixed vertex (d,0)+f1,
and its unchanged support is

    epsilon=(1-da)x+dbt=x+d*n_x.                        (2)

Consequently

    0<x<=epsilon<1/60,
    0<=n_x<epsilon/d<1/61.                             (3)

The actual direction of n differs from South by less than1/59.
Indeed its tangent is at most
(1/61)/sqrt(1-1/61^2)=1/sqrt(3720)<1/60.

Also (2), using da<=d, gives

    dbt<=epsilon(1+x),
    b<epsilon*sqrt((1+x)/(1-x))<1/59.                  (4)

For the last bound it suffices to use epsilon<1/60, x<1/60,
and 61*59=3599<3600.

We now verify the complete actual B-port hypotheses of Section3
of FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md.

If u>0, its actual point is the opposite A vertex

    P=(d-a-b,a-b).

Since 0<=1-a<=b and d=1+epsilon,

    -b<P_x<=epsilon<1/30.

If u=0, retain its original mean Z=ka. The exact channel line
gives

    k=t/(bx+at)>=1-bx/t,
    q=d-k<=epsilon+bx/t
             <=epsilon/(1-x)<1/59.                    (5)

Here the middle upper bound follows from dbt<=epsilon(1+x)
and t^2=(1-x)(1+x); no mean is selected. The actual P_x is

    P_x=d-a^2 k-b=q+k b^2-b.

Since kb<db<1, equations (4)--(5) imply

    -b<P_x<q<1/59<1/30.

In both complete root features the actual vertical coordinate is

    P_y=a-bZ, 0<=Z<=1,
    29/30<a-b<=P_y<=a<1.                               (6)

The strict lower bound follows from a>=1-b^2 and b<1/59:
the reserve between 1-1/59-1/59^2 and 29/30 is1681/104430.

Thus the actual boundary unit B contains P with

    |P_x|<1/30, 29/30<P_y<=1.

The actual physical C has minimum n support d>1>59/60, and
(3) puts its normal within1/59 of the opposite, South vertical.
The actual B--M--C boundary path therefore contradicts the
whole force-free endpoint theorem in Section3 of the cited
far-support source. This theorem retains the real physical M;
no unloaded reserve is substituted between B and C.

Hence n_x>=0 is impossible.

## 3. Exact conclusion and scalar identities retained for later callers

The whole surviving tilted original radial-C domain now satisfies

    m_x<0<m_y,       n_x<0, n_y<0,
    0<=u<=v,        x>epsilon.                         (7)

The last inequality follows from (2) when t>0. If t=0, x=1,
so it holds there as well.

For clarity, in the strict-channel case t>0, put
p_AU=epsilon*n-T*f. The unchanged unit side from the real
leaf point to this actual application gives the exact identities

    db=x*T+epsilon*t,
    da=1-epsilon*x+t*T,
    T^2+2*t*T=2*epsilon*(1+x),
    q=d*T/(t+T).                                      (8)

They follow directly by projecting p_AU=(d,0)+f1 on the actual
n,f frame and using x^2+t^2=1. Every T is the original actual
transverse mean; no physical parameter is interpolated.

When t=0, retain instead the whole original A-owned mean:

    da=1-epsilon, db=2*sqrt(epsilon),
    T=db-Y, 0<=Y<db, q=d*T/(db).                        (9)

Formula (8) is not imposed on this side-mean domain unless Y=0.

The direct A-owned f2 mean u=0 and the opposite A vertex u>0
remain the two exact tilted obligations. The high aligned root
remains separate. No original fine or coarse gate is declared
closed by (7), and no force, radial weight, body, or completion
is deleted.

