# Positive root-normal projection throughout the f-owned/shared HK branch

**Status: complete hand implication; root and separate independent saved-source
and exact-arithmetic review passed. Both original g-corner alternatives are
covered. The full LOW diamond parent remains open.**

## 1. Original domain and exact claim

Use the actual f-owned/shared HK row of the accepted complete upper-left
diamond fan, with its true H5/K3/A2/B2 equations, original means, physical
circle masks and all nine squares. Write

    q0=6241/1600 <= q <= 1105/256,
    zA=(a,b), a>b>3/5, a^2+b^2=q,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    P=(a-1,b-1), H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    f=(s,c)=E n+p j, g=(-c,s)=-p n+E j,
    E^2+p^2=1, p>=0, s,c>0,
    L=(a-1)s+bc, h=-(a-1)c+bs,
    delta=c-rp, K=[L-delta,L+1-delta]f+[h,h+1]g.

A has its actual negative root pressure. The independently accepted uniform
triangle theorem gives u/v>5/9 throughout the original radius interval,
without a high-radius premise. Since s=Eu-pv>0, one has 0<=p<u.

K is an original circle-loaded unit, so at least one of its physical
corners has squared norm q. Then

    c_H dot n=P dot n-1/2>0.                        (1)

The proof checks both actual g-coordinate extremes h and h+1. It does
not assign either one by a force sign, and it retains every KB feature.
No K2 equation is used below.

## 2. Enlarge the original r interval without moving a packing square

Suppose (1) fails. Put

    N=zA dot n, D=-zA dot j=av-bu>0,
    S=u+v, V=v-u, N^2+D^2=q,
    C=1+P dot n=1+N-S, G=1+v-D.

Then N<=S+1/2. The original K far f coordinate is positive:
delta<=c and L>(3/5)c give

    L+1/2-delta>1/2-(2/5)c>1/10.

Its farthest-f endpoint increases with r, because p>=0. Thus replacing
r by 1 in the upper bound for the upper-g corner's squared norm is an enlargement
of a scalar comparison, not a displacement of any original body.
The g coordinates remain unchanged.

At that enlarged endpoint the far-f, upper-g corner, expressed
in the original (n,j) frame, is exactly

    (C-deltaRot,G+Z),
    deltaRot=(1-E)(1+p)+ps,
    Z=p(1-c)+E(1-E).                               (3)

For example it is T+(1-c+p)f+g, where T=(a-1,b); expanding in n,j
gives (3). Both deltaRot and Z are nonnegative.

We next verify the bounds needed for the reviewed rotation inequality.

First P dot n>0. If not, since a>1 and u/v>5/9, one would have
5a+9b<14 and 3/5<b<1. Consequently

    q=a^2+b^2<[(14-9b)/5]^2+b^2
      <=2074/625<6241/1600.

The quadratic here has derivative (-252+212b)/25<0 on (3/5,1);
its value at b=3/5 is 2074/625. The final radius reserve is
23289/40000. This contradiction proves C>1.

Also S<=sqrt(2)<99/70 gives N<67/35. Therefore

    D^2>q0-(67/35)^2>(12/25)^2,

with final reserve 11241/1960000. The ratio u/v>5/9 gives
v<9/sqrt(106)<7/8. Hence

    G<1+7/8-12/25=279/200<7/5.                     (4)

No lower sign of G is needed for the comparison: Z>=0 suffices.
LOW_DIAMOND_F_INTERFACE_ROTATION_INEQUALITY.md, on its full enlarged
domain u/v>=8/15 and 0<=p<=u, now gives

    (C-deltaRot)^2+(G+Z)^2<=C^2+G^2.                (5)

Indeed the difference is deltaRot^2+Z^2-2C deltaRot+2GZ,
bounded above by deltaRot^2+Z^2-2deltaRot+(14/5)Z<=0.
This retains the genuine p=0 shared-HK endpoint.

## 3. One uniform circle comparison for the aligned bound

We prove C^2+G^2<q under the whole enlarged domain

    u^2+v^2=1, 5/9<u/v<=1, N^2+D^2=q>=q0,
    0<N<=S+1/2, D>0.

Set A=S-1>0 and B=1+v>1. Direct expansion gives

    q-C^2-G^2=2AN+2BD-A^2-B^2.                     (6)

For fixed u,v,N, the right side increases with D. Since
q>=q0 and (S+1/2)^2<q0, it is at least

    F(N)=2AN+2B sqrt(q0-N^2)-A^2-B^2,
    0<=N<=S+1/2.

This function is concave in N, so its minimum on that entire interval
is at an endpoint. At N=0,

    F(0)=2(79/40)B-A^2-B^2>0,

because 79/40>3/2, B<2 and 0<A<1.

For the other endpoint put t=u/(1+v). The whole original ratio domain
is contained in 1/4<=t<=5/12. The rational unit identities give

    u=2t/(1+t^2), v=(1-t^2)/(1+t^2),
    N_max=S+1/2=(3+4t-t^2)/[2(1+t^2)].

The inequality F(N_max)>0 is equivalent to

    sqrt(q0-N_max^2)>
          (2-3t+t^2+t^3+t^4)/[2(1+t^2)].           (7)

The right side is positive since 2-3t>=3/4. Squaring (7), multiplying
by its positive denominator and expanding leaves one polynomial:

    P(t)=1041/400-12t+(1641/200)t^2+10t^3
          +(6241/400)t^4+4t^5-3t^6-2t^7-t^8>0.    (8)

Here is a table-free completion-of-squares proof on the whole interval.
Put y=t-1/3, so |y|<=1/12. The exact expansion is

    P=2321/26244-(16079/21870)y
       +(1068763/36450)y^2+(775921/24300)y^3
       +(447521/32400)y^4-(236/27)y^5
       -(97/9)y^6-(14/3)y^7-y^8.

After factoring y^2 from the terms of degree at least two, their
coefficient is at least

    1068763/36450-(775921/24300)/12
       -(236/27)/12^3-(97/9)/12^4-(14/3)/12^5-1/12^6
      =26+48883423/74649600>26.

The fourth-degree positive term was simply dropped. Thus

    P>=2321/26244-(16079/21870)y+26y^2
      >=4140689159/49742877600>0.                   (9)

Equations (7)--(9) prove the other endpoint comparison. Concavity
therefore proves (6) strictly positive for every original N,D in
the enlarged domain. No angle or pose subdivision is used.

## 4. Both corner alternatives and the complete contradiction

For the original upper-g corner, the scalar enlargement to r=1,
(3)--(5), and Section 3 give

    (L+1-delta)^2+(h+1)^2
       <= |enlarged corner|^2 <= C^2+G^2 < q.        (10)

For the other corner, LOW_DIAMOND_F_INTERFACE_NEGATIVE_G_CORNER.md
proves throughout an even larger domain u/v>=8/15, under the same
cn<=0 hypothesis, that

    (L+1-delta)^2+h^2<q.                            (11)

Its proof retains every r in [0,1] and every p in [0,u]. It establishes
N>S and D>17/35, then uses one monotonicity comparison in p and one
strictly increasing polynomial on the entire half-angle interval.
Root independently checked its complete coordinate identities,
all sign conditions, both original scalar intervals, the endpoint
polynomial and every exact reserve.

The original K center has strictly positive f coordinate, as shown
in Section 2. Consequently, at each fixed g endpoint the other f
endpoint has strictly smaller squared norm. Equations (10)--(11)
therefore put all four original K corners strictly inside the circle.
This contradicts K's original positive circle load and proves (1).

No sign or far-corner choice at K is assumed. The genuine p=0 shared-HK
normal and its full original mean interval remain. No normal or force
is reselected; all body degrees, the petal and every completion square
are unchanged.

## 5. Review and retained scope

Root derived the positive upper-g comparison. The separate
low_radius_diamond reviewer read the full saved source and its
original whole-window angle prerequisite, independently reconstructed
the corner coordinates, the concavity argument, the endpoint
equivalence, all nine polynomial coefficients, all nine shifted
coefficients and every exact reserve with Fraction arithmetic.
No gap was found.

The same agent authored the separate rotation and lower-g lemmas.
Root independently expanded their full polynomial identities and
checked every geometric/sign prerequisite, complete monotonicity
interval and exact endpoint reserve. The joined theorem thus covers
the entire original f-owned/shared HK type, including every actual
K circle corner.

This establishes a positive H-normal projection. The separate complete
LOW_DIAMOND_F_INTERFACE_UNIQUE_RETURN_EXCLUSION.md and
LOW_DIAMOND_F_INTERFACE_RADIAL_RETURN_EXCLUSION.md now supply the
original HB/KB cover and genuine H5/K3 force join for both B masks.
REVIEW_LOW_F_INTERFACE_2026_10_25.md records the combined independent
review. The remaining LOW H-owned n and free n/g HK types, unrestricted
theorem, original equality and older full-chain audit stay open.
No Lean compilation or CI was run.

