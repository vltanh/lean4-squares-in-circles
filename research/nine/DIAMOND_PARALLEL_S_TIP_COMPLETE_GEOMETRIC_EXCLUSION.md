# Complete geometric exclusion of the hub/tip diamond with a parallel S tip

Date: October 27, 2026.

**Status: complete new hand proof of the entire parallel-tip interface;
full independent review requested.** This is a fresh derivation from the
readable sources pinned in Section 7. It does not reconstruct or invoke
an absent earlier complete proof from a historical hash. The nonparallel
tip remains a separate original interface.

Keep all nine actual contained, interior-disjoint unit squares and the
common compatible selected certificate. The original positive edges are

    HK, HB, HC, KB, KC, HL, BM.

H and B are genuine S-leaf roots, with actual leaves L and M. K and C
have positive total circle loads. The genuine degrees remain
H4,K3,B3,C2,L1,M1. Preserve all original forces, normals, support owners,
application means, physical circle masks and individual zero weights.

Assume the remaining high-radius domain

    d=1+epsilon, 0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4<=1105/256,

and suppose the actual two nonleaf forces at B are parallel.

**Theorem.** This entire original interface is impossible.

## 1. The actual remaining frame and its unique circle corner

The complete parallel-B cover and H-owned exit are proved in
DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_OWNED_HUB_EXCLUSION.md. The complete
tilted-H reduction, including every non-K-owned HK contact and every
aligned K, is proved in
DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_TILTED_HUB_REDUCTION.md. Their
original statements retain precisely the graph and degrees above.

After their common rotation and reflection, their entire remaining
actual frame is

    M=S(East), B=[epsilon,d] times [a_B-1,a_B],
    P=p_BH=(epsilon,y), Q=p_BK=(epsilon,z),
    -1<z<-16/25<0<y<9/25,
    Delta=y-z<=1,
    u=(-c,-t), v=(-t,c), c,t>0, c^2+t^2=1,
    H=P+[0,1]u+[0,1]v,
    U=P+u, V=P+v,
    w=(-a,b), j=(-b,-a), a,b>0, a^2+b^2=1,
    K=Q+[0,1]w+[0,1]j,
    U=Q+sigma*w, 0<sigma<1,
    c=sigma*a, Delta=t+c*b/a<=1.                    (1)

The original B torque, mu_H*y+mu_K*z=0, remains. In particular
none of y,z,sigma is a replacement mean. Put

    k=b/a, A_+=a+b, A_-=a-b, q_0=-z.

The last relation in (1) gives

    0<k<=c/(1+t)<1,  A_->0,  16/25<q_0<1.         (2)

The only possible physical circle corner of K is

    Z=Q+w+j=(epsilon-A_+,-q_0-A_-).                 (3)

Indeed Q has squared norm below1+epsilon^2. At Q+w both
coordinates have absolute value below1. At Q+j,

    |Q+j|^2 < b^2+epsilon^2+(1+a)^2
             =2+2a+epsilon^2<4+epsilon^2<17/4.

Thus all three other actual corners are strictly inside the circle.
Since K is physically boundary, (3) has norm exactly R. Using
A_+^2+A_-^2=2, its exact identity is

    q_0^2+2q_0*A_-=9/4+2epsilon*(2+A_+)>9/4.       (4)

Since q_0<1, (4) gives A_->5/8. The function
(1-k)/sqrt(1+k^2) decreases strictly for k>=0, and its value at
3/8 is 5/sqrt(73)<5/8. Therefore

    0<k<3/8.                                      (5)

This is a physical unique-corner conclusion, not a positive-weight
submask choice. The full K3 equation remains unaltered.

## 2. A sharper actual H angle: t>39/50

We prove

    t>39/50, c<63/100.                             (6)

Suppose t<=39/50. For fixed k in (5), the function
T+k*sqrt(1-T^2) increases on 0<=T<=39/50: throughout that interval
sqrt(1-T^2)>3/5 and T*k/sqrt(1-T^2)<39/80<1.
Since sqrt(979)/50<63/100, (1) gives

    q_0=Delta-y<Delta
       <=39/50+(sqrt(979)/50)k
       <D(k):=39/50+(63/100)k.                     (7)

Write g(k)=(1-k)/sqrt(1+k^2)=A_-. Equation (4) and (7) require

    9/4<D(k)^2+2D(k)g(k).                          (8)

Here is a complete elementary estimate contradicting (8), with both
ends of the k interval retained.

For 0<=k<=1/3, the exact positive-square identity

    (1+z)(1-z/2+3z^2/8)^2-1
      =z^3(40-15z+9z^2)/64>0, z>0,

gives g(k)<=(1-k)(1-k^2/2+3k^4/8). Expanding the resulting lower
bound for9/4-D^2-2Dg gives

    51/625-(1707/2500)k+(16431/10000)k^2
       -(3/20)k^3-(243/200)k^4
       +(9/80)k^5+(189/400)k^6.

The cubic and quartic negative terms are bounded by -(1/20)k^2
and -(27/200)k^2 respectively. Dropping only the nonnegative last
two terms leaves

    51/625-(1707/2500)k+(14581/10000)k^2>0.          (9)

Its exact positive discriminant reserve is
4*(51/625)*(14581/10000)-(1707/2500)^2=2427/250000;
its minimum on the whole real line is2427/1458100.

For 1/3<=k<=3/8, 1/sqrt(1+k^2)<=3/sqrt(10)<19/20. Therefore

    D^2+2Dg <D^2+(19/10)D(1-k)
       =2613/1250+(3489/5000)k-(8001/10000)k^2.

The last quadratic increases through k=3/8, where its value is
1433319/640000=9/4-6681/640000. This again contradicts (8).
These two closed ranges prove t>39/50. Its squared consequence
c^2<979/2500<3969/10000 proves the second assertion in (6).

## 3. The full real H leaf forces tau<1/5

In the H frame put

    tau=epsilon*c+y*t, kappa=y*c-epsilon*t,
    A=1-tau, D=1+kappa.

The actual H rectangle is [-tau,A] times [kappa,D]. The complete
genuine-leaf cover in the reduction has exactly two possibilities:

* an H-owned +v leaf, with y*c=epsilon*(1+t);
* a strict leaf at V=P+v, with
  y^2+2c*y=2epsilon*(1+t).

Thus in both full leaf types

    0<tau<=epsilon*(1+t)/c.                         (10)

If c>=1/6, (10) immediately gives tau<1/5. To include every
smaller c, suppose 0<c<1/6 and set q=t-y. Then
t>49/50, q>31/50, q<1 and k<c<1/6.

For an auxiliary scalar s in [0,k], put

    h(s)=(1+s)/sqrt(1+s^2),
    g(s)=(1-s)/sqrt(1+s^2),
    Phi(s)=(h(s)-epsilon)^2+(q+c*s+g(s))^2.

This is only a comparison of explicit scalar values; it does not
move a square or reselect an original contact. Its derivative is

    Phi'(s)/2
       =-[epsilon*g(s)+(q+c*s)h(s)]/(1+s^2)
          +c*(q+c*s+g(s))
       <-(31/50)(36/37)+73/216
       =-53003/199800<0.                            (11)

Here h>=1, g<=1, q<1 and c*s<1/36 were used. At the actual k,
Phi(k)=R^2 by (3); hence Phi(0)>R^2. It follows that

    q>k_A:=sqrt(13/4+6epsilon)-1,
    401/500<k_A<5/6, k_A<t.

Consequently

    tau<epsilon*c+t(t-k_A)
       =1-k_A-c^2+k_A*(1-t)+epsilon*c
       <1-k_A-c^2/2+epsilon*c
       <=1-k_A+epsilon^2/2
       <99/500+1/7200<1/5.                          (12)

The strict middle inequality uses k_A/(1+t)<1/2. The final
reserve against1/5 is67/36000. This finishes both genuine-leaf
types over the entire c range. In particular

    A>4/5, D>59/60.                                (13)

## 4. Every actual C center lies in one of two far-face regions

The exact physical argument in Section4 of the readable reduction
applies to the present tilted K after replacing its aligned bottom
vertex by the actual Q. Here are all its required geometric facts.

P is a relative side-interior point of B and a strict vertex of H,
so no third unit through it has a free right-angle sector. U is a
relative side-interior point of K by 0<sigma<1, and a strict H
vertex, giving the same exclusion. The triangle with vertices
P,U,Q has its three complete sides in H,K,B respectively. It is
nondegenerate, lies strictly inside the containing disk, and lies
on the outward side of H's near side P-U. A boundary C entering
that side enters this occupied closed pocket and cannot leave it
through its sides or weak endpoints. The actual genuine H leaf
excludes V, including its owned-leaf shared-side endpoint as
proved in the reduction.

Thus C can meet H only on its far-u face, its far-v face, or the
opposite vertex. If (X,Y) are its true center coordinates in the
unchanged H frame, necessarily

    X>=A+1/2 or Y>=D+1/2.                           (14)

For a side this is the true center halfwidth bound. At the opposite
vertex (A,D), its center is within sqrt(2)/2 of that point and
cannot pass either near side of H. If both coordinates exceed
A,D, the actual incircle has distance at least1/2 from H, giving

    |c_C|^2>=A^2+D^2+1/4+min(A,D)
       >(4/5)^2+(59/60)^2+1/4+4/5>(91/60)^2.

If both coordinates are below A,D, the center lies in H. Otherwise
the sole coordinate beyond the far face has excess at least1/2.
This proves (14) for every actual vertex and side endpoint.

The second alternative in (14) is impossible. Every contained
center has norm<91/60, so that center's direction is less than
pi/12 from v because (D+1/2)/(91/60)>89/91>cos(pi/12).
The real H-leaf center direction is v or is within pi/12 of v,
since its strict direction has coordinates(-tau,D) and
tau/D<12/59<tan(pi/12). Two distinct boundary centers would then
be separated by less than pi/6, contrary to the strict2pi/9
boundary-center separation.

It remains to exclude the entire first alternative in (14).

## 5. The actual tilted K transverse center improves the aligned bound

Retain the radius R and the actual H axes c,t. As a function of
an auxiliary s in [0,k], define

    h(s)=(1+s)/sqrt(1+s^2), g(s)=(1-s)/sqrt(1+s^2),
    F(s)=sqrt(R^2-(h(s)-epsilon)^2).

The square root is positive throughout this interval: h increases
and F(k)=q_0+A_->0. The actual K center from (3) is

    c_K=(epsilon-h(k)/2,-F(k)+g(k)/2).

Its v coordinate is the value at s=k of

    B(s)=-t*epsilon+t*h(s)/2-c*F(s)+c*g(s)/2.

The exact derivative has the sign of

    t/c+2(h(s)-epsilon)/F(s)-h(s)/g(s),              (15)

since B'(s)=c*g(s)/(2(1+s^2)) times that expression.
Here t/c>9/8 by (6), F(s)<R<25/12 and s<3/8.
For 0<=s<=1/3, h>=1 and h/g<=2, so (15) is greater than

    9/8+118/125-2=69/1000>0.

For 1/3<=s<=k, h>=4/sqrt(10)>5/4 and h/g<11/5, so it is
greater than

    9/8+148/125-11/5=109/1000>0.

Consequently the actual v coordinate is strictly greater than
its explicit s=0 comparison value:

    B_K>B(0)=t*(1/2-epsilon)-c*(k_A+1/2),
    k_A=sqrt(13/4+6epsilon)-1<5/6.                  (16)

Again this is solely a monotone scalar comparison of the actual
circle identity. It does not introduce a new aligned K, use an
aligned force equation, or change a physical side mean.

## 6. All three remaining center-angle ranges contradict the actual order

The selected straight-center drawing is plane, and all physical
boundary centers are strictly exposed, by the full degree-independent
drawing lemmas in TWO_NEAR_HUBS_BOUNDARY_DIAMOND_EXCLUSION.md. B is
exterior to the diamond because its real BM strand reaches the
exposed leaf M; C is itself boundary. Thus H-B-K-C-H is the outer
face and HK remains its interior chord. The genuine HL and BM
strands give the original boundary order L,M,K,C, up to reversal.

Here L lies in the second quadrant, K's actual center in the third,
and M is on the positive horizontal ray. Hence C's center lies
strictly between L and K on the counterclockwise arc avoiding M.
This is the same complete original exterior-order argument in
Section5 of the readable reduction; no degree or physical feature
used in that argument assumed K aligned.

In the remaining first cap of (14), let delta be the absolute angle
between c_C and u. The true center bound gives

    cos(delta)>(A+1/2)/(91/60)>6/7.                  (17)

The u coordinate of c_K is positive, since c_K has both world
coordinates negative and u=(-c,-t). Also |c_K|>4/3. If B_K>=0,
the actual order puts C farther clockwise than K from u, so their
gap is at most delta, already smaller than2pi/9. If B_K<0,
write alpha for K's counterclockwise deviation from u. Then

    sin(alpha)=|B_K|/|c_K|,
    gap(C,K)<=delta+alpha.                         (18)

The following three closed-range estimates cover all0<c<63/100.
They use only the actual leaf estimate(10), the center comparison
(16), and the exact center order just proved.

### 6.1. 0<c<=2/5

Here t>9/10. Equation(16) gives

    B_K>(9/10)(29/60)-(2/5)(4/3)>-1/10.

Thus sin(alpha)<3/40, cos(alpha)>99/100, while (17) gives
sin(delta)<13/25. Therefore

    cos(gap(C,K))>(99/100)(6/7)-(3/40)(13/25)
                   =5667/7000>4/5.                (19)

### 6.2. 2/5<=c<=1/2

Now t>173/200, and(16) gives B_K>-1/4. Hence
sin(alpha)<3/16<19/100 and cos(alpha)>49/50.
The actual leaf bound(10) gives tau<1/12, so

    cos(delta)>85/91>91/100, sin(delta)<21/50.

Consequently

    cos(gap(C,K))>(91/100)(49/50)-(21/50)(19/100)
                   =203/250>4/5.                  (20)

### 6.3. 1/2<=c<63/100

Use t>39/50 and k_A+1/2<4/3 in(16):

    B_K>(39/50)(29/60)-(63/100)(4/3)=-463/1000.

Thus sin(alpha)<1389/4000<7/20 and cos(alpha)>15/16;
the latter squared reserve is8179/16000000.
Here t<sqrt(3)/2<13/15. Equation(10) gives tau<14/225 and hence

    cos(delta)>1294/1365>18/19, sin(delta)<13/40.

The two exact reserves for these last comparisons are16/25935
and1809/577600 respectively. Therefore

    cos(gap(C,K))>(18/19)(15/16)-(13/40)(7/20)
                   =11771/15200
                   =77/100+67/15200>77/100.        (21)

All angle sums above are below pi/2 by their displayed bounds, so
the cosine comparisons follow directly from(18). The accepted
boundary-center gap is greater than2pi/9, whereas
cos(2pi/9)<77/100. For the latter exact comparison, 4x^3-3x is
strictly increasing for x>1/2, equals-1/2 at cos(2pi/9), and has
value greater than-1/2 at77/100. Each of(19)--(21) is a contradiction.
This excludes the first cap and finishes the remaining tilted K frame.

## 7. Exact whole parallel-tip join and frozen prerequisites

The full original parallel-B cover first gives its actual aligned
B frame. The H-owned HB case is wholly excluded by the first source
below. The second source wholly excludes non-K-owned HK and aligned K,
and gives the exact remaining tilted frame(1). Sections1--6 above
exclude that entire frame with both actual H-leaf types and all original
side endpoints. Thus every parallel-B case at high radius is excluded.
The low/critical domain is separately complete for the same graph in
ADJACENT_LEAF_ROOT_TRIANGLE_LOW_CRITICAL_EXCLUSION.md. No nonparallel-B
case or whole hub/tip fine gate is claimed by the present theorem alone.

| Readable prerequisite | SHA-256 |
|---|---|
| DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_OWNED_HUB_EXCLUSION.md | f8f118f4f326a4a83f0aab31909bdc3008af381086204c8ff16092b7d0a628b2 |
| DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_TILTED_HUB_REDUCTION.md | 5fb11f502f63d0c25e0737a99129c27179a8e4a22e6c3811de42acdc426c7fa0 |
| TWO_NEAR_HUBS_BOUNDARY_DIAMOND_EXCLUSION.md | 6fa0dc8ad21463d6f33b8c200fc8a56d21df81eb21a024fd1288e7932f3e4954 |

The first prerequisite has full independent acceptance in
REVIEW_DIAMOND_PARALLEL_TIP_OWNED_HUB_HEXAGON_2026_10_27.md.
The second has the fresh full independent read and acceptance in
REVIEW_DIAMOND_PARALLEL_TIP_TILTED_REDUCTION_HEXAGON_2026_10_27.md.
The new proof above awaits its own separate complete review.

Every original H4/K3/B3/C2 force is retained. After the true B3
reduction, the new final contradiction is entirely physical geometry;
no false lower-degree star or zero-external-moment triangle is used.
There is no numerical certificate, altered mean, post-extraction
normal change, metadata edit, remote action, compilation or CI.
