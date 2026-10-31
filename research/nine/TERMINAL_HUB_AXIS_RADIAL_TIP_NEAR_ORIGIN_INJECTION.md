# A complete radial-tip terminal-axis interface supplies a near-origin unit with a strict vertex margin

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete new local theorem and conditional two-near-unit exclusion, frozen for full independent review.** The actual hub in the entire physical-two-V domain of the stated V-owned return interface has distance from O strictly below 1/60, and every one of its vertices has norm strictly above 7/100. The result uses the original boundary-W application. It requires no occupied hub pocket, no small-center hypothesis, no equation at W or T, and no boundary-path hypothesis.

The existing radial-pocket manuscript supplied and separately proved the local force/mask chart and scalar estimates. The new geometric step uses the actual W port to prevent the hub's transverse coordinate from exceeding one. The complete local proof, including the older scalar estimates needed here, is printed below so that its scope does not depend on that manuscript's fully loaded-path caller.

## 1. Full physical local statement

Keep four distinct actual closed unit squares U,V,W,T with pairwise disjoint open interiors in the same origin-centered disk

    2<=R<=sqrt(Q_*), Q_*=1105/256.

Retain the common compatible selected physical certificate, every original positive magnitude, original application or shared-side mean, full physical circle mask and possible individual zero circle coefficient. U is genuinely unloaded of positive degree three, with its entire original neighborhood V,W,T. V is genuinely loaded of positive degree two, with its entire original pair neighborhood U,W. W is physically boundary and otherwise has arbitrary degree and circle weights. T has arbitrary degree and need only be an actual contained neighbor.

Suppose the actual interface, in one unchanged rigid coordinate frame, is

    U=[x-1,x] x [p-1,p],
    P=P_UV=(x,p), Q=P_UW=(x,p-1),
    S=P_UT=(x-1,p-h),

    n=n_UV=(a,b), m=n_UW=(c,-d),
    a,b,c,d>0, a^2+b^2=c^2+d^2=1,
    n_UT=West.

The UV normal is V-owned and P is in the relative interior of that actual V side. The UW normal is W-owned and Q is in the relative interior of that actual W side. The UT application is its original point or mean on the West side; no singleton premise on UT is needed.

Put

    k=Jn=(-b,a), l=Jm=(d,c),
    K=ad+bc>0, L=ac-bd>0, K^2+L^2=1.

The original V-to-W normal is

    g=-k.

Assume V has two physical circle corners. Both are retained even if one individual coefficient is zero.

**Local theorem.**

    dist(O,U)<1/60,
    |Z|>7/100 for every actual vertex Z of U.          (1)

**Two-near-unit corollary.** There cannot also be two distinct actual units H,E, different from U and interior-disjoint from U and one another, with

    dist(O,H),dist(O,E)<=1/40,
    every vertex of H and E has norm >3/50.            (2)

No original graph/load flag is closed by the local theorem alone. A caller must prove the actual two units in (2) and their distinctness.

## 2. Original support and full-force equations

Let mu,nu,lambda>0 be the original magnitudes at UV,UW,UT. The entire original U3 force and torque give

    mu*b=nu*d,
    lambda=mu*a+nu*c,
    1-h=mu*a/lambda=ad/K,

so

    h=bc/K in(0,1).                                  (3)

In particular an original UT mean is forced into the relative interior by the full equations; it is not moved there.

Write V in its actual own frame (n,k):

    V=P+[0,1]n+[-rho,1-rho]k, 0<rho<1,
    m=(L,-K), l=(K,L).

Because L,K>0, W's maximum-k vertex is the upper endpoint M of its minimum-m side. The original Q lies in that side's relative interior. The actual V-axis support g=-k gives

    M=Q+sigma*l, 0<sigma<1,
    W=M+[-1,0]l+[0,1]m.

The actual VW contact is a singleton. The original strict isolated vertex/vertex convention for the selected own-axis normal g makes M a relative-interior point of V's minimum-k side. Thus, at the unchanged actual point,

    M=P-rho*k+tau*n, 0<tau<1.

Comparing coordinates gives

    sigma=(b+tau)/K,
    rho=(d-L*tau)/K=a-(L/K)(b+tau),
    0<tau<K-b.                                       (4)

These are the actual parameters, with both strict side-interior hypotheses retained. The excluded endpoint contacts belong to other original selected interfaces; they are not silently reassigned to this one.

Let omega>0 be the original VW magnitude, distinct from nu. The complete true V2 resultant is

    F_V=mu*n+omega*k.                                (5)

No W or T force equation is used.

## 3. Every physical-two V mask is covered

Both components in (5) are positive. A contained boundary square's physical circle corners are its farthest vertices, so both own center coordinates are nonnegative. They cannot both be zero since R>=2.

First suppose the n-center coordinate is zero. Then in the actual (n,k) frame

    V=[-1/2,1/2] x [D,D+1],
    D=sqrt(R^2-1/4)-1>1/2,
    P=(-1/2,D+rho).

The actual world horizontal coordinate satisfies

    x=-a/2-b(D+rho)<-(a+b)/2<-1/2.

But T lies wholly to the West of its actual support S, whose world x coordinate is x-1. Every unit square has horizontal width at least one. Since T is contained in the disk, this implies

    x>=2-R>-1/12,

because Q_*<(25/12)^2. This contradicts x<-1/2. This exit needs neither a boundary status nor a force equation at T.

The full remaining physical-two mask is therefore

    V=[D,D+1] x [-1/2,1/2],
    P=(D,q), M=(D+tau,-1/2),

    q=rho-1/2,
    187/200<D<61/60.                                 (6)

The lower squared comparison is 231/40000; the upper one is 31/57600. The radius endpoint R=2 is included.

The full resultant can be written Lambda*(D+1,xi). The physical two-corner weights and (5) give

    0<xi<=1/2.

The original torque is

    mu*q=omega*(D+tau).

Thus

    q>0, rho>1/2,
    (D+1)q=xi*(D+tau)<=(D+tau)/2.                    (7)

The endpoint xi=1/2 is retained. No unique-circle equality is imposed on this physical-two domain.

## 4. Entire W circle-mask derivation

In the same frame the actual square is

    W=M+[-1,0](K,L)+[0,1](L,-K).

Its m-center coordinate is (D+tau)L+K/2+1/2>0. Therefore all its physical circle corners are on its maximum-m face. They are among the two actual candidates

    Z_+=M+m,
    Z_-=M-l+m.

Put

    zeta=K(D+tau)-(1+L)/2.

The plus point can be physical only if zeta>=0 and the minus point only if zeta<=0. Equality keeps both physical corners.

The exact deficits from the original radius are

    R^2-|Z_+|^2
      =2D(1-L-tau)-tau^2-2L*tau-K,

    R^2-|Z_-|^2
      =2D(1-L-tau+K)-tau^2-2tau(L-K)-(1+L+K).       (8)

If the minus point were physical, put H0=1-L-tau+K>1-L>0, using tau<K. Its equality in (8) gives

    D+tau=[-tau^2+2tau+1+L+K]/(2H0).

Expansion using K^2+L^2=1 yields

    2zeta=tau(1+L+2K-K*tau)/H0>0.

This contradicts the required zeta<=0, and excludes the tie as well. Hence W has the unique physical circle corner Z_+, and its exact equation is

    D=[tau^2+2L*tau+K]/[2(1-L-tau)].                 (9)

Its numerator is positive, so 1-L-tau>0. In particular

    D>D0:=K/[2(1-L)]=(1+L)/(2K).                    (10)

Every possible W physical mask was retained before deriving this unique-corner consequence. There is no V2 substitution for W's true degree.

## 5. Complete local scalar bounds

Set z=L/K>0. We need only the following consequences:

    z*tau<1/16, z<4/5, tau<3/7,
    rho<727/847, b>9/100.                            (11)

These are continuous consequences of (4), (7), and (9), not sampled pose bounds.

### 5.1. The product z*tau

For fixed L,K, define

    F(t,D)=t^2+2(D+L)t+K-2D(1-L).

Its positive root tau increases with D because

    d tau/dD=(1-L-tau)/(D+L+tau)>0.

At D_*=61/60 the positive comparison root t_* exists by D_*>D>D0 and has t_*<1-L. Its positive quadratic term gives

    tau<t_*<[2D_*(1-L)-K]/[2(D_*+L)].

Using (1-L)/K=K/(1+L), the desired z*tau<1/16 follows from

    976 L K<(61+540L)(1+L).                          (12)

The elementary K<=1-L^2/2 reduces the right-minus-left difference to

    H(L)=61-375L+540L^2+488L^3.

For 0<=L<=1/5, its quadratic part decreases and is at least 38/5. For L>=1/5,

    H(L)>=(3188/5)L^2-375L+61
         >=61-703125/12752
          =74747/12752>0.

This proves (12) on the full L interval, including the split endpoint, and proves the first bound in (11).

### 5.2. z, tau, and the full rho interval

The exact identity

    z=D0-1/(4D0)

and (10) give

    z<61/60-15/61=2821/3660<4/5.                    (13)

For tau, subtract the polynomial F(t,D,0)=t^2+2Dt+1-2D from the same polynomial at L. The difference is

    2L(D+t)+K-1
       =L[2(D+t)-L/(1+K)]>0

for every relevant t>=0, using D>187/200. Thus the actual positive tau is below the positive root at L=0. That root increases with D. At D=61/60,t=3/7 the polynomial is 16/735>0. Therefore tau<3/7.

Since tau<1, the quantity (D+tau)/(2(D+1)) increases with both D and tau. Equation (7) therefore gives

    rho<1/2+(61/60+3/7)/(2(121/60))
        =727/847.                                   (14)

Both original circle-weight endpoints allowed by (7) remain included.

Suppose b<=9/100. Then a>199/200 since

    1-(9/100)^2-(199/200)^2=3/1600>0.

Using the actual identity rho=a-zb-z*tau and the first two bounds of (11),

    rho>199/200-(4/5)(9/100)-1/16
        =1721/2000>727/847.

The last reserve is 3687/1694000. This contradicts (14), proving b>9/100.

These local comparisons require no later small-port bound, no T2 properness, and no boundary-path order.

## 6. The original hub is within one sixtieth of O

Transform (6) back to the unchanged world frame:

    P=D*n+q*k,
    x=aD-bq,
    p=bD+aq,
    0<q<1/2.                                        (15)

From (4), a>rho>1/2; hence b<sqrt(3)/2. Consequently

    x>187/400-sqrt(3)/4>0.                           (16)

Both compared quantities in the final inequality are positive, with squared reserve 4969/160000. Also

    x<aD<D<61/60.                                    (17)

Meanwhile b>9/100 and D>187/200 give

    p>bD>1683/20000>7/100.                           (18)

The last reserve is 283/20000.

The key additional fact is that the unchanged point

    Q=(x,p-1)

belongs to the actual physical boundary square W. Therefore the unit diameter gives

    |Q|>=R-sqrt(2)>=2-sqrt(2).                       (19)

If p>=1, then (15) gives

    |Q|^2=x^2+(p-1)^2
          =D^2+q^2+1-2p
          <(61/60)^2-3/4
           =1021/3600.                              (20)

But

    (2-sqrt(2))^2>12/35>1021/3600,

using sqrt(2)<99/70, with final rational reserve 1493/25200. This contradicts (19). Thus

    0<p<1.                                          (21)

The actual vertical interval [p-1,p] contains zero in its interior. The actual horizontal interval [x-1,x] has x>0 and x<61/60. If x<=1, U contains O. If x>1, its distance to O is x-1<1/60. In both cases,

    dist(O,U)<1/60.                                 (22)

This argument does not assume the stronger x<1 estimate from the old radial-pocket proof and does not need its rho>17/25 conclusion. It preserves the entire remaining x>=1 strip as well.

## 7. Every actual hub vertex stays strictly away from O

The two original right vertices P and Q lie in actual physical boundary units V and W. The diameter bound puts both at norm at least R-sqrt(2)>7/100.

The upper-left vertex is (x-1,p). Its norm is at least p>1683/20000>7/100 by (18).

For the lower-left vertex, the triangle inequality and (15) give

    |(x-1,p-1)|>=sqrt(2)-|P|.

Now

    |P|^2=D^2+q^2<(61/60)^2+1/4<(8/7)^2,

with final squared reserve 3971/176400. Since sqrt(2)>7/5,

    |(x-1,p-1)|>7/5-8/7=9/35>7/100.

The final reserve is 131/700. Every actual vertex is covered, including the unused left vertices and every circle-weight endpoint.

Equations (22) and these four vertex inequalities prove the entire local theorem (1).

## 8. Exclusion of two distinct additional near-origin units

The complete radius-free near-origin lemma in Section 4 of

    SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md

states that if 0<delta<d_0/2 and d_0<1/2, at most two actual interior-disjoint unit squares can each meet the closed disk D_delta while every vertex has norm greater than d_0. Its proof uses complete angular measures on the same small circle and includes squares containing O, squares with O on a side, and squares outside O.

Take

    delta=1/40, d_0=3/50.

The strict ratio condition holds since delta/d_0=5/12<1/2. By (1), the original U meets D_delta and every U vertex has norm greater than 7/100>3/50. If the two distinct actual units H,E in (2) also existed, U,H,E would be three squares satisfying this exact lemma, a contradiction.

This is an injection using the unchanged hub itself. It does not move an extra into U, replace a boundary unit by a tip, infer dist(O,U)<1/40 from a small center, or discard a positive force.

## 9. Exact conditional D02.L0134 application

The literal graph is the original rim

    01,12,23,34,45,50

with its original positive chord 02 and load set {0,1,3,4}. Put

    U=2, V=1, W=0, T=3, H=5.

Then U is truly unloaded degree three, V is truly loaded degree two, W remains truly loaded degree three, T remains truly loaded degree two, and H is truly unloaded degree two on the actual channel 0--5--4. All three other physical squares remain.

In the stated terminal-axis V-owned return interface with L>0 and physical-two V, the local theorem applies directly. Unlike the old radial-pocket caller, it makes no requirement that the actual path V,W,H,4,T be entirely loaded. H is retained as genuinely unloaded. No nonexistent boundary edge is substituted for the channel.

If the actual side-channel exterior pocket is occupied, the separately established force-free occupied-channel theorem provides the unchanged H with

    dist(O,H)<1/40,
    every H vertex has norm >7/100.

If an actual central extra E is also present in the bounded central free union, the existing enclosed-unit side/corner restrictions provide

    dist(O,E)<sqrt(2)*121/7200<1/40,
    every E vertex has norm >19/300>3/50.

The actual finite core ring and all its chords remain in place for this central restriction. U,H,E are distinct by their original labels and the definition of an extra. They therefore contradict Section 8.

Consequently the **whole physical-two-V domain of this local interface cannot realize an allocation with both an occupied side-channel pocket and a central extra**. In particular it excludes the candidate allocation (central, hub-closing, side-channel)=(1,1,1) at this interface. The existence or geometry of the hub-closing extra is not needed for this contradiction.

This is not a claim that every original U-normal owner interface has the displayed chart, or that a unique-circle V mask satisfies the radial equations. Those separate original-domain obligations remain outside this manuscript. Root alone owns any original-row union and ledger adoption.

## 10. Exact sources, scope, and proof provenance

The complete local algebra in Sections 2--5 is reproduced from the actual local portions of the already reviewed radial-pocket source. Its fully loaded-path hypothesis is not used or transferred here; the new source explicitly proves its own local scope before the geometric injection.

| Source | SHA256 | Exact role |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_RADIAL_MASK_POCKET_CAPACITY_ONE.md | b3ee9bd0861293bb828e243399a98e31128589d0dfc91ea6f9f37b9cf78e9580 | Actual local support and physical-mask calculations in Sections 2--5, and the first b>9/100 calculation of Section 8; all needed calculations are reproduced above. No pocket, T2, or fully loaded-path conclusion is imported. |
| REVIEW_TERMINAL_HUB_AXIS_TIP_OWNED_RADIAL_POCKET_ROOT_2026_10_28.md | f96ac654135ee35409303fd236fa415f84544d8943ccced607fac579a9acd911 | Independent complete review of those exact old bytes; not a transferred review of the new theorem. |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | Only its complete radius-free Section 4 theorem with delta=1/40 and d_0=3/50. |
| FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md | 5e8f69ad14c78b6ad99a1ba46855fc3627df5ccc1d5451f295826d2b06709abb | Only the separately reviewed original occupied-side-channel proximity and vertex margin for the conditional caller in Section 9. Not needed for the local theorem or the abstract corollary. |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | b9329b7a81b57cd0fef4b62c69c26388face02b8b985c79624aa285416284733 | Only the whole-ring enclosed-unit own-center and vertex restrictions in the conditional caller. No simple-cycle stress reduction. |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, load mask, true degrees, and distinct extra-unit contract. |

The new use of the actual boundary-W point Q, the full hub distance and four-vertex bounds, and the local two-near-unit contradiction are authored here. House supplied the earlier radial physical chart and full-weight identity, as disclosed in the old source. Root suggested examining the original boundary applications in the joint allocation, and cycles supplied the separately reviewed full-channel proximity theorem. These contributions remain disclosed for independent review.

All displayed rational reserves were recomputed exactly. There is no sampled pose, numerical-angle subdivision, new computational geometry certificate, altered original normal, relocated mean, force deletion, Lean compilation, CI, remote mutation, or shared-ledger edit.

