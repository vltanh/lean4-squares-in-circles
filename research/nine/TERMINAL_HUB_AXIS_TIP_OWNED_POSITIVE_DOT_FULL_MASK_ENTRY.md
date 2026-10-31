# Full physical-mask entry for a terminal-axis hub with a perpendicular tip-owned return

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed local chart and uniform whole-mask exclusions, submitted for independent review.** This source proves the exact actual chart for the remaining V-owned return -Jn, derives the entire W mask without choosing a circle corner, excludes all Y>=X for every W mask, and excludes all Y>=1 in the physical plus mask. The last exclusion holds on the wider closed radius interval 4<=R^2<=5.

This is a reusable family-wide entry, not a whole original D02 exclusion. The remaining unique plus and minus domains and the radial V domain retain their separate full proof obligations.

## 1. Actual local hypotheses

Keep actual contained, pairwise interior-disjoint unit squares in the unchanged disk D_R. Assume R>=2. U has zero total circle load and exactly the original positive pair neighbors V,W,T. V has positive total circle load and exactly the original positive pair neighbors U,W. W and T physically touch the containing circle. Their true degrees and all other forces remain arbitrary.

After rotating about the original origin and reflecting if needed, suppose the original support chart is

    U=[x-1,x] x [p-1,p],
    P=P_UV=(x,p), Q=P_UW=(x,p-1),

    n=n_UV=(a,b), m=n_UW=(c,-d),
    a,b,c,d>0, a^2+b^2=c^2+d^2=1,

    n_UT=West.

V owns n at the actual relative side-interior point P. W owns m at the actual relative side-interior point Q. These are actual physical singletons. Keep the original strict point-contact convention.

Put

    k=Jn=(-b,a), l=Jm=(d,c),
    K=ad+bc>0, L=ac-bd>0, K^2+L^2=1.                (1)

Assume the original directed VW normal is the V axis

    g=n_VW=-k.                                       (2)

No original normal is changed. The actual UT application may be a singleton or the unchanged full weighted mean of a genuine shared feature. In either case write

    S=(x-1,p-1+t).

The original positive U3 magnitudes give exactly

    t=ad/K, h=1-t=bc/K,
    S=P-(1,h), 0<h<1.                               (3)

Indeed full force gives mu*b=nu*d and the West magnitude mu*a+nu*c; torque about Q gives its product with t equal to mu*a. This uses all three actual U forces.

The entire physical V mask and every individual zero circle coefficient remain. No force equation at W or T is introduced.

## 2. Complete actual VW feature and original side parameters

The actual V is

    V=P+[0,1]n+[-rho,1-rho]k, 0<rho<1.              (4)

In V coordinates,

    m=(L,-K), l=(K,L).

Both K,L are strictly positive. The original incoming W normal g=-k therefore strictly exposes its maximum-k vertex. This is the upper endpoint of W's minimum-m side, whose relative-interior point is the actual Q. Call that vertex M. Thus

    M=Q+sigma*l, 0<sigma<1,
    W=M+[-1,0]l+[0,1]m.                             (5)

On V, the original g is its minimum-k side axis. Because g is not a W side axis, the intersection is a physical singleton. The original strict convention makes M a relative-interior point of that V side: otherwise a vertex/vertex singleton would have a non-strict V normal. Consequently

    M=P-rho*k+tau*n, 0<tau<1.                       (6)

This is the original actual application, not a replacement endpoint or a mean chosen after extraction.

The equality M-Q=(0,1)+tau*n-rho*k, projected on m and l, yields

    rho=(d-L*tau)/K
         =a-(L/K)*(b+tau),
    sigma=(b+tau)/K,
    0<tau<K-b<K.                                   (7)

All strict endpoint statements follow from the actual relative-interior contacts. Closed endpoints below occur only in enlarged scalar comparisons.

## 3. Entire physical V mask and the exact original terminal port

Let omega>0 be the original VW magnitude, separate from the UW magnitude nu. The true V2 force is

    F_V=mu*n+omega*k,

with both own components strictly positive. Hence both own center coordinates are nonnegative, and its actual farthest coordinates can be written

    V=[X-1,X] x [Y-1,Y],
    X,Y>=1/2, X^2+Y^2=R^2,

    P=(X-1,Y-1+rho),
    M=(X-1+tau,Y-1).                                (8)

If one center coordinate vanishes, both corresponding physical circle corners remain. Both cannot vanish since R>=2.

The mask X=1/2 is impossible whenever R<25/12. In that mask Y-1=sqrt(R^2-1/4)-1>1/2, so the actual world coordinate

    x=a*(X-1)-b*(Y-1+rho)<-(a+b)/2<-1/2.

But the actual boundary T is wholly to the left of its West support point S and has horizontal width at least one. Its containment gives x>=2-R>-1/12, a contradiction. The later uniform X>Y proof also excludes X=1/2 directly and needs no upper-radius assumption.

Put

    s=1-tau in (1-K,1), J=X-s.

When X,Y>1/2, V's physical circle mask is unique, with corner (X,Y). Its full original torque, combined with F_V=Lambda*(X,Y), is precisely

    X*(1-rho)=Y*(1-tau),
    rho=1-(Y/X)*s.                                  (9)

Neither original force magnitude has been identified with the UW magnitude.

When Y=1/2, the complete resultant has the form Lambda*(X,xi), 0<xi<=1/2. Its full torque retains the weaker inequality

    Y*(1-tau)<=X*(1-rho),                            (10)

once J>0; that positivity follows from the uniform X>Y result below. Equation (9) is not imposed on this physical-two mask.

In the positively oriented frame (-k,n), the unchanged terminal application from (3) is exactly

    S=(-A_T,B_T),

    A_T=Y-1+rho+b-h*a,
    B_T=X-1-a-h*b,
    h=bc/K.                                         (11)

These identities assert neither A_T>Y nor B_T>=X-2. Such bounds, if needed by a later caller, must be proved on that caller's actual full domain.

## 4. A force-free theorem puts the whole W minimum-m face strictly inside

The following argument uses only X,Y>=1/2, X^2+Y^2>=4, K,L>0, K^2+L^2=1, and 0<tau<K. It does not use any V torque equation or T premise.

The actual M in (8) lies strictly inside D_R. It is in the relative interior of V's minimum-k side; at least one own-coordinate norm is strictly below the farthest coordinate. This includes Y=1/2 and X=1/2 separately.

For M-l, put

    A=1+K-tau in (1,1+K),
    B=1+L.

Its exact circle deficit is

    R^2-|M-l|^2=2AX+2BY-A^2-B^2.                   (12)

At fixed R>=2 and positive A,B, the minimum of the linear part on the circle arc X,Y>=1/2 is at one of its endpoints. This follows from concavity of A*X+B*sqrt(R^2-X^2) on the complete interval. Both endpoint values increase with R. It therefore suffices to use

    (X,Y)=(1/2,sqrt(15)/2)
    or (sqrt(15)/2,1/2).

For either endpoint, the deficit is concave in A, so its minimum on [1,1+K] is at A=1 or A=1+K. The four endpoint expressions are

    (1+L)*(sqrt(15)-1-L),

    sqrt(15)-1-L-L^2,

    sqrt(15)-2-K+(sqrt(15)-2)*L,

    sqrt(15)-2-L+(sqrt(15)-2)*K.                     (13)

All are strictly positive; the latter three are at least sqrt(15)-3>0, and the first is positive because 1+L<2<sqrt(15). This proves (12) strictly throughout the full enlarged continuous domain.

By convexity of the squared norm, the entire actual face [M-l,M] is strictly inside D_R. If W's m-center coordinate were nonpositive, a physical farthest corner would lie on that face. This would contradict actual physical boundary W. Hence its m-center coordinate is strictly positive.

Define its actual own coordinates

    C=M.m+1=L*(X-s)-K*(Y-1)+1>1/2,
    z=M.l=K*(X-s)+L*(Y-1).                         (14)

The complete physical W mask is exactly

    plus:  Z_W^+=M+m,       z>=1/2 if physical;
    minus: Z_W^-=M-l+m,     z<=1/2 if physical.       (15)

At z=1/2 both physical corners remain. Their actual circle equations are respectively

    C^2+z^2=R^2,
    C^2+(z-1)^2=R^2.                                (16)

This is an exhaustive farthest-face derivation, not a selected algebraic circle point.

## 5. One whole-angle theorem excludes every Y>=X mask

Assume Y>=X. Then Y>=R/sqrt(2)>=sqrt(2).

For the plus point, put

    A=s-L, B=1+K.

Its deficit is again 2AX+2BY-A^2-B^2. If A>=0, then 0<=A<1 and X>=1/2, while B<2<2Y. The horizontal term A*(2X-A) is nonnegative and the vertical term is strictly positive.

If A<0, write v=-A. Since tau<K,

    0<v<K+L-1<=sqrt(2)-1,
    B<2,
    u=B-v in (1,2).

Using X<=Y and Y>=sqrt(2), the deficit satisfies

    -v*(2X+v)+B*(2Y-B)
       >=2Y*(B-v)-B^2-v^2
       >=u*(2sqrt(2)-u)-2Bv.

The concave quadratic u*(2sqrt(2)-u) has minimum 4(sqrt(2)-1) on [1,2]. On the other hand 2Bv<4(sqrt(2)-1). Thus the plus point is strictly inside in this case too.

For the minus point use

    A=s+K-L in (1-L,1+K-L),
    B=1+K+L.

Both are positive. At each fixed R>=2, the minimum of its linear deficit on the arc Y>=X>=1/2 is at

    (X,Y)=(1/2,sqrt(R^2-1/4))
    or (R/sqrt(2),R/sqrt(2)).

Both endpoint values increase with R, and concavity in A reduces to A=1-L or A=1+K-L. At A=1+K-L the two R=2 endpoint deficits are

    (sqrt(15)-3)*(1+K)+(sqrt(15)-1)*L>0,
    4*(sqrt(2)-1)*(1+K)>0.

At A=1-L the first endpoint is

    sqrt(15)-2-L^2+(sqrt(15)-2)*K
                       +(sqrt(15)-1)*L-2KL
       >=sqrt(15)-3
          +(sqrt(15)-2)*K
          +L*(sqrt(15)-1-2K)>0.

The diagonal endpoint is

    4sqrt(2)-4+K^2+2K*(sqrt(2)-1-L)
       >=4sqrt(2)-4+K^2+2K*(sqrt(2)-2)
       >=8sqrt(2)-10>0.                            (17)

The last line completes the square; sqrt(2)>5/4 makes its strict sign explicit.

Thus both possible physical farthest W corners would be strictly inside D_R. The whole actual boundary W cannot exist. Consequently every original physical configuration in Sections 1--4 satisfies

    X>Y>=1/2, X>sqrt(2).                            (18)

This excludes the entire Y>=X domain simultaneously for unique V, physical-two V, either W mask and the physical W tie. It uses no upper radius, no T equation and no W force equation.

## 6. The plus mask has Y<1 throughout 4<=R^2<=5

Now assume the unique V mask, the actual physical plus point, and the wider closed radius bound R^2<=5. We prove

    Y<1.                                           (19)

Suppose Y>=1. By (18),

    1<=Y<X<=2,
    r=Y/X in [1/2,1).

The original geometry (7) and a<1,b>0 give

    rho=a-(L/K)*(b+tau)<1-(L/K)*tau.

Together with the unique physical torque (9), this implies

    tau<K*r/(L+K*r),
    s>s0:=L/(L+K*r).                                (20)

Put

    B=1+K, v=L+K*r.

The plus-point deficit as a function of s is

    D(s)=2X*(s-L)+2Y*B-(s-L)^2-B^2.

It increases strictly with s throughout the relevant interval, because

    D'(s)=2*(X-s+L)>0.

It suffices to show D(s0)>0.

If v<=1, then 0<=s0-L<1. Both terms in

    D(s0)=(s0-L)*(2X-s0+L)+B*(2Y-B)

are nonnegative, the second strictly positive because B<2<=2Y.

It remains to consider v>1. Set

    delta=L-s0=L*(v-1)/v in (0,1).

Then

    D(s0)=2X*[r*B-delta]-B^2-delta^2.               (21)

Here delta<K*r, so r*B-delta>r>0. At fixed r,K,L, expression (21) increases with X. The smallest allowed comparison value is

    X0=max(2/sqrt(1+r^2),1/r).                      (22)

The two branches meet at r=1/sqrt(3).

### 6.1. The complete low-r branch

For 1/2<=r<=1/sqrt(3), use X0=1/r, Y0=1. Then X0>=sqrt(3)>5/3, and (21) becomes

    D0=L^2-2X0*delta-delta^2.

The full interval satisfies

    2K<2X0*(1-L)+L.                                (23)

Indeed the right side is at least (10-7L)/3>0, and its squared excess over (2K)^2 is

    [85L^2-140L+64]/9
      =[85*(L-14/17)^2+108/17]/9>0.

Using v=L+K/X0, equation (23) gives 2X0*(v-1)<L, hence

    delta<L^2/(2X0+L).

Since delta<L, it follows that

    delta*(2X0+delta)<L^2.

Thus D0>0 on this whole branch, including both comparison endpoints.

### 6.2. The complete high-r branch

For 1/sqrt(3)<=r<1, put X0=2/sqrt(1+r^2). On the interval where v>1, differentiation gives

    delta'=L*K/v^2<=1/(4r),

by (L+K*r)^2>=4LK*r. Write F(r) for (21) evaluated at this X0. Direct differentiation gives

    F'(r)/2
      =X0/(1+r^2)*(B+r*delta)
           -(X0+delta)*delta'
      >X0/(1+r^2)-(X0+1)/(4r)>0.                  (24)

For the final sign, throughout this whole interval,

    4r/(1+r^2)>=sqrt(3)
          >1+1/sqrt(2)>=1+1/X0.

The middle strict inequality follows by squaring positive quantities:
(1+1/sqrt(2))^2=3/2+sqrt(2)<3.

The set v>1 is an interval because v=L+Kr increases in r. If it already contains the left endpoint 1/sqrt(3), Section 6.1 supplies a strictly positive initial value. If it begins later, its entrance v=1 has the strictly positive direct value from the previous case. Equation (24) then preserves strict positivity throughout the entire remaining interval. No entrance or endpoint is omitted.

This proves D(s0)>0 in all cases. Since the actual s>s0, its actual plus-point deficit is strictly positive, contradicting its physical circle contact. Equation (19) follows.

This is a continuous full-domain exclusion. No actual or sampled pose is used. The comparison parameters at r=1/2, r=1/sqrt(3), v=1 and R^2=5 are all retained.

## 7. Useful exact surviving equations and limits

The complete original unique-plus remainder is now

    X>sqrt(3), 1/2<Y<1,
    X^2+Y^2=R^2,

    0<tau<K-b, s=1-tau,
    rho=1-(Y/X)*s=(d-L*tau)/K,

    z=K*(X-s)+L*(Y-1)>=1/2,

    2X*(s-L)+2Y*(1+K)
       =(s-L)^2+(1+K)^2.                           (25)

The unique-minus remainder retains X>Y>1/2 and

    z<=1/2,

    2X*(s+K-L)+2Y*(1+K+L)
       =(s+K-L)^2+(1+K+L)^2.                       (26)

For that minus point, A=s+K-L is in (0,2) and X>sqrt(2). If Y>=(1+K+L)/2, both terms in its circle deficit are nonnegative and the horizontal one strictly positive. Hence

    Y<(1+K+L)/2< (1+sqrt(2))/2,
    X^2>(13-2sqrt(2))/4>5/2.                        (27)

No sign z>=0 is asserted in (26) when Y<1.

The radial V mask Y=1/2 keeps its full original weight inequality (10). It is not absorbed into (25) by setting a unique-circle force ratio at that physical tie.

In every case, (11) is the actual original terminal port. If T is boundary then its actual diameter gives |S|>=R-sqrt(2). If a complete loaded boundary path is present, its genuine endpoint torque and properness give the further original angular information. Those statements must be joined with their actual full premises by the final caller.

The present proof does not yet exclude the remaining plus, minus or radial domains. It changes no original row flag or coarse gate.

## 8. Exact direct inputs

| Complete source | SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original support conventions, actual side-interior/singleton distinction, full force and torque, every physical circle corner and full original mean |
| D02_ENTIRE_INCOMING_HUB_AXIS_AND_SHARED_TERMINAL_EXCLUSION.md | 0b0e8b90ff7535e6e80f429e10ff7535190c2a74220022d1a9ad3676a8595c7f | Literal original sole-UT singleton interface only |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Optional original U=2,V=1,W=0,T=3, unchanged graph/load and true-degree mapping |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same retained nine-unit R>2 entry only; every local lemma states its own radius domain |

All new support, mask and continuous scalar steps are printed above. No old feature-specific port bound is transferred. Every original circle coefficient, force, normal, actual mean and true degree remains. No Lean compilation, CI, numerical pose search, computational pose certificate, remote write or ledger edit is used.

