# Independent review: the uniform centered 36-degree arc on radius 43/40

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

**Verdict: complete independent PASS, without repair.** Every actual contained unit with center radius at least 4/5 has the entire stated closed centered 36-degree arc inside its open interior. The closed-clearance corollary and strict separation conclusion also hold at every stated endpoint.

## 1. Exact source and independence

Reviewed complete source:

    ALL_UNITS_CENTER_RADIUS_FOUR_FIFTHS_CENTERED_THIRTY_SIX_DEGREE_ARC.md

SHA256:

    cd72561bd5221a47c8c47aa34d5913b988e83d895725d64529a3428181967ffc

Current size: 8,915 bytes.

I read the entire source and independently rederived the actual own-frame formulas, all three center-radius regimes, the exact degree-six identity, its full-interval positive reduction, and both corollaries.

The new proof is root-authored. I did not contribute its new radius, center threshold, polynomial identity or positive cubic argument. I authored earlier centered-arc results, but none is an operative mathematical premise of this self-contained proof. This review therefore does not treat a review of an older theorem as approval of the new source.

There are no imported mathematical source pins requiring a proof transfer. The optional physical applications in Section 6 are only direct premise checks; their actual pocket geometry must remain independently established.

## 2. The complete actual arc is represented correctly

Use the actual own orthonormal axes, with signs and order chosen so the center is

    c=r(C,S0), C>=S0>=0, C^2+S0^2=1.

This covers the entire orientation interval 0<=theta<=pi/4, including both endpoints. The farthest actual corner gives exactly

    r^2+r(C+S0)+1/2<=1105/256.

For every deviation delta with |delta|<=pi/10, the displayed pair of own-coordinate displacements is the actual displacement of the radius-43/40 point from c. Bounding both absolute values strictly below 1/2 is therefore exactly open membership in the unchanged unit, not membership in a comparison disk or a changed frame.

With A=rho*cos(alpha), B=rho*sin(alpha), the proof uses the uniform inequalities

    A<=A_delta<=rho,
    0<=B_delta<=B

for every point of the closed arc. It does not infer an interior-arc statement by checking only its two angular endpoints.

## 3. All radical and coefficient comparisons are exact

The positive acute half-angle branches give

    cos(alpha)^2=(5+sqrt(5))/8,
    sin(alpha)=(sqrt(5)-1)/4.

The bound sqrt(5)>20/9 has squared reserve 5/81. It yields

    cos(alpha)^2>65/72>(19/20)^2,

with the last reserve 1/3600. Positive square roots give cos(alpha)>19/20.

Thus

    A>817/800=49/48+1/2400.

For the sine bound, sqrt(5)<47/21 has squared reserve 4/441. It gives

    B<559/1680<1/3,

with final reserve 1/1680.

Because alpha lies strictly between zero and pi/2, cos(alpha)+sin(alpha)>1. Both A+B>rho and rho-A<B follow in the claimed directions. No numerical angle approximation enters.

## 4. The first two complete center-radius intervals are valid

For 4/5<=r<=A, the radial coefficient A_delta-r is nonnegative and at most rho-r<=11/40. Cauchy's inequality bounds either actual squared coordinate deviation by

    (11/40)^2+B^2
      <2689/14400<1/4.

The strict final reserve is 911/14400. This includes r=4/5, r=A, theta=0, theta=pi/4 and both closed arc endpoints.

For A<=r<=A+B, the greatest possible radial-coefficient magnitude over A_delta in [A,rho] is bounded by

    max(r-A,rho-r)<=B.

If r>rho, the term r-A already dominates r-rho, so the same displayed maximum remains a valid bound; there is no omitted sign case. If r<=rho, the two ends of the interval give precisely the two terms shown.

Cauchy's inequality then gives

    squared deviation <=2B^2<2/9<1/4,

with reserve 1/36. The strict bound is retained at both endpoints of this full middle interval.

## 5. The high-center reduction retains both coordinates and every angle

When r>=A+B, the established A+B>rho implies r>rho. Consequently

    |A_delta-r|<=r-A,
    B_delta<=B,
    r-A>=B.

The two absolute coordinate deviations are bounded respectively by

    (r-A)C+B*S0,
    (r-A)S0+B*C.

Their difference is (C-S0)(r-A-B)>=0. Thus controlling the first expression controls both, including C=S0 and r=A+B.

Suppose this larger expression were at least 1/2. Since C>=1/sqrt(2)>0,

    r>=A+(1/2-B*S0)/C
      >49/48+(1/2-S0/3)/C=r0.

The strict inequality follows from A>49/48 even when S0=0; when S0>0 the strict sine comparison contributes in the same direction. The numerator 1/2-S0/3 remains positive on the full actual domain, so r0>0.

For fixed C,S0, the farthest-corner expression is strictly increasing for nonnegative r. Therefore it suffices to prove that its value at r0 exceeds Q. This is a valid global contradiction reduction, not an optimization over selected orientations.

## 6. Exact identity and whole-interval positivity

The exact parameter t=tan(theta/2) ranges over

    0<=t<=sqrt(2)-1<5/12<1/2.

The comparison sqrt(2)<17/12 has squared reserve 1/144. The half-angle formulas give

    C=(1-t^2)/(1+t^2),
    S0=2t/(1+t^2),
    r0=(73-32t-25t^2)/(48(1-t^2)).

I independently expanded the identity

    288(1-t^2)^2(1+t^2)
       [r0^2+r0(C+S0)+1/2-Q]
      =5+100t+27t^2-1176t^3
          +1971t^4+308t^5-1171t^6.

All seven coefficient differences are exactly zero. One direct way to check the clearing of denominators is to write N=73-32t-25t^2, D=1-t^2, U=1+t^2 and V=1+2t-t^2. Eight times the displayed polynomial is exactly

    N^2*U+48*N*D*V-8793*D^2*U.

There is no residual rational denominator or missing sign.

The displayed grouping is also exact. With

    g(t)=3-37t^2+50t^3,

the difference between P(t) and 5+27t^2+32t*g(t) is

    4t+8t^3+371t^4+308t^5-1171t^6.

For 0<=t<=1/2, the last term is at least -(1171/4)t^4. Hence that difference is at least

    4t+8t^3+(313/4)t^4+308t^5>=0.

On the entire larger interval [0,5/12],

    g'(t)=t(150t-74)<=0.

The upper endpoint gives 150(5/12)-74=-23/2, and the zero derivative at t=0 is harmless. Thus g(t)>=g(5/12)=167/864>0.

It follows that P(t)>=5>0 throughout the entire original orientation domain. The prefactor 288(1-t^2)^2(1+t^2) is strictly positive there. Therefore the farthest-corner value at r0 is strictly greater than Q, contradicting actual containment.

This proves the high-center coordinate bound strictly, including the axis and diagonal-center orientations, the center-regime join and every point of the closed angular interval. Together with Section 4, the three ranges cover all r>=4/5.

## 7. Clearance and strict separation are literal corollaries

For a whole square at distance d0>=3/10 from O, its actual nearest point p has positive norm. The convex nearest-point inequality gives the geometric support n.z>=d0 for n=p/d0.

The square's actual support halfwidth in any unit direction is at least 1/2, so

    |c|>=n.c>=d0+1/2>=4/5.

This invokes the already proved closed center threshold. The geometric support is used only for an estimate; it does not change a stress normal or an application.

For two distinct interior-disjoint squares satisfying either entry, the two entire closed arcs lie in their respective open interiors. A minor center gap at most 36 degrees makes the arcs intersect. At equality, their common endpoint still belongs to both open interiors. Thus separation is strictly greater than 36 degrees.

No connectedness statement about either square's entire circle intersection is needed for either corollary.

## 8. Exact arithmetic record

The audit recomputed every displayed fixed reserve and both polynomial identities:

| Expression | Exact result |
| --- | ---: |
| 5-(20/9)^2 | 5/81 |
| 65/72-(19/20)^2 | 1/3600 |
| 817/800-49/48 | 1/2400 |
| (47/21)^2-5 | 4/441 |
| 1/3-559/1680 | 1/1680 |
| 121/1600+1/9 | 2689/14400 |
| 1/4-2689/14400 | 911/14400 |
| 1/4-2/9 | 1/36 |
| (17/12)^2-2 | 1/144 |
| 371-1171/4 | 313/4 |
| g(5/12) | 167/864 |
| 150(5/12)-74 | -23/2 |
| All seven coefficients of the identity remainder | 0 |
| Grouping remainder coefficients, in increasing powers of t | 0,4,0,8,371,308,-1171 |

These exact calculations corroborate a printed continuous proof. They are not a numerical pose search, interval subdivision, root-isolation certificate or finite orientation test.

## 9. Optional physical applications and precise limits

A physical boundary unit at R>=2 has center norm at least R-1/sqrt(2)>4/5, independently of its physical corner mask or individual corner weights. An actual extra in the completely proved force-free channel pocket has clearance greater than 3/10 and therefore meets the new clearance corollary. These are direct checks of the theorem's genuine premises.

The source correctly supplies no pocket routing, no prescribed gap width and no transmitter proximity conclusion by itself. A smaller circle does not automatically disconnect a free middle interval from a lateral interval when a transmitter's top lies below that circle. Such a further geometric argument remains a separate obligation.

**Final disposition:** accept the exact cd72561b theorem and both corollaries, with zero new original fine or coarse credit. No source repair, force deletion, changed mean, normal reselection, physical movement, Lean compilation, CI, remote write or shared-ledger mutation was performed.

