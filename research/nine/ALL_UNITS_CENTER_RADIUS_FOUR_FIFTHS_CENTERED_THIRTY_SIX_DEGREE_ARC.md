# Every contained unit with center radius at least four fifths has a closed centered 36-degree arc on radius 43/40

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free geometric theorem, submitted for independent full review.** The smaller common circle is intended for physical channel and near-origin arguments. The proof treats every square orientation and every point of the entire closed arc. It needs no force, load, contact, graph or containing-radius lower bound.

## 1. Exact theorem

Put

    Q=1105/256, rho=43/40, alpha=pi/10=18 degrees.

Let S be an actual closed unit square contained in the original disk D_(sqrt(Q)) centered at O=0. Suppose its actual center c satisfies

    r=|c|>=4/5.

**Theorem.** Every point of the closed radius-rho arc of halfwidth alpha centered at the direction of c lies in the open interior of S. Thus the entire closed centered arc has width36 degrees, including both endpoints.

**Clearance corollary.** The same conclusion holds whenever the whole actual square has distance at least3/10 from O.

**Separation corollary.** Two distinct interior-disjoint actual squares satisfying either entry have minor center-angle separation strictly greater than36 degrees. Equality is impossible because their closed arcs would share a point in both open interiors.

No assertion is made that this arc is the square's whole circle intersection, that an exterior pocket has a given winding label, or that its actual transmitter is within any particular distance of O.

## 2. Actual own-frame geometry and exact constants

Choose signs and order of the square's two orthonormal own axes so that its actual center coordinates are

    c=(r cos(theta),r sin(theta)), 0<=theta<=pi/4.

Write C=cos(theta), S0=sin(theta). Then C>=S0>=0, C^2+S0^2=1. Its actual farthest-corner containment is exactly

    r^2+r(C+S0)+1/2<=Q.                              (1)

The symbol S0 is a scalar; the physical square remains S. Every point of the proposed arc has angular deviation delta with |delta|<=alpha from the actual center direction. Its two own-coordinate displacements from c are

    (rho cos(delta)-r)C-rho sin(delta)S0,
    (rho cos(delta)-r)S0+rho sin(delta)C.              (2)

It suffices to prove the absolute values of both expressions are strictly less than1/2 for every such delta.

Set

    A=rho cos(alpha), B=rho sin(alpha).

The exact half-angle constants give

    cos(alpha)>19/20,
    A>817/800=49/48+1/2400,
    0<B<1/3.                                        (3)

For completeness, sqrt(5)>20/9 because 5-400/81=5/81>0. Hence

    cos(alpha)^2=(5+sqrt(5))/8>65/72>(19/20)^2,
    65/72-361/400=1/3600>0.

Also sqrt(5)<47/21 because (47/21)^2-5=4/441>0. Since sin(alpha)=(sqrt(5)-1)/4,

    B<43*26/(160*21)=559/1680<1/3.

The last reserve is1/1680. These are exact radical inequalities, not decimal angle approximations.

We will also use

    rho-A<B, A+B>rho.                                (4)

Both follow from cos(alpha)+sin(alpha)>1 on this strict first-quadrant angle; squaring gives 1+sin(2alpha)>1.

For every |delta|<=alpha put A_delta=rho cos(delta) and B_delta=rho|sin(delta)|. Then

    A<=A_delta<=rho, 0<=B_delta<=B.                  (5)

The estimates below use (5) throughout the closed arc, so checking only its endpoints is unnecessary.

## 3. The whole lower and middle center ranges

First suppose 4/5<=r<=A. Then A_delta>=r, and

    |A_delta-r|<=rho-r<=rho-4/5=11/40.

By Cauchy's inequality applied to each expression (2), both absolute coordinate displacements have squared values at most

    (11/40)^2+B^2
       <121/1600+1/9
       =2689/14400<1/4.                             (6)

The final reserve is911/14400>0. This includes the closed center threshold r=4/5, all delta endpoints and both own-axis directions theta=0,pi/4.

Next suppose A<=r<=A+B. By (4)--(5),

    |A_delta-r|<=max(r-A,rho-r)<=B.

Cauchy's inequality now bounds both squared coordinate displacements by

    2B^2<2/9<1/4,                                   (7)

with reserve1/36. Thus the whole arc lies in open S in these two entire ranges.

## 4. A single exact polynomial handles the remaining high centers

Suppose r>=A+B. By (4), r>rho, so (5) gives

    |A_delta-r|<=r-A, B_delta<=B,
    r-A>=B.

Consequently the larger of the two bounds for the absolute values in (2) is

    (r-A)C+B S0.                                    (8)

Indeed subtracting the other bound gives (C-S0)(r-A-B)>=0. It remains to prove (8)<1/2.

Suppose (8)>=1/2. Since C>0, (3) implies

    r>=A+(1/2-B S0)/C
      >49/48+(1/2-S0/3)/C=:r0.                    (9)

The last strict inequality holds also at theta=0 because A>49/48. The quantity r0 is positive: its numerator 1/2-S0/3 is positive on S0<=1/sqrt(2), and 49/48>0.

For fixed C,S0 the left side of (1) increases strictly with r>=0. It is therefore enough to show

    r0^2+r0(C+S0)+1/2>Q                            (10)

throughout 0<=theta<=pi/4.

Use the exact half-angle parameter t=tan(theta/2). Its entire range satisfies

    0<=t<=sqrt(2)-1<5/12<1/2,

where sqrt(2)<17/12 follows from (17/12)^2-2=1/144>0. Then

    C=(1-t^2)/(1+t^2), S0=2t/(1+t^2),
    r0=(73-32t-25t^2)/(48(1-t^2)).                 (11)

Direct multiplication gives the exact identity

    288(1-t^2)^2(1+t^2)
       *[r0^2+r0(C+S0)+1/2-Q]=P(t),               (12)

where

    P(t)=5+100t+27t^2-1176t^3
               +1971t^4+308t^5-1171t^6.           (13)

Here is a short positive proof on the whole continuous range, rather than a root isolation or an orientation table. For 0<=t<=1/2,

    P(t)-[5+27t^2+32t(3-37t^2+50t^3)]
       =4t+8t^3+371t^4+308t^5-1171t^6
       >=4t+8t^3+(313/4)t^4+308t^5>=0.            (14)

The first comparison uses only t^2<=1/4. The cubic

    g(t)=3-37t^2+50t^3

is nonincreasing on [0,5/12], since

    g'(t)=t(150t-74)<=0.

Its exact endpoint value is

    g(5/12)=167/864>0.                              (15)

Thus P(t)>=5>0 for every original half-angle parameter. All factors outside the brackets on the left of (12) are strictly positive. This proves (10). Equations (9)--(10) contradict actual farthest-corner containment (1), proving (8)<1/2.

Sections3--4 prove that both actual own-coordinate displacements in (2) are strictly less than1/2 in absolute value for every delta in the closed interval. The entire closed arc therefore lies in open S, as claimed.

## 5. Clearance and separation at their closed thresholds

Suppose dist(0,S)=d0>=3/10. Let p be the actual nearest point of the closed convex square to O. Then n=p/d0 is a unit direction, and the nearest-point variational inequality gives

    n.z>=d0 for all z in S.

The actual support halfwidth of a unit square in any unit direction is at least1/2: in any orthonormal own frame it is (|n.e_1|+|n.e_2|)/2>=1/2. Hence its center satisfies

    |c|>=n.c>=d0+1/2>=4/5.

The theorem applies, including equality in either threshold. This is a geometric supporting direction used only to estimate the unchanged square, not a replacement stress normal or new contact application.

For two interior-disjoint units satisfying the center or clearance premise, their two closed centered arcs on the same radius-rho circle cannot intersect. Every point of either closed arc lies in its own open square. A minor center gap at most2alpha=36 degrees would force an arc intersection, including a shared endpoint at equality. Thus the center gap is strictly greater than36 degrees.

## 6. Reusable scope and verification boundary

Every actual physical boundary unit in the same-nine window R>=2 satisfies the center hypothesis, since its center has radius at least R-1/sqrt(2)>4/5. Every actual extra in the newly proved force-free upper side-channel pocket satisfies the clearance premise because that pocket has distance greater than3/10 from O. These are immediate premise checks, independent of endpoint degrees or corner weights.

This smaller-circle lemma does not complete any pocket-routing argument. For example, when a transmitter's top lies below rho, a central free interval above it may connect to a lateral interval unless a separate geometric obstruction disconnects them. The existence of this centered arc alone does not prove that an occupied channel has transmitter distance less than1/40.

The proof is self-contained in actual unit-square geometry, the farthest-corner formula, elementary trigonometry, exact polynomial algebra and a whole-interval cubic derivative. The identity (12), the grouping (14) and the listed rational reserves were checked with exact fractions. Those checks corroborate the displayed proof and are not a finite pose exclusion certificate.

No physical square, force, actual normal, application mean, circle mask, individual corner coefficient or original graph flag is changed. No numerical pose search, sampled-angle test, Lean compilation, CI or remote action is used.
