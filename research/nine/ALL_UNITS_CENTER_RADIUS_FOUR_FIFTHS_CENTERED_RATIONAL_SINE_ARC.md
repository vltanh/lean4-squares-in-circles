# A wider universal centered arc with half-angle sine thirteen fortieths

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed self-contained hand theorem, frozen for separate full independent review.** This strengthens the earlier radius-43/40 centered 36-degree theorem. It does not supply a pocket route, a whole original-family exclusion or any ledger credit.

## 1. Exact statement

Put

    Q=1105/256, rho=43/40,
    alpha=arcsin(13/40) in (0,pi/2).

Let K be any actual closed unit square contained in the origin-centered disk D_sqrt(Q). Let c be its actual center and r=|c|. If

    r>=4/5,

then the entire closed arc

    {rho*(cos(theta_c+delta),sin(theta_c+delta)):
                           -alpha<=delta<=alpha}

lies in the open interior of K. Here theta_c is the actual center direction.

The full arc has exact angular length 2*arcsin(13/40), approximately 37.93 degrees. The approximation has no role in the proof. In particular its length is strictly greater than 36 degrees: sin(pi/10)=(sqrt(5)-1)/4<13/40 follows from sqrt(5)<23/10, whose squared reserve is 29/100.

Every unit at distance at least 3/10 from O satisfies the center hypothesis. Two distinct interior-disjoint units satisfying it therefore have minor center-angle separation strictly greater than 2*alpha. All thresholds and the complete closed arc are included.

No lower radius, physical circle contact, positive force, degree, normal, contact application or shared-side mean is assumed.

## 2. Actual own coordinates and exact constants

Choose signs and order of K's actual own orthonormal axes so that

    c=r(C,S), C>=S>=0, C^2+S^2=1.

Write C=cos(theta), S=sin(theta), with 0<=theta<=pi/4. The actual farthest corner of K gives the containment inequality

    r^2+r(C+S)+1/2<=Q.                              (1)

For an actual point of the displayed closed arc, its two own-coordinate displacements from c are

    (rho*cos(delta)-r)*C-rho*sin(delta)*S,
    (rho*cos(delta)-r)*S+rho*sin(delta)*C.            (2)

It suffices to bound both absolute values strictly below 1/2.

Set

    A=rho*cos(alpha)=43*sqrt(1431)/1600,
    B=rho*sin(alpha)=559/1600,
    A0=8133/8000.

The exact squared reserve is

    A^2-A0^2=1143/32000000>0.                        (3)

Thus A>A0>4/5. Both A and A0 are positive. Since alpha is strictly acute,

    A+B>rho, rho-A<B.                               (4)

These inequalities follow from cos(alpha)+sin(alpha)>1. For every delta in the entire closed arc, including both endpoints,

    A<=rho*cos(delta)<=rho,
    |rho*sin(delta)|<=B.                            (5)

The proof below controls these complete ranges, not just the two endpoint points.

## 3. All low and middle center radii

Suppose first 4/5<=r<=A. By (5),

    0<=rho*cos(delta)-r<=rho-4/5=11/40.

Cauchy's inequality applied to either coordinate in (2) gives

    squared displacement <=(11/40)^2+B^2<1/4,

with the exact positive reserve

    1/4-(11/40)^2-B^2=133919/2560000.                (6)

Now suppose A<=r<=A+B. Over the interval in (5), both endpoint distances from r are at most B: r-A<=B, and rho-r<=rho-A<B. If r>rho, the first endpoint distance dominates r-rho as well. Therefore

    |rho*cos(delta)-r|<=B.

The squared absolute value of either coordinate in (2) is at most 2B^2, which is strictly below 1/4 by

    1/4-2B^2=7519/1280000>0.                        (7)

Both ranges retain their closed center endpoints, both own-axis endpoints theta=0,pi/4, and every point of the closed angular arc.

## 4. The high-center contradiction reduces to one exact polynomial

Suppose r>=A+B. By (4), r>rho. The two absolute coordinate displacements in (2) are at most

    (r-A)*C+B*S, (r-A)*S+B*C.

The first is at least the second because their difference is

    (C-S)*(r-A-B)>=0.

If the first were at least 1/2, then C>0 and (3) would give

    r>=A+(1/2-B*S)/C
      >A0+(1/2-B*S)/C=:r0.                          (8)

Here r0>0 because B<1/2 and S<=1. For fixed C,S the left side of (1) is strictly increasing in r>=0. It will therefore suffice to prove

    r0^2+r0(C+S)+1/2>Q                              (9)

on the entire actual orientation interval.

Use the exact half-angle parameter

    t=tan(theta/2), 0<=t<=sqrt(2)-1<5/12.

The comparison sqrt(2)<17/12 has squared reserve 1/144. We also have

    t^2<=3-2sqrt(2)<11/64,                          (10)

because sqrt(2)>181/128, with squared reserve 7/16384.

The half-angle formulas give

    C=(1-t^2)/(1+t^2), S=2t/(1+t^2),
    r0=(12133-5590*t-4133*t^2)/(8000*(1-t^2)).

Direct exact expansion gives the polynomial identity

    64000000*(1-t^2)^2*(1+t^2)
                  *[r0^2+r0(C+S)+1/2-Q]=P(t),

    P(t)=23689+13761060*t+5784411*t^2
              -260256000*t^3+444920411*t^4
              +67614940*t^5-260232311*t^6.           (11)

For a direct denominator check, let

    N=12133-5590*t-4133*t^2,
    D=1-t^2, U=1+t^2, V=1+2*t-t^2.

Then P is exactly

    N^2*U+8000*N*D*V-244250000*D^2*U.

This is a coefficient identity, not a numerical orientation check.

## 5. Entire-interval positivity by two continuous comparisons

Using (10) to absorb the last negative term in (11) gives

    P(t)>=23689+t*[q(t)+67614940*t^4],               (12)

where

    q(t)=13761060+5784411*t-260256000*t^2
                               +(25612350883/64)*t^3. (13)

The inequality at t=0 is sufficient as written; for positive t its absorbed-term comparison is strict. We prove that the bracket in (12) is positive throughout the larger closed interval [0,5/12].

On [0,3/8], q' is an upward quadratic and

    q'(0)=5784411>0,
    q'(3/8)=-84280010703/4096<0.

An upward quadratic with these signs has exactly one root in (0,3/8), and its other root is larger than 3/8. Thus q first increases and then decreases on this interval. Its minimum is at an endpoint. Both endpoints are strictly positive:

    q(0)=13761060,
    q(3/8)=14275082289/32768>0.                      (14)

This proves the bracket positive on the first entire interval.

On [3/8,5/12], the same derivative is a convex quadratic. Its values at both endpoints are negative:

    q'(3/8)=-84280010703/4096,
    q'(5/12)=-8176877333/3072.

A convex function is at most the linear interpolation of its endpoint values. Hence q'<0 on this whole interval, and q(t)>=q(5/12). Also t^4>=(3/8)^4. The exact endpoint values therefore give

    q(t)+67614940*t^4
      >=q(5/12)+67614940*(3/8)^4
       =140911340555/110592>0,                      (15)

where q(5/12)=-6962533225/110592.

Equations (12)--(15) prove P(t)>=23689>0 on the entire actual orientation domain. The prefactor in (11) is positive because t<1. Thus (9) follows. By (8), actual containment (1) is contradicted whenever either coordinate displacement could reach 1/2.

This completes the high-center range, including r=A+B and both own-axis orientation endpoints. With Section 3 it proves the stated entire closed arc theorem for every r>=4/5.

## 6. Whole-square clearance and strict separation corollaries

Suppose dist(O,K)=d0>=3/10. Let p be its actual nearest point and n=p/d0. The nearest-point inequality for a convex square gives

    n.z>=d0 for every z in K.

The square's actual support halfwidth in any unit direction is at least 1/2. Consequently

    |c|>=n.c>=d0+1/2>=4/5.

The proved closed center threshold applies. This geometric support estimate neither selects nor modifies any physical stress normal or application.

For two distinct interior-disjoint squares satisfying the theorem, their closed centered arcs lie in their respective open interiors. A minor center gap at most 2*alpha would make those arcs intersect. At equality their common endpoint still lies in both open interiors. Hence the minor center gap is strictly greater than 2*alpha.

No assertion about connectedness of a square's entire circle intersection is required.

## 7. Scope and verification

The theorem is self-contained. The earlier centered 36-degree source motivated this stronger radius/angle choice but is not an operative input. All own-coordinate formulas, complete center ranges, half-angle denominators, continuous polynomial comparisons and exact reserves are printed above.

At R>=2, every physical boundary unit has center radius at least R-1/sqrt(2)>4/5, so it meets the hypothesis independently of its degree, physical corner mask or individual corner weights. A whole extra with proved clearance greater than 3/10 meets the clearance corollary. These are only premise checks: routing these arcs into a particular pocket and bounding its available angular interval remain independent physical obligations.

No original family is closed by this arc theorem. No force, square, contact, mean, normal or circle mask has been changed. There is no pose sample, numerical optimizer, finite geometric exclusion certificate, Lean compilation, CI, remote mutation or shared-ledger change.
