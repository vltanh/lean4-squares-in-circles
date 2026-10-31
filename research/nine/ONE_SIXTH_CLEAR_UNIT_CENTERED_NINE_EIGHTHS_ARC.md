# A unit with one-sixth clearance has a centered forty-degree arc

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free hand theorem, submitted for independent review.** This strengthens the closed clearance threshold to1/6 and keeps every actual orientation and the equality endpoint. The concavity method comes from pentagon's complete nine-fiftieths-clearance proof; the new threshold, weak nearest-corner endpoint and exact remaining reserve are proved here. No older frozen source is changed.

## 1. Uniform statements

Let E be an actual closed unit square with center c and

    dist(0,E)>=1/6, |c|<=5/6.

Put r0=9/8 and alpha=atan(3/8). Then its entire closed radius-r0 arc centered at arg(c), with halfwidth alpha, lies in its open interior.

Consequently every actual unit in the unchanged disk D_(sqrt(Q)), Q=1105/256, with dist(0,E)>=1/6 contains the entire closed radius-9/8 arc of halfwidth pi/9 centered at arg(c) in its open interior. Two interior-disjoint such units have minor center separation strictly greater than2pi/9.

The near-center statement has no containing-radius premise. Neither statement has a force, degree, physical boundary-contact, normal-owner, graph or application premise. The conclusion alone assigns no square to a pocket.

## 2. Every nearest-point case, including the weak corner endpoint

Choose signs and order of the actual own axes so

    c=(a,b), a>=b>=0,
    E=[a-1/2,a+1/2] x [b-1/2,b+1/2].

If b>=1/2, put A=a-1/2 and B=b-1/2. They are nonnegative and the exact nearest-point formula gives

    A^2+B^2>=1/36,
    A+B>=sqrt(A^2+B^2)>=1/6.

Hence

    |c|^2=1/2+A+B+A^2+B^2>=25/36.

The assumed opposite weak bound forces equality in every step. In particular A+B=1/6, A^2+B^2=1/36 and AB=0. Because A>=B, necessarily

    a=2/3, b=1/2, |c|=5/6.

This is a retained actual endpoint, not an excluded corner case.

If b<1/2, the exact nearest-side formula gives a-1/2>=1/6, so a>=2/3. Therefore in every case

    a>=2/3, b<=1/2,
    c=r(cos(phi),sin(phi)),
    2/3<=r<=5/6, 0<=phi<=pi/4.                    (1)

All forthcoming estimates include the weak corner endpoint from above.

## 3. Both complete first-coordinate bounds

The elementary angle values are

    cos(alpha)=8/sqrt(73), sin(alpha)=3/sqrt(73),
    0<alpha<pi/4,
    r0*cos(alpha)=9/sqrt(73)>5/6.                 (2)

The last comparison follows from54^2-25*73=1091>0.

For every actual angular displacement t in[-alpha,alpha], the radius-r0 point has own coordinates

    (r0*cos(phi+t),r0*sin(phi+t)).

Its positive first-coordinate deviation is at most

    r0-a<=9/8-2/3=11/24<1/2.                    (3)

For the negative deviation, |phi+t|<=pi/4+alpha<pi/2. Thus

    r0*cos(phi+t)>=45/(8sqrt(146))>45/104,

and

    a-r0*cos(phi+t)<5/6-45/104=125/312<1/2.       (4)

The strict comparisons are uniform, including every closed angle and center-radius endpoint.

## 4. One complete concavity bound for the second coordinate

Sine is increasing throughout[-alpha,pi/4+alpha]. Since a=r*cos(phi)>=2/3, the positive second-coordinate deviation is at most

    F(phi)=r0*sin(phi+alpha)-(2/3)*tan(phi).       (5)

Over the entire comparison interval0<=phi<=pi/4,

    F''(phi)
      =-r0*sin(phi+alpha)-(4/3)*sec(phi)^2*tan(phi)
      <=-r0*sin(alpha)<-3/8.                    (6)

The final strict inequality is27/(8sqrt(73))>3/8, equivalent after positive squaring to81>73.

At the single comparison angle alpha, the exact double-angle values sin(2alpha)=48/73, cos(2alpha)=55/73 and sec(alpha)^2=73/64 give

    F(alpha)=143/292,
    F'(alpha)=611/7008.                          (7)

Global Taylor concavity and completing the square therefore give, for every actual phi,

    F(phi)
      <=F(alpha)+F'(alpha)*(phi-alpha)
                    -(3/16)*(phi-alpha)^2
      <=F(alpha)+(4/3)*F'(alpha)^2
       =1/2-5111/36834048<1/2.                  (8)

The strict reserve is positive at the new closed clearance threshold. Equation(8) is a whole-interval bound, not an orientation sample.

For the negative second-coordinate deviation, use (2) and r<=5/6:

    b-r0*sin(phi-alpha)
      =(r-r0*cos(alpha))*sin(phi)
            +r0*sin(alpha)*cos(phi)
      <=r0*sin(alpha)=27/(8sqrt(73))<27/64<1/2.   (9)

Every point in the entire closed centered arc consequently has both own-coordinate deviations strictly between-1/2 and1/2. It belongs to the open interior of the unchanged actual unit. This proves the complete near-center statement, including a=2/3,b=1/2,r=5/6.

## 5. All actual centers and strict separation

The exact accepted d575 source in Section6 proves that every contained unit with actual center radius at least3/4 contains its closed centered radius-9/8 arc of halfwidth pi/9 in its open interior. It also proves cos(pi/9)>15/16.

On the positive acute branch,

    tan(pi/9)<sqrt(31)/15<3/8=tan(alpha),

where9/64-31/225=41/14400>0. Thus alpha>pi/9.

For a unit with clearance at least1/6, use d575 when r>=3/4. When r<3/4, the new near-center theorem applies since r<=5/6. The overlap and both radius thresholds are retained, so all centers are covered.

If two such interior-disjoint units had minor center gap at most2pi/9, the midpoint of that angular interval would lie in both closed centered arcs and hence in both open interiors. This is impossible. The separation is strictly greater than2pi/9, including the alleged equality case.

No connectedness of a unit's entire circle intersection is presumed. The proof only uses one complete actual centered arc in each unit.

## 6. Exact operative input and provenance

| Complete operative source | SHA256 | Exact use |
| --- | --- | --- |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | All-center regime r>=3/4 and the strict elementary twenty-degree comparison |

The new near-center proof is fully supplied here. Its global concavity method was introduced in pentagon's NINE_FIFTIETHS_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md, SHA256 e804bfab8299a167b57bb5c41c5e4b545e69a70dbe09b5551a3d7c742bf7bf6f, independently reviewed by root at its own complete scope. That stricter-clearance theorem is acknowledged as provenance, not used to infer a weaker premise by implication. The new1/6 threshold and equality case are proved in Sections2--4.

The source changes no original fine flag, coarse flag or proof input. No force, application, actual square, physical mask or selected normal is modified. No Lean compilation, CI, workflow, numerical pose sample, optimization certificate, remote write or shared-ledger mutation is used.

