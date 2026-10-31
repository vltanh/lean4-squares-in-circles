# A unit with nine-fiftieths clearance has a centered forty-degree arc

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed force-free hand theorem, submitted for independent review.** Every actual orientation and every closed clearance endpoint is included. The theorem has no force, circle-contact, normal-owner, degree, physical-mask, graph or application premise.

## 1. Statements and unchanged physical coordinates

Let E be an actual closed unit square, with center c, such that

    dist(0,E)>=9/50, |c|<=5/6.

Put

    r0=9/8, alpha=atan(3/8).

Then the entire closed radius-r0 arc centered at arg(c), with halfwidth alpha, lies in the open interior of E.

As a consequence, if E is any actual unit contained in the unchanged disk of squared radius Q=1105/256 and dist(0,E)>=9/50, its entire closed radius-9/8 arc of halfwidth pi/9 centered at arg(c) lies in its open interior. Thus two such interior-disjoint units have minor center-angle separation strictly greater than2pi/9.

The near-center statement has no containing-radius assumption. The all-center consequence uses the separately accepted three-quarter-center theorem only on its literal center-radius domain.

## 2. Complete actual frame cover near the center

Choose signs and order of the actual own axes so that the unchanged center coordinates are

    (a,b), a>=b>=0,
    E=[a-1/2,a+1/2] x [b-1/2,b+1/2].

Suppose first b>=1/2. Put A=a-1/2 and B=b-1/2. The exact nearest-point formula gives A,B>=0 and

    A^2+B^2>=81/2500,
    A+B>=sqrt(A^2+B^2)>=9/50.

Consequently

    |c|^2=1/2+A+B+A^2+B^2
          >=1781/2500>25/36,

with strict rational reserve101/5625. This contradicts |c|<=5/6.

Hence b<1/2. The same exact nearest-point formula now gives a>=17/25. Write

    r=|c|, a=r*cos(phi), b=r*sin(phi),
    17/25<=r<=5/6, 0<=phi<=pi/4.                    (1)

This covers nearest-side, nearest-vertex and weak-clearance possibilities. No low-center orientation was discarded.

The elementary values are

    cos(alpha)=8/sqrt(73), sin(alpha)=3/sqrt(73),
    0<alpha<pi/4,
    r0*cos(alpha)=9/sqrt(73)>5/6.                   (2)

The last squared reserve is54^2-25*73=1091>0.

## 3. Entire first-coordinate interval

For any actual circle angle displacement t in[-alpha,alpha], the point has own coordinates

    (r0*cos(phi+t), r0*sin(phi+t)).

Its positive first-coordinate deviation is at most

    r0-a<=9/8-17/25=89/200<1/2.                    (3)

For the negative deviation, |phi+t|<=pi/4+alpha<pi/2. Hence

    r0*cos(phi+t)
       >=r0*cos(pi/4+alpha)
        =45/(8*sqrt(146))>45/104,

using sqrt(146)<13. Therefore

    a-r0*cos(phi+t)<5/6-45/104=125/312<1/2.         (4)

Both closed displacement endpoints and both actual frame endpoints are retained.

## 4. One global concavity bound for the second coordinate

Sine is increasing on the complete angle interval[-alpha,pi/4+alpha], which lies in(-pi/2,pi/2). Since a=r*cos(phi)>=17/25, the positive second-coordinate deviation is bounded by

    F(phi)=r0*sin(phi+alpha)-(17/25)*tan(phi).       (5)

On the full interval0<=phi<=pi/4,

    F''(phi)
      =-r0*sin(phi+alpha)
         -(34/25)*sec(phi)^2*tan(phi)
      <=-r0*sin(alpha)<-3/8.                        (6)

For the last strict comparison, r0*sin(alpha)=27/(8*sqrt(73))>3/8 because81>73.

At the single comparison angle phi=alpha, exact evaluation gives

    F(alpha)=7077/14600,
    F'(alpha)=8407/116800.                          (7)

Indeed sin(2alpha)=48/73, cos(2alpha)=55/73 and sec(alpha)^2=73/64. Global Taylor concavity and a completed square therefore give, for every actual phi,

    F(phi)
      <=F(alpha)+F'(alpha)*(phi-alpha)
                    -(3/16)*(phi-alpha)^2
      <=F(alpha)+(4/3)*F'(alpha)^2
       =1/2-85600751/10231680000<1/2.               (8)

This is a continuous whole-angle bound; no sampled orientation or numerical extremum is used.

For the negative deviation, (2) gives

    b-r0*sin(phi-alpha)
       =(r-r0*cos(alpha))*sin(phi)
            +r0*sin(alpha)*cos(phi)
       <=r0*sin(alpha)
        =27/(8*sqrt(73))<27/64<1/2.                (9)

Equations(3)--(9) prove that both own-coordinate deviations of every point in the closed centered arc are strictly between-1/2 and1/2. The entire arc is therefore in the actual open unit.

## 5. All centers, the exact twenty-degree comparison and pair separation

The complete current source

    ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md
    d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9

proves that every unit in D_(sqrt(Q)) with center radius at least3/4 contains the closed centered radius-9/8 arc of halfwidth pi/9 in its open interior. Its full orientation domain and strict closed-arc conclusion are retained.

That source also proves cos(pi/9)>15/16. On the positive first-quadrant branch this implies

    tan(pi/9)<sqrt(31)/15<3/8=tan(alpha),

because9/64-31/225=41/14400>0. Hence alpha>pi/9.

Now take any contained unit with clearance at least9/50. If its center radius is at least3/4, apply the accepted all-center theorem at exactly its stated threshold. If its center radius is below3/4, then it is certainly at most5/6 and Sections1--4 apply. Thus every actual center radius is covered, including the two overlapping threshold endpoints.

If two such units had minor center separation at most2pi/9, the midpoint of that minor angular interval would belong to both of their closed centered arcs and hence to both open interiors. This is impossible. Their separation is strictly greater than2pi/9.

The conclusion concerns the actual center directions and actual open interiors. It does not assert connectedness of an entire square-circle intersection or assign any square to a pocket. Those routing premises must be proved separately by a caller.

## 6. Exact dependency and scope

The only operative imported result is the full d575e663 source in Section5, for its all-center regime and its elementary twenty-degree comparison. The new near-center theorem, including the complete actual frame cover, is proved above.

This strengthens the earlier one-fifth-clearance near-center method at a smaller actual clearance, with a separately proved halfwidth and strict reserve. No old frozen manuscript or old review is changed.

There is no degree, force, physical circle mask, shared mean, graph or nine-square-completion hypothesis in the force-free theorem. No original fine or coarse gate is closed by the arc result alone.

No Lean compilation, CI, pose sample, numerical exclusion certificate, changed original square, moved application, remote write or shared-ledger mutation is used.

