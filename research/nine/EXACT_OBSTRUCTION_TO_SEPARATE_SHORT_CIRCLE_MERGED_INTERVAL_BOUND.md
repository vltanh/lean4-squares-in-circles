# Exact obstruction to a separate endpoint bound for the merged short-circle interval

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: exact counterexample to a proposed intermediate force-free geometric assertion.** This note does not construct an extra packing unit, a positive stress or a nine-unit counterexample. Its purpose is to prevent the false endpoint-only assertion below from entering the proof. The complete side-channel capacity and one-eighth proximity theorems are unaffected.

## 1. The proposed assertion and exact actual channel

Put

    rho=43/40, w=41/40,
    gamma=acos(w/rho)=acos(41/43),
    x_0=sqrt(rho^2-w^2)=sqrt(42)/20.

An attempted endpoint-only strengthening would say that, whenever a<x_0 and the actual channel port height h<=w, the left boundary unit's upper gap-facing rho-circle endpoint satisfies

    alpha_X<7pi/10-gamma.                            (1)

Here is an exact channel violating (1). Let

    a=323/1000, b=677/1000, h=1, v=1/40,
    sigma=1/sqrt(2),
    P=(-a,1),
    u=(sigma,sigma), t=(-sigma,sigma),

    H=[-a,b] times [v,v+1],
    X=P+[-1,0]u+[0,1]t,

    R^2=3+a^2+2a sqrt(2),
    B=sqrt(R^2-(b+1)^2),
    Y=[b,b+1] times [B-1,B].                         (2)

These are actual unit squares, not normal or force substitutions. The two original support applications for the geometric statement are P_X=(-a,1) and P_Y=(b,1).

## 2. Full containment, contact and physical-mask checks

The unique farthest corner of X is P-u+t=(-a-sqrt(2),1), with squared norm R^2. Its squared-norm differences from the other three actual corners are

    R^2-|P+t|^2=1-b sqrt(2)>0,
    R^2-|P-u|^2=1+(1+a)sqrt(2)>0,
    R^2-|P|^2=2+2a sqrt(2)>0.

For the first strict sign, b<7/10 and sqrt(2)<10/7 suffice. Thus X is contained and physically touches the circle.

The exact comparisons sqrt(2)>7/5 and sqrt(2)<99/70 give

    R^2-4>8729/1000000>0,
    1105/256-R^2>8356563/28000000>0.                 (3)

Also

    B^2=-1+4a+2a sqrt(2).

The same elementary radical bounds give 1<B<2. Therefore P_Y=(b,1) belongs to the actual left side of Y. Since b>0 and B-1>0, Y's unique farthest corner is (b+1,B), whose squared norm is exactly R^2. Y is contained and physically boundary.

Both applications have height h=1 in H's actual vertical interval [1/40,41/40]. The original supports are

    X subset {x<=-a}, Y subset {x>=b}.

Consequently the three open interiors are pairwise disjoint. H is contained: its farthest corner has squared norm at most b^2+(41/40)^2<4<R^2.

Finally

    x_0^2-a^2=671/1000000>0.                        (4)

Hence a<x_0 and h<=w, exactly the proposed small-port domain.

## 3. The target point lies strictly outside X before its actual arc begins

Let theta_*=7pi/10-gamma and q=rho(cos(theta_*),sin(theta_*)). Direct angle addition gives

    q_x+q_y
      =[(41+2sqrt(42))cos(pi/5)
          +(2sqrt(42)-41)sin(pi/5)]/40.              (5)

The exact elementary comparisons

    sqrt(42)>162/25,
    cos(pi/5)>809/1000,
    sin(pi/5)<147/250

imply

    q_x+q_y>679153/1000000
                 >677/1000=1-a.                    (6)

For the first bound, 42-(162/25)^2=6/625>0. For the latter two, use sqrt(5)>559/250, whose squared reserve is 19/62500, together with the exact cosine and sine-square formulas at pi/5. In particular

    (147/250)^2-691/2000=61/250000>0.

Expression (5) increases with sqrt(42). After substituting its lower bound, the cosine coefficient is positive and the sine coefficient is negative, so the remaining comparison directions are legitimate.

Every point of X satisfies

    x+y<=1-a,

because u is its actual outward normal for the side through P. Equation (6) therefore puts q strictly outside that actual supporting half-plane.

The actual center is c_X=(-a-sigma,1). Since a+sigma>1, its angle exceeds 3pi/4=135 degrees, while theta_*<126 degrees. Its radial rho-circle point is in the open unit: |c_X|<3/2 and |c_X|>sqrt(2)>rho imply ||c_X|-rho|<1/2.

The full closed rho-circle intersection of X is connected. One direct verification is to choose signs and order of its actual own axes so its center coordinates are x>=y>=0. Its larger far coordinate x+1/2 exceeds rho, and its corresponding inner coordinate x-1/2 is positive. On that positive-coordinate semicircle the remaining square inequalities cut out one angular interval. The existing radial-center interior point identifies the nonempty interval.

Thus the complete connected interval contains the radial center angle later than theta_*, but does not contain theta_* by (6). Its initial, gap-facing endpoint must therefore satisfy

    alpha_X>theta_*.                                 (7)

This is the strict reverse of the proposed assertion (1).

## 4. Consequence for the proof strategy

This exact three-unit channel refutes only the endpoint-only interval estimate (1). It does not establish that its free region contains an additional whole unit. In particular an actual extra square must also keep its entire inscribed radius-one-half disk disjoint from H. That whole-square requirement is absent from (1), and is available for a stronger occupied-pocket argument.

No sampled orientation, parameter mesh, numerical optimizer, finite exclusion certificate or claimed nine-unit packing is involved. All positions, physical corners and inequalities in this note are exact. No force or torque equation is asserted for this force-free counterexample, and no original graph/load flag is changed.

