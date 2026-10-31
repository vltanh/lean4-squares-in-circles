# One low physical port controls the entire boundary-center arc angle

Date: October 28, 2026 UTC. Author: sole-UV continuation.

**Status: complete proposed force-free hand lemma, submitted for full independent review.** This is a geometric implication for an actual contained boundary unit. No positive degree, selected normal, force equation, circle-weight split, or endpoint owner is assumed. Its whole continuous domain is proved by one elementary squared-distance estimate with a strict rational reserve.

## 1. Statement about the unchanged origin and an actual point

Put

    Q=1105/256, rho=5/4, beta=arctan(5/16).

Let E be an actual closed unit square contained in D_R about the unchanged origin, with 2<R<=sqrt(Q), and with at least one actual containing-circle corner. Let P=(-A,-h) be any actual point of E, where

    0<A<=1, |h|<=27/100.

Let C be E's actual center. Its direction has a unique lift theta in (pi/2,3pi/2), as proved below. Put

    theta_A=arccos(-A/rho), pi/2<theta_A<pi.

**Theorem.**

    theta-beta-theta_A < pi/2.                    (1)

In particular, if a separate actual occupied-crosscut argument routes every extra's complete connected radius-rho arc into the angular interval (theta_A,theta-beta), two disjoint arcs each longer than pi/4 cannot lie there. Equation (1) does not itself supply that routing premise.

The point P may be a vertex, a side point, an original aggregate mean, or a point used only to construct an occupied path. Its actual location is never changed. Reflection in the horizontal axis gives the corresponding reversed-angle statement.

## 2. Center radius and the correct half-plane

Set sigma=1/sqrt(2) and r=|C|. An actual containing-circle corner is at distance sigma from C, while every point of E is at distance at most sigma from C. Hence

    r>=R-sigma>129/100,
    |C-P|<=sigma,
    sigma<71/100.                                 (2)

The rational comparison in (2) uses 1/2<(71/100)^2.

We have C_x<0. Otherwise replacing P by (0,-h) could only decrease its distance to C, and the reverse triangle inequality would give

    |C-P|>=|C-(0,-h)|>=r-|h|>102/100>sigma,

contrary to (2). Thus theta has the claimed lift. If C_y>=0, then theta<=pi, so (1) is immediate from theta_A>pi/2 and beta>0.

Suppose therefore C_y<0, and write

    C=(-r*c,-r*s), c,s>0, c^2+s^2=1,
    theta=pi+phi, 0<phi<pi/2,
    c=cos(phi), s=sin(phi).

The original point-distance inequality gives r*s<=h+sigma<98/100. Consequently

    s<98/129<4/5, c>3/5.                           (3)

If phi<=beta then (1) follows at once. Retain phi>beta. Since sin(beta)=5/sqrt(281)>1/4, we also have s>1/4.

## 3. One whole-domain squared-distance contradiction

It is enough to prove

    A>rho*sin(phi-beta).                           (4)

Indeed A/rho is in (0,1), so (4) implies
phi-beta<arcsin(A/rho), which is exactly (1).

Suppose instead A<=rho*sin(phi-beta). The exact beta values give

    rho*sin(beta)=25/(4*sqrt(281))>37/100,
    rho*cos(beta)=20/sqrt(281)<6/5.                 (5)

The respective squared positive reserves are
625/16-281*(37/100)^2>0 and 36/25-400/281>0.
Using (2), (5), and the alleged reverse of (4),

    r*c-A
      >=(r+rho*sin(beta))*c-rho*cos(beta)*s
       >(83/50)*c-(6/5)*s>9/250>0.                (6)

The last comparison follows from (3). Also

    r*s-h>(129/100)*s-27/100>21/400>0.            (7)

The last comparison uses s>1/4. Both lower bounds are positive before they are squared. Thus

    |C-P|^2
      >((83/50)*c-(6/5)*s)^2
        +((129/100)*s-27/100)^2.                  (8)

After subtracting 1/2 and using c^2+s^2=1, the right side is exactly

    4657/2000 +(697/2000)*s^2
      -(498/125)*c*s -(3483/5000)*s.

Since c*s<=1/2, this is at least

    f(s)=673/2000 +(697/2000)*s^2-(3483/5000)*s.

Its derivative is strictly negative on 0<=s<=4/5, because

    f'(s)=(697/1000)*s-3483/5000<=-695/5000<0.

Therefore its full interval lower bound is

    f(s)>=f(4/5)=113/50000>0.                     (9)

Equations (8)--(9) contradict |C-P|^2<=sigma^2=1/2. This proves (4), hence the entire theorem, with all closed h and A endpoints retained.

## 4. Exact scope and reuse

The conclusion concerns the actual center and the actual radius-rho angular ray. If an independent boundary-unit arc theorem places the closed centered halfwidth-beta arc strictly inside E, its lower angular endpoint theta-beta is an occupied barrier. A caller still must prove the whole actual extra arcs are in the claimed interval and must retain the original physical units.

The theorem imposes no force, load, degree, triangle, side ownership, or common-certificate selection condition. In particular an arbitrary-degree boundary unit can serve as E when a caller has the stated physical point. It introduces no numerical pose cover, finite coefficient packet, normal reselection, changed mean, or smaller surrogate packing.

No imported mathematical theorem is needed beyond the unit-square circumradius, the triangle inequality, and the printed elementary trigonometric identities. Exact rational arithmetic was used only to check the displayed identity and reserves; the continuous argument above is the proof. No Lean compilation, CI, workflow, ledger edit, commit or remote action was performed.
