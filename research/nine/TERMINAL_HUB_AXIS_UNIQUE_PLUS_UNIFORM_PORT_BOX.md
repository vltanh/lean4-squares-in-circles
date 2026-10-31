# One continuous scalar bound controls every terminal port in the unique-plus tip-owned return

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed uniform scalar and physical-port theorem, submitted for independent review.** The entire actual unique-V/plus-W mask satisfies d/K>2/3. It follows that its unchanged terminal port has

    -7/20<B_T<1/6, A_T>7/15,

whenever the actual terminal unit physically touches the circle. The proof keeps the full U3 and the genuine V2 and uses no T force equation or W2 surrogate.

This is a whole continuous port theorem, not a completion-capacity assertion. Its final caller must still prove the needed diagonal-port inequality and actual pocket routing.

## 1. Exact actual entry

Use TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md at its exact pin below. Keep its original local chart, all true degrees, actual means and physical masks. Restrict to the unique physical V circle corner and an actual physical plus W corner; a physical W tie is included in the plus premise. Assume

    2<=R<=sqrt(1105/256).

The complete entry gives

    X>sqrt(3), 1/2<Y<1,
    X^2+Y^2=R^2,

    a,b,c,d>0,
    a^2+b^2=c^2+d^2=1,
    K=ad+bc>0, L=ac-bd>0,
    K^2+L^2=1,

    0<tau<K-b,
    rho=(d-L*tau)/K
         =1-(Y/X)*(1-tau),

    Z_W^+=(X-1+tau+L,Y-1-K),
    |Z_W^+|=R.                                      (1)

The original full U3 fixes

    h=bc/K,
    S=(-A_T,B_T)

in the positively oriented V-top frame (-k,n), where

    A_T=Y-1+rho+b-h*a,
    B_T=X-1-a-h*b.                                  (2)

No port in (2) is chosen or moved.

Put

    r=Y/X,
    kappa=d/K,
    z=L/K.

The exact original identities yield

    kappa=a-z*b<a,
    h=1-a*kappa,
    tau=(r-1+kappa)/(r+z).                          (3)

The last identity follows from rho=kappa-z*tau and the unique physical V torque. It is never asserted on a two-circle V mask.

We first prove the stronger scalar conclusion

    kappa>2/3.                                      (4)

Its proof uses only the data displayed above and R>=2, after the entry's X>sqrt(3),Y<1 reduction. No terminal premise is needed.

## 2. A whole-domain ellipse bound under the alleged kappa<=2/3

Suppose kappa<=2/3. Positivity of tau in (3) gives

    r>1-kappa>=1/3.

Because Y<1 and X>sqrt(3),

    1/3<r<1/sqrt(3)<3/5.

Define

    beta=1-1/(3r) in (0,4/9),
    A0=X-1>0, v0=1-Y>0,
    B0=beta*A0+v0>0.

Since L+r*K>=r and kappa<=2/3, equation (3) gives the uniform estimate

    tau=K*(r-1+kappa)/(L+r*K)
          <=beta*K.                                (5)

The actual plus corner has positive first coordinate and negative second coordinate. Thus (5) gives

    |Z_W^+|^2
       <=(A0+L+beta*K)^2+(v0+K)^2.

Expanding this upper bound and using L^2+K^2=1 shows that its circle deficit is at least

    2(X+Y)-3
       -2beta*L*K-beta^2*K^2-2A0*L-2B0*K.

The complete quadrant bounds 2LK<=1, K^2<=1 and Cauchy's inequality imply the further lower bound

    2(X+Y)-3-beta-beta^2
                      -2sqrt(A0^2+B0^2).           (6)

Finally,

    sqrt(A0^2+B0^2)
       <=A0+B0^2/(2A0),

by squaring the two positive sides. Therefore (6) is at least

    T(X,r)/A0,

where

    T(X,r)=(2Y-1-beta-beta^2)*(X-1)
               -[beta*(X-1)+1-Y]^2,
    Y=r*X.                                         (7)

It remains to prove T>0 on the entire continuous domain. That will put the actual physical circle point strictly inside D_R.

## 3. One explicit positive polynomial covers the full scalar range

Write

    T(X,r)=A2(r)*X^2+A1(r)*X+A0r(r),

where direct expansion of (7) gives

    A2=2r*(1+beta)-beta^2-r^2,
    A1=-1-3beta+beta^2-2beta*r,
    A0r=3beta.                                      (8)

Here A0r is a scalar coefficient, not the positive length A0=X-1.

### 3.1. A uniform elementary lower bound for X

From R>=2,

    X>=2/sqrt(1+r^2)>2-r/2=:x0.                    (9)

For completeness, both sides are positive. After squaring, the strict comparison is equivalent to

    r*[2-(17/4)r+2r^2-r^3/4]>0.

The bracket decreases on [1/3,3/5], since its derivative is at most -17/4+12/5<0. At 3/5 it is 29/250>0. Thus (9) holds throughout the whole interval.

### 3.2. T increases in X above the comparison line

Since r>=1/3 and beta<=4/9,

    A2>=2r-r^2-beta^2>=5/9-16/81=29/81>0.

Set u=r-1/3. On the enlarged interval 1/3<=r<=3/5,

    0<=u<=4/15<1/3.

Exact expansion at x0=2-r/2 gives

    9r^2*[2A2*x0+A1]
      =-3+28r-87r^2+141r^3-72r^4+9r^5

      =28/27+(62/9)u+(28/3)u^2
                        +u^3*(55-57u+9u^2)>0.      (10)

Indeed the last bracket is at least 55-57/3=36. Every remaining displayed term is nonnegative, with strictly positive constant. Because A2>0, (10) proves that T increases strictly with X for every X>=x0.

### 3.3. The whole comparison line has a strict positive reserve

Another exact expansion gives

    36r^2*T(x0,r)
      =-8+90r-355r^2+600r^3-411r^4+108r^5-9r^6

      =11/81-(10/9)u+(28/3)u^2
          +u^3*(496/3-246u+90u^2-9u^3).            (11)

The first three terms form a quadratic with global minimum

    11/81-25/756=233/2268>0.

For 0<=u<=1/3 the final bracket is at least

    496/3-82-1/3=83>0,

after dropping its nonnegative 90u^2 term. Thus the entire expression (11) is strictly positive.

Equations (9)--(11) prove T(X,r)>0 uniformly throughout the complete alleged kappa<=2/3 domain. This is a printed global polynomial proof, not a stored collection of sampled scalar cases.

By Sections 2--3, the actual plus circle point has strictly positive circle deficit, a contradiction. This proves (4).

## 4. The entire unchanged vertical port lies in one small box

From kappa>2/3 and kappa<a,

    a>2/3,
    h=1-a*kappa>b^2.

Consequently

    a+b*h>a+b^3>1-b^2+b^3>=23/27.                  (12)

The middle strict inequality uses a>a^2=1-b^2. The last inequality follows from the global maximum b^2*(1-b)<=4/27 on [0,1], obtained by differentiating the cubic.

Since Y>1/2 and R^2<=1105/256,

    X<121/60,

with squared reserve

    (121/60)^2-(1105/256-1/4)=31/57600>0.

Equations (2),(12) give

    B_T<61/60-23/27=89/540<1/6.                    (13)

For the opposite direction,

    a+b*h=a+b-ab*kappa
                <a+b-(2/3)ab.

Writing u0=a+b in (1,sqrt(2)], with ab=(u0^2-1)/2, the last expression is

    u0-(u0^2-1)/3.

It increases throughout [1,sqrt(2)], because 1-2u0/3>0. Hence

    a+b*h<sqrt(2)-1/3.

Together with X>sqrt(3), this proves

    B_T>sqrt(3)-sqrt(2)-2/3>-7/20.                  (14)

For the final exact comparison, use sqrt(3)>433/250 and sqrt(2)<99/70. Their squared reserves are 11/62500 and 1/4900, and

    433/250-99/70-19/60=11/10500>0.

Thus (13)--(14) hold for every original continuous orientation and the whole physical W plus mask, including its two-circle tie.

## 5. The actual boundary terminal forces A_T>7/15

Let P0=Y-1+rho be the actual V-side transverse coordinate. The unique force identity gives

    P0=Y*(1-(1-tau)/X)
         >(1/2)*(1-1/sqrt(3))>1/5.                 (15)

The last comparison follows from sqrt(3)>5/3.

Also, by (4),

    a*h=a*(1-a*kappa)
            <a-(2/3)a^2<=3/8.

Therefore the actual port satisfies

    A_T=P0+b-a*h>-7/40.                            (16)

This is a lower bound on the original point. No positive endpoint moment or T2 equation is needed here.

The original S belongs to the actual boundary T. Any physical T circle corner is within its unit diameter sqrt(2), so

    |S|>=R-sqrt(2)>=2-sqrt(2),
    |S|^2>12/35,                                   (17)

using sqrt(2)<99/70.

By (13)--(14), |B_T|<7/20. Hence

    A_T^2>12/35-49/400=617/2800
                               >49/225=(7/15)^2,   (18)

with exact reserve 13/5040 in the last comparison. The negative alternative in (18) contradicts (16). Thus

    A_T>7/15.                                       (19)

This argument preserves every physical T circle mask and every zero individual coefficient. Its actual true degree is arbitrary and no force at T has been added or dropped.

## 6. Exact scope for a later whole-pocket join

Every original unique-V/plus-W case in the stated radius window therefore has

    P0>1/5,
    A_T>7/15,
    -7/20<B_T<1/6.                                 (20)

These estimates hold simultaneously at the same unchanged original points. In particular both original V-side point P=(-P0,X-1) and terminal point S=(-A_T,B_T) lie strictly left of the fixed line x=-1/5 in the V-top frame. The actual intermediate upper-left U vertex lies farther left than P.

A later full component proof may use this fixed support line after it also proves the location of every physical T circle corner, the actual selected closing circle arc and the angular cone for the whole occupied crosscut. None of those unproved routing conclusions is asserted merely from (20).

The additional diagonal-port target A_T-B_T<199/250 is not supplied by this manuscript. Its proof, the full genuine endpoint torque, actual circle order and unchanged completion allocation remain necessary before the current original D02 feature can be called closed.

## 7. Exact inputs and verification boundary

| Complete source | SHA-256 | Exact operative use |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Complete original contact/mean chart, unique V identity, whole W mask, and X>sqrt(3),1/2<Y<1 for the physical plus mask |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original force/torque and actual physical means; no new selection |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Optional literal original U=2,V=1,W=0,T=3 and all true degrees and extras |

The new scalar proof is completely printed in Sections 2--3, including both polynomial expansions and full-interval positivity arguments. Exact arithmetic checks verify those expansions and displayed reserves; no numerical pose or geometric minimizer supplies any assertion.

All actual normals, force magnitudes, physical circle corners and individual zero coefficients, true degrees and original side means remain. No Lean compilation, CI, numerical pose search, computational pose certificate, remote write, shared-ledger mutation or whole original family credit is used.

