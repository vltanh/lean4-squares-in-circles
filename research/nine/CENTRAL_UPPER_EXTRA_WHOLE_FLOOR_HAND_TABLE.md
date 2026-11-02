# Every central extra above P has whole floor above one tenth

This is a short physical reduction followed by a 356-leaf exact rational table. The complete original routed `000/01` mask is retained. The proof uses no Lean, Lake, or CI.

**Theorem.** Let U be one of the additional physical squares. If

    |x_U|<29/60,          y_U>y_P,

then

    y_U-h_U>1/10.                                     (1)

The theorem does not require a low-floor hypothesis on P. In the complete low-floor domain, the previously proved central-extra theorem supplies at least one such U, so (1) produces a new high-floor middle square for the original shoulders L,R.

## 1. Uniform physical inputs

Write

    p=h_P, u=h_U, x=x_P, v=x_U, y=y_P, V_U=y_U,
    rho=91/60, l=29/60, a0=23/30, a1=13/12,
    C=451/810, d0=981/1240.

All halfwidths lie in `[1/2,1/sqrt(2)]`. The established full-mask bounds give

    -23/405<x<23/60,
    -13/12<x_L<-23/30,       y_L>3/4,
    x>p-C.                                           (2)

The original outer cone edges give `y_M1,y_M2>-139/120`, and P is above both mains. The central adjacent-proxy barrier therefore implies

    y-p>min(y_M1,y_M2)+869/1860
         >-139/120+869/1860=-857/1240,
    y>p-857/1240.                                    (3)

Every pair of physical unit squares satisfies

    |center_A-center_B|>=1+|h_A-h_B|,                 (4)

as proved in the orientation-aware distance lemma in `LOW_CENTRAL_FLOOR_RIGHT_SIDE_EXTRA_BARRIER.md`. This retains the cost of their differing orientations; the weaker bound one alone is insufficient for the first reduction below.

Assume, for contradiction, that U violates (1), so `V_U<=u+1/10`.

## 2. U must lie far to the left of P

Its positive vertical gap from P obeys, by (3),

    0<V_U-y<u-p+d0.                                  (5)

Suppose their horizontal gap were at most 3/5. Put `t=u-p`. If t>=0, the square of the required center distance from (4), minus the upper squared center distance from (5), is greater than or equal to

    (1+t)^2-(3/5)^2-(d0+t)^2
      =21703/1537600+2t(1-d0)>0.

If t<=0, the same calculation instead gives

    (1-t)^2-(3/5)^2-(d0+t)^2
      =21703/1537600-2t(1+d0)>0.

If the right side of (5) were nonpositive, it would already contradict its positive left side. Thus both square comparisons are legitimate. We obtain

    |v-x|>3/5.                                      (6)

U cannot lie to the right of P, because its central strip and (2) would give

    v-x<29/60+23/405=175/324<3/5.

Consequently `x-v>3/5`. Combining this with the original strip bounds gives the complete reduced position rectangle

    7/60<x<23/60,
    -29/60<v<-13/60.                                (7)

## 3. The original shoulder L is above U

We have `x_L<v`, and

    0<v-x_L<13/12-13/60=13/15.

If U were at or above L, its vertical gap would be less than

    1/sqrt(2)+1/10-3/4<3/50.

The squared center distance would then be less than

    (13/15)^2+(3/50)^2<1,

contradicting the two contained half-unit disks. Thus `y_L>V_U`.

Put `A=-x_L`. The actual L--P comparison gives

    A>=p+h_L-x>=p+1/2-x.

Together with (2), this places the original L center in

    A0<=A<=a1,
    A0=max(a0,p+1/2-x).                              (8)

The interval in (8) is nonempty at every physical witness. Its endpoints need not correspond to additional physical squares; they will only bound the original center.

Since the L center has norm less than rho, while L and U have center distance at least one,

    V_U<sqrt(rho^2-A^2)-sqrt(1-(A+v)^2)=F(A).         (9)

Every radical is real on the physical interval: `0<A+v<13/15<1` and `A<=13/12<rho`.

For fixed negative v, the derivative of F has the sign of

    (rho-1)A+rho*v.

Indeed its two terms are `-A/sqrt(rho^2-A^2)` and `(A+v)/sqrt(1-(A+v)^2)`, and squaring the two positive quantities reduces their comparison to `rho*(A+v)` versus A. This sign changes at most once, from negative to positive. Hence F has no interior maximum on (8), and

    V_U<=Ucap:=min(u+1/10,max(F(A0),F(a1))).          (10)

The actual shoulder has therefore been eliminated only through valid consequences of its original containment, its original nonoverlap with U, and actual L--P separation.

## 4. Retain the genuine P--U side-axis inequality

Use unsigned orientation slopes `tP,tU in [0,1]`, with

    a(t)=1/sqrt(1+t^2), b(t)=t/sqrt(1+t^2),
    h(t)=(a(t)+b(t))/2.

Thus `p=h(tP)`, `u=h(tU)`. Both original physical chiralities remain allowed. Put

    D=x-v,
    Vcap=Ucap-p+857/1240,
    s=(1+aP*aU+bP*bU+|aP*bU-bP*aU|)/2.

Equations (3) and (10) imply `0<V_U-y<Vcap`. A physical separating axis of P and U belongs to one of their side frames. Regardless of chirality, its absolute projection is bounded above by one of

    aP*D+bP*Vcap, bP*D+aP*Vcap,
    aU*D+bU*Vcap, bU*D+aU*Vcap.

The genuine support sum is at least s. Thus every hypothetical U must satisfy

    max(aP*D+bP*Vcap,bP*D+aP*Vcap,
        aU*D+bU*Vcap,bU*D+aU*Vcap)>=s.              (11)

Here s>=1. This lower bound is retained in the exact interval calculation to avoid unnecessary dependency loss.

## 5. Complete four-variable exact table

The closed root rectangle is

    tP,tU in [0,1],
    x in [7/60,23/60],
    v in [-29/60,-13/60].                            (12)

It contains every physical possibility (7), including a closed cover of its boundary. The following expressions must be nonnegative at any such witness:

| Rule | Necessary expression | Leaves |
|---|---|---:|
| 0 | x-p+C | 0 |
| 1 | D-3/5 | 15 |
| 2 | Vcap | 0 |
| 3 | left side of (11) minus s | 341 |
| **Total** | **All of (12)** | **356** |

The complete binary subdivision tree is `upper_extra_floor_certificate.json`. Its independently written exact arithmetic replay is `verify_upper_extra_floor_exact.py`, and its report is `upper_extra_floor_verification_report.json`.

All 356 leaves passed exact replay, with strictly positive exclusion reserve exceeding 1/100000. The tree has 711 nodes and maximum depth 16. Its SHA-256 is

    1381a04af873ac5cb6736e906409250e251ab718b111a9f79143bc0b404ad333.

The verifier reconstructs the rational root and every midpoint split, checks complete binary coverage, and verifies each terminal inequality with Fraction arithmetic and integer-square-root enclosures at scale 2^44. It imports no discovery producer and uses no floating arithmetic. The finite table is an exact proof; the numerical search only chose the subdivisions.

This excludes every hypothetical central U above P with whole floor at most 1/10, proving (1).

## 6. The upper-triple caller and the completed support theorem

The exact low-floor central-extra theorem supplies a central extra U above P. By the present result it has whole floor greater than 1/10. The original shoulders L,R satisfy

    x_L<-23/30<x_U<23/30<x_R,
    25/32<y_L,y_R<21/16,
    y_U>=3/5, y_U<91/60.

Therefore the vertical center difference between U and either shoulder is less than one. Every genuine separating normal directed from U toward R has positive horizontal component: a nonpositive horizontal component would give projection less than one in unit normalization, while the two half-unit disks require at least one. The reflected statement supplies a negative horizontal component for U toward L.

Thus the original five physical units M0,L,U,R,M3 admit the outward fork normals needed by a joint two-sided support argument. No center-cone comparison and no actual L--U or U--R edge has been presumed.

Here are their complete finite slope bounds. Normalize the two U-to-shoulder normals to

    m_L=(-1,z_L),       m_R=(1,z_R).

The horizontal center gaps are below `13/12+29/60=47/30`. The upward vertical difference is below `21/16-3/5=57/80`, and the downward vertical difference is below `91/60-25/32=353/480`. Since `57/80<353/480`, either sign of either normal obeys, with `t=|z|`,

    sqrt(1+t^2)<47/30+(353/480)*t.

For t>=6, the unit-vector lower bound `(7+24t)/25` contradicts this inequality. At t=6 its excess is exactly `73/1200>0`, and its excess derivative is `539/2400>0`. Thus

    |z_L|,|z_R|<6.                                  (13)

The original endpoint-to-shoulder physical normals have positive vertical component because their horizontal center gaps are below 3/4. Normalize them to

    n_L=(w_L,1),       n_R=(-w_R,1).

Section 1 of `FORK_SEPARATOR_SLOPE_BOUNDS.md` uses only each original endpoint and its original shoulder, so it applies unchanged here and gives

    -2/3<w_L,w_R<6.                                 (14)

Their physical owner is the corresponding endpoint or shoulder, with no omitted alternative. If the endpoint owns its normal, the existing main-frame argument further gives `|w|<7/100`; the near-horizontal endpoint-owned alternative has already been excluded by (14).

Consequently the original five-square caller has the full closed cover

    w_L,w_R in [-2/3,6], z_L,z_R in [-6,6],
    |x_U|<=29/60, y_U>=h_U+1/10,

along with the original endpoint/shoulder center and angle bounds. This covers both central-normal signs, every endpoint-normal owner, and every equality face used by a finite table. It does not import the narrower x-band of the original P or the older bounded-main-height caller.

The completed theorem `UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md` applies to exactly this original five-square domain, with no central-normal owner restriction. If the containing squared radius is strictly below Q, it gives

    46*(x_M3-x_M0-h_M0-h_M3)+27/2 < 211/2.

The actual main four-chain gives `x_M3-x_M0-h_M0-h_M3>=2`, so its left side is at least 211/2. This is a contradiction. Therefore the original low-floor mask is excluded at every strictly subcritical radius once its central-extra theorem has supplied U. No new coordinate-separation or center-cone property of L,U,R is assumed.
