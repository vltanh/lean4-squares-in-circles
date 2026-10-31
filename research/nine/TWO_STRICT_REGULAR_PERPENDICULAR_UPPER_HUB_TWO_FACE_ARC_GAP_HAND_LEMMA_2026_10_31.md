# Two exact circle-face angle gaps for the regular upper hub pocket

Date: October 31, 2026 UTC. Joint hand continuation.

**Status: complete analytic hand lemma.** In the actual regular
two-unique chart, the two B-face thresholds which can face the upper
A pocket each occur less than pi/4 after the A roof threshold, in
the full roof-height range `47/50<T<=7/6`. The proof below includes
all scalar monotonicity, the actual far-circle-corner equation, and
an exact two-row rational comparison. A separate physical winding
argument is required to identify these thresholds with every free
flank of the actual pocket. No pocket emptiness or original-row
closure is asserted solely from this analytic lemma.

Use T for the roof height throughout; it is not the earlier symbol
t=1-rho.

## 1. Actual coordinates and exact scalar premises

Retain the entire regular two-unique, unloaded-side-N chart. The
complete existing inputs used to enter this lemma are:

* `TWO_STRICT_REGULAR_TWO_UNIQUE_FORCE_RATIO_AND_HALF_CLEAR_HUB_POCKETS_2026_10_31.md`,
  which gives m>1 with the full original V2 torque retained;
* `TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_HUB_ROOF_COORDINATE_LOWER_BOUND_2026_10_31.md`,
  which gives the actual coordinate y>11/25;
* the same original owned-side chart and physical unique B corner.

Retain all nine original physical units and apply the complete hand
radius reduction R>2. Its precise current route is
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
with the five fixed values and derivative supplied by the printed
analytic proof in `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`,
Sections 2--6. Acceptance of that entire same-nine-square route and
retirement of its historical checker dependency are recorded in
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3. The same
nonnegative radial measure has total mass 8997/1000<9 and gives
every actual open unit square mass at least one in D_2, so the nine
original interiors force R>2. No checker is needed or run here.
This is not an R>2 assertion about an isolated six-square core. Then

    d=sqrt(R^2-1/4)-1,
    14/15<d<61/60.

The lower comparison follows from `15>3364/225`; the upper bound
is the existing original-window comparison. Work in A's actual
orthonormal frame (h,e), and put

    P_h=d*cos(alpha)-(1/2)*sin(alpha),
    B0=d*sin(alpha)+(1/2)*cos(alpha),
    T=B0+y,
    q0=1-P_h,
    p=sqrt(1+m^2), m>1,
    r=5/4, l=sqrt(r^2-T^2).

The present lemma treats

    47/50<T<=7/6.                              (1)

Indeed B0>1/2 and y>11/25 give the strict lower endpoint. The actual
AB point is K=(-q0,T) in this frame. Consequently

    A=K.b=(T+m*q0)/p>0,
    X=-K.w=(m*T-q0)/p,
    D=[(m+1)*l+(m-1)*T]/(p*sqrt(2)).           (2)

The actual B corner in this pocket is

    Z_B=K+b-(1-beta_B)*w,
    0<beta_B<1,
    |Z_B|^2=R^2.

In particular its positive far w-coordinate magnitude is

    F_B=X+1-beta_B>X,
    R^2=(A+1)^2+F_B^2.                        (3)

No mean or physical circle corner has been replaced to obtain (3).

Since `P_h^2+B0^2=d^2+1/4>1009/900`, and
`B0=T-y<T-11/25`,

    -1/60<q0<Q(T),
    Q(T)=1-sqrt(1009/900-(T-11/25)^2).         (4)

The square root is positive. To check the relevant branch, P_h>0
in the entire original angle range, and P_h<d<61/60 gives the
lower q0 bound. Put u=T-11/25. In (1),

    1/2<u<=109/150,
    1009/900-u^2>=1112/1875>9/16.

Thus throughout the complete interval

    Q(T)<1/4,
    Q'(T)=u/sqrt(1009/900-u^2)<1.              (5)

For the last inequality, both sides are positive and
`2*(109/150)^2<1009/900` is exactly 23762<25225 after multiplication
by 22500. No independent enlargement of T and q0 is used below
unless explicitly bounded in a displayed estimate.

The two scalar conclusions to be proved are

    (m+1-sqrt(2))*T-(m-1)*l>sqrt(2)*m*q0,      (6)
    F_B>D.                                    (7)

## 2. The inner-face inequality holds over the whole interval

Define

    C(T)=T-l-sqrt(2)*Q(T).

Because T>l in (1), sqrt(2)<3/2 and the square-root denominator in
(5) exceeds 3/4,

    C'(T)
      =1+T/l-sqrt(2)*Q'(T)
      >2-(3/2)*(109/150)/(3/4)
       =2-109/75>0.                            (8)

At T0=47/50,

    Q(T0)=1/15,
    l(T0)=sqrt(6789)/100<83/100,
    C(T0)>11/100-1/10=1/100.

Hence (4),(8) give

    T-l-sqrt(2)*q0>0.

Subtract the right side of (6) from its left side and regroup:

    m*(T-l-sqrt(2)*q0)+(1-sqrt(2))*T+l
       >(2-sqrt(2))*T-sqrt(2)*q0
        =sqrt(2)*[(sqrt(2)-1)*T-q0]>0.

The first strict step uses m>1 and the preceding positive bracket.
For the last, use `sqrt(2)-1>2/5`, T>47/50 and q0<1/4.
This proves (6) on the entire continuous domain.

## 3. A uniform monotonicity lemma for the outer-face test

For fixed T,q0 in the bounds (1),(4), define

    F(m)=(1+A)^2+D^2.

We claim F is strictly decreasing for m>=1. Put
`kappa=arctan(m)` and `psi=kappa-pi/4`. Then

    pi/4<=kappa<pi/2,
    A=T*cos(kappa)+q0*sin(kappa),
    X=T*sin(kappa)-q0*cos(kappa),
    D=l*cos(psi)+T*sin(psi).

Here X>0: both T>47/50 and q0<1/4 give the claim directly on the
actual kappa interval. Also `A'=-X`, so A decreases to q0 and
`A>=q0>-1/60`. Prime in this section denotes differentiation in
kappa. Set

    g=(1+A)*X.

Since `X'=A`, direct differentiation gives

    g''=-X*(1+4*A)<0.

Thus g is strictly concave on the closed interval
`[pi/4,pi/2]`, with its continuous endpoint values understood.
Its minimum is at an endpoint. Those endpoint values obey

    g(pi/2)=T*(1+q0)
        >(47/50)*(59/60)=2773/3000>25/32,

    g(pi/4)=(T-q0)/sqrt(2)+(T^2-q0^2)/2
        >(69/100)*(7/10)+8211/20000
         =17871/20000>25/32.                  (9)

For the second bound, the displayed expression increases with T
and decreases with q0 in the complete bounds under consideration;
its lower endpoint substitution is T=47/50,q0=1/4. The inequality
`1/sqrt(2)>7/10` is exact by squaring positive quantities.

Meanwhile `D^2+(D')^2=l^2+T^2=25/16`, so

    D*D'<=(D^2+(D')^2)/2=25/32.

Consequently

    F'/2=D*D'-(1+A)*X<0.                      (10)

Because arctan(m) increases with m, (10) proves the claimed strict
decrease in m. The proof does not assume an unverified sign for D'
or replace the correlated cap by a pose sample.

## 4. The lower roof-height range: F(m)<4

First let `47/50<T<=11/10`. The cap Q(T) increases, and

    Q(11/10)<7/40.

Indeed

    1009/900-(33/50)^2=3856/5625>(33/40)^2.

By (10), F(m)<=F(1). At m=1,

    F(1)=(1+(T+q0)/sqrt(2))^2+25/16-T^2.

This expression increases in T and q0 on the present full bounds:
its T derivative is `sqrt(2)+q0-T>0` and its q0 derivative is
`sqrt(2)+T+q0>0`. Therefore

    F(m)<(1+51/(40*sqrt(2)))^2+141/400
         =1+51*sqrt(2)/40+3729/3200
         <4.                                  (11)

For the final exact comparison use sqrt(2)<99/70. The resulting
upper expression is 88895/22400, with positive reserve
`4-88895/22400=705/22400`.

## 5. Moderate slopes at the upper roof heights: D<X

Now let `11/10<=T<=7/6` and `1<=m<=3/2`. From (5) and
Q(11/10)<7/40,

    q0<Q(T)<T-37/40.                           (12)

Also `l<=l(11/10)<3/5`. Consider the expression

    G(m)=sqrt(2)*(m*T-q0)
                    -[(m+1)*l+(m-1)*T].

It is affine in m. At its two endpoints, (12) gives

    G(1)>sqrt(2)*(37/40)-6/5
         >(7/5)*(37/40)-6/5=19/200>0,

    G(3/2)>(sqrt(2)-1)*T/2
                       +sqrt(2)*(37/40)-3/2
         >(2/5)*(11/10)/2+(7/5)*(37/40)-3/2
          =3/200>0.

Thus G(m)>0 on the entire interval, including both endpoints. By
(2), this is exactly D<X. Equation (3) consequently gives

    F_B>X>D.                                  (13)

This is a direct use of the actual unique-circle-corner equation;
no upper bound on R has replaced it.

## 6. Larger slopes: an exact two-row endpoint comparison

It remains to treat `11/10<=T<=7/6` and m>=3/2. By (10),
`F(m)<=F(3/2)`. At m=3/2,

    A=(2*T+3*q0)/sqrt(13),
    D=(5*l+T)/sqrt(26).                         (14)

The second expression strictly decreases with T, since its derivative
is `(1-5*T/l)/sqrt(26)<0`. Use sqrt(13)>18/5 and the following two
complete intervals.

| Whole T interval | Valid correlated q0 bound | Upper bound for A | Upper bound for D squared | Exact reserve below 4 |
| --- | --- | --- | --- | --- |
| `[11/10,23/20]` | `q0<11/50` | `A<37/45` | `D^2<1681/2600` | `4-6724/2025-1681/2600=6943/210600>0` |
| `[23/20,7/6]` | `q0<1/4` | `A<185/216` | `D^2<5329/10400` | `4-160801/46656-5329/10400=622793/15163200>0` |

Every bound in this table follows directly as follows. On the first
interval,

    1009/900-(71/100)^2>(39/50)^2,

because the difference is 31/3600; hence q0<11/50 by (4). Formula
(14) gives

    A<(2*(23/20)+3*(11/50))/(18/5)=37/45.

Since D decreases with T and l(11/10)<3/5,

    D<(5*(3/5)+11/10)/sqrt(26)=41/(10*sqrt(26)).

On the second interval q0<1/4 was already proved uniformly in (5),
so

    A<(2*(7/6)+3/4)/(18/5)=185/216.

At T=23/20, `l=sqrt(6)/5<1/2`. Thus monotonicity in T gives

    D<(5/2+23/20)/sqrt(26)=73/(20*sqrt(26)).

Squaring these positive estimates gives precisely the two table rows.
They prove F(m)<4 throughout this last domain.

## 7. Completion of the outer-face inequality

The three exhaustive parameter ranges were:

1. `T<=11/10`, for every m>1, where (11) gives F(m)<4;
2. `T>=11/10` and `1<m<=3/2`, where (13) gives F_B>D directly;
3. `T>=11/10` and `m>=3/2`, where Section 6 gives F(m)<4.

Every equality boundary appears in at least one full interval. In
the first and third ranges, use R^2>4 and the same original circle
equation (3):

    F_B^2=R^2-(A+1)^2>4-(A+1)^2>D^2.

Both F_B and D are positive, so F_B>D. Together with (13) this
proves (7) on the whole domain (1).

## 8. The exact angular meaning of the two inequalities

Put

    theta_A=arcsin(T/r),
    kappa=arctan(m),
    epsilon=theta_A-kappa+pi/4.

Because T>47/50>r/sqrt(2), m>1 and kappa<pi/2,

    0<epsilon<pi/2.

The right side obtained after rearranging (6) is exactly

    A<[(m+1)*T-(m-1)*l]/(p*sqrt(2))
      =r*sin(epsilon).

Since A>0, this also proves A<r and makes the original inner-face
angle unambiguous. Thus

    kappa+arcsin(A/r)-theta_A<pi/4.             (15)

Similarly the actual D in (2) is

    D=r*cos(epsilon).

Define the actual outer-face threshold by

    chi_B=arccos(min(1,F_B/r)).

If F_B>=r, the corresponding far-w constraint is automatic on the
inner circle, and chi_B=0 encodes exactly that case. If F_B<r,
it is the ordinary positive arccos threshold. In both exhaustive
cases, (7) gives chi_B<epsilon, so

    kappa+chi_B-theta_A<pi/4.                   (16)

Consequently the maximum of these two face thresholds also lies
strictly less than pi/4 after theta_A. Equations (15)--(16) are the
complete analytic angle-gap result. Identifying that maximum with
the beginning of every actual B obstruction arc, assigning the
correct exterior flank, and retaining any additional physical
contacts are geometric winding obligations for the caller; they
are not silently inferred from the scalar inequalities.

All original physical units, means, circle coefficients and full-star
equations are retained. The only table is the two exact rational
interval comparison printed in Section 6, whose entries are proved
in the adjacent text. No external script, numerical certificate,
Lean/Lake invocation or CI was used.
