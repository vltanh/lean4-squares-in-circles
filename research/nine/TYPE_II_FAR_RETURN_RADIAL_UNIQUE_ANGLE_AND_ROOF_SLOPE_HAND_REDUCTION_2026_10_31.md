# A whole radial/unique side-channel angle exclusion and the far-return roof slope

Date: October 31, 2026. **Complete hand lemmas; the remaining small-angle
far-return feature is not claimed closed here.**

The first lemma applies to any actual radial endpoint and any actual unique
circle endpoint with the stated two-force side transmission. For every
`R>2`, it excludes the entire exterior-axis sector `q>=1/3`, without a pose
cover or any equation at the other endpoint of the external force. In the
original Type II far-A-return chart, the surviving sector consequently has
the uniform full-hub slope bound `z<11/12`.

No generated certificate is a dependency of either lemma. All nine actual
units, the unchanged circle origin, original forces, applications and means
remain in the original caller. This source does not change an original flag.

## 1. Exact local domain

Use an oriented orthonormal frame `(d0,n)`, and write coordinates in that
frame. Put

    D=sqrt(R^2-1/4)-1, R>2,
    C=[-D-1,-D]*n+[-1/2,1/2]*d0.

Thus C is an actual physical radial unit. Its two physical circle vertices
and both original nonnegative circle coefficients remain; no equality of
those coefficients is imposed.

Let the other actual endpoint B own the actual minimum-side normal

    f=(-a,b), w=(-b,-a), a,b>0, a^2+b^2=1, q=b/a,

at a genuine original side-interior point Q. Its actual unit is

    B=Q+[0,1]*f+[-(1-beta),beta]*w, 0<beta<1.

Suppose that B is loaded true2 with its unique physical circle corner,
and that the complete original two incoming force vectors are

    P*f at Q, ell*u at T, P,ell>0.

The actual unit side transmitter gives

    T=Q+beta*w, U=(-1/2,-D), T-U=u, |u|=1.

Assume that the unchanged channel direction lies strictly between n and f.
Write

    u=(-sin(theta),cos(theta)),
    Theta=atan(1/q), 0<theta<Theta<pi/2,
    phi=Theta-theta.

The full original force has positive f and negative w components, so its
unique physical circle corner is exactly

    Z_B=Q+f-(1-beta)*w=T+f-w.                         (1)

This last conclusion can alternatively be included as an explicit physical
premise. In the far-return caller it is already part of the complete
physical-mask theorem. No corner with zero coefficient is discarded in C.

## 2. The full unique-B torque leaves a strict angular sector

Take the unchanged B torque about its actual circle corner Z_B. The circle
force contributes zero. Since

    Q-Z_B=-f+(1-beta)*w,
    T-Z_B=-f+w,
    u=cos(phi)*f-sin(phi)*w,

the complete equation is

    P*(1-beta)=ell*(sin(phi)-cos(phi)).               (2)

Both P and 1-beta are strictly positive. Therefore

    phi>pi/4,
    0<theta<Theta-pi/4,
    0<q<1.                                         (3)

In particular the upper endpoint in (3) is not an actual unique-B case.
It will only be used as a closed scalar comparison point. A physical-two B
does not satisfy this unique-corner torque identity and is outside this
lemma's B mask.

## 3. One circle identity excludes every q>=1/3

Put

    c=a+b, d=a-b, c^2+d^2=2, c>=1, d>0.

Here d is a scalar, distinct from the frame vector d0. From (1),

    Z_B=(-1/2-sin(theta)-d, -D+cos(theta)+c).

The two actual circle equations are

    |Z_B|^2=R^2=(D+1)^2+1/4.

Their direct difference gives the exact original identity

    D=F_q(theta)
      =[2+d+2*c*cos(theta)+(1+2*d)*sin(theta)]
         /[2*(1+c+cos(theta))].                     (4)

The denominator is positive. The function F_q is strictly increasing on
the whole closed comparison interval

    0<=theta<=Theta-pi/4.                            (5)

Here is a full sign proof. Apart from its positive denominator, its
derivative numerator is

    (1+2*d)*[1+(1+c)*cos(theta)]
        +(2+d-2*c-2*c^2)*sin(theta).                 (6)

If the second coefficient is nonnegative, (6) is positive. Otherwise use
the entire interval bounds

    cos(theta)>=c/sqrt(2), sin(theta)<=d/sqrt(2).

The expression (6) is at least

    (1+2*d)+(c+c^2+2*d+d^2)/sqrt(2)
      =(1+2*d)+(c+2+2*d)/sqrt(2)>0.

Thus (4),(3) give the strict bound

    D<Dcrit(q),
    Dcrit(q)=(2*sqrt(2)+d)/(4-2*sqrt(2)+2*c).        (7)

On 0<q<1, c=(1+q)/sqrt(1+q^2) increases and
d=(1-q)/sqrt(1+q^2) decreases. The denominator in (7) is positive,
so Dcrit strictly decreases. If q>=1/3, then

    D<Dcrit(1/3)
      =(2*sqrt(2)+2/sqrt(10))
        /(4-2*sqrt(2)+8/sqrt(10))
      <117/125.                                    (8)

For completeness, the last strict comparison is equivalent to

    242*sqrt(2)<234+343/sqrt(10).

It follows from the two exact bounds

    sqrt(2)<99/70, 1/sqrt(10)>79/250,
    242*(99/70)<234+343*(79/250).

The two squared reserves are `1/4900` and `9/62500`; the last rational
comparison has positive numerator `229/1750` after subtraction.

On the other hand R>2 gives

    D>sqrt(15)/2-1>117/125,                          (9)

because `15/4-(242/125)^2=119/62500>0`. Equations (8),(9) contradict
each other. We have proved, over the complete local domain,

    q<1/3.                                         (10)

This theorem uses the actual side N, the actual radial C position, the full
unique-B force and torque, and the physical circle equations. It makes no
force or degree assumption at B's other actual neighbor. It retains the
original endpoint means at C in any caller establishing the stated U.

## 4. Literal Type II far-return caller

The complete hand domains in

    UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md
    TYPE_II_FAR_SIDE_COMPLETE_PHYSICAL_RADIAL_ENDPOINT_MASK_ALTERNATIVE_2026_10_29.md
    TYPE_II_FAR_SIDE_UNIFORM_C_TANGENT_BOUND_AND_COMPLETE_RADIAL_C_AXIS_REDUCTION_2026_10_29.md

retain the original stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

The hubs A,D are unloaded true3; V,B,C are loaded true2; N is unloaded
true2. V has its unique physical circle corner. Keep the original common
selector, every individual circle coefficient, all physical corners, all
nine actual units and every original side mean. This is the original
D-owned roof-direction, strict far-A-vertex Type II return of D02.L135.

The earlier complete physical-mask reduction leaves B radial along f or
C radial along -n. In the latter mask with B unique, its exact original
side data have every premise of Sections 1--3. In particular B owns f at
its genuine side interior; the strict cone gives the actual U in Section 1;
the original full C2 proves `0<Q_C.d0<1/2`; and the actual B circle corner
is (1). Thus (10) holds across that entire physical mask.

The full all-nine bound R>2 used here has a hand-only route: the measure
normalization in `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`, the exhaustive
join in `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` Sections 1--3,
the LINE, OUTER_CURVE and RECTANGLES ANALYTIC_REDUCTION sources, and the
printed rational comparisons in `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`
Sections 2--6. The adopted checkpoint is
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md` Section 3. These manual
proofs give measure mass 8997/1000<9, with mass at least one on the open
interior of each contained unit. No historical checker is used here.

## 5. The whole remaining far-hub slope is less than 11/12

The exact full-hub normalization of this same original chart is

    0<e<1/2, q>0,
    J=sqrt(1+e^2), A=1+e, B0=1-e,
    M=sqrt((1+e)^2+(1+q)^2), H=(1+e)/M,
    z=(A/B0)*(1-J^3/M),
    F=(1,z), Z=lambda*F, lambda>0.                 (11)

These are derived original ratios; z is not reselected. In particular (10)
puts the entire present mask in `0<q<1/3`. The right side of (11) is
strictly increasing in q. It is therefore enough to bound it at q=1/3.
For this scalar comparison only, write

    M0=sqrt((1+e)^2+16/9),
    w=(1+e^2)^(3/2)/M0,
    Z0(e)=((1+e)/(1-e))*(1-w), 0<=e<=1/2.

We prove Z0 is strictly increasing on this entire closed interval. Direct
differentiation gives

    (1-e)^2*Z0'(e)
      =2-w*[2+3*e*(1-e^2)/(1+e^2)
                -(1+e)*(1-e^2)/M0^2].             (12)

The following three bounds cover the full interval, including endpoints.

First w has at most one interior critical point, and it is a minimum.
Indeed the sign of w' is the sign of

    -1+(22/3)*e+5*e^2+2*e^3,

which is strictly increasing. Thus its maximum is at an endpoint, and

    w<=max(3/5,15/(4*sqrt(29)))<7/10.               (13)

Second,

    3*e*(1-e^2)/(1+e^2)<=1.                        (14)

For a short complete polynomial verification set t=2e in [0,1]. The
numerator after multiplying (14) by its positive denominator is

    1-3*e+e^2+3*e^3
      =(1-t)^3+(3/2)*t*(1-t)^2
        +(1/4)*t^2*(1-t)+(1/8)*t^3>0.

Third, `(1+e)*(1-e^2)>=1` since e<=1/2, while `M0^2<=145/36`.
Consequently

    (1+e)*(1-e^2)/M0^2>=36/145.                    (15)

Equations (12)--(15) give

    (1-e)^2*Z0'(e)
      >2-(7/10)*(3-36/145)=107/1450>0.

Therefore the full original slope satisfies

    z<Z0(1/2)=3-45/(4*sqrt(29))<11/12.             (16)

The last inequality is equivalent to `sqrt(29)<27/5`, whose squared
reserve is `4/25>0`. This is one continuous derivative proof; no sampled
angle or pose is used.

## 6. Exact remaining boundary of these results

The original C-radial/B-unique far-return mask is reduced to

    0<q<1/3, 0<z<11/12.

The complete original forces at C and B remain additional conditions.
For clarity, put

    u0=cos(theta), v0=sin(theta),
    c=a+b, d=a-b,
    E=(1/2+d)*u0+(D-c)*v0,
    G=sqrt(1+q^2)-D-q/2+u0-q*v0.

In the normalization `P=sqrt(1+q^2)`, the full unique-B force gives
`ell=G/E`, while the full radial-C torque gives

    (q+z)*Q_C.d0=ell*(D*v0+u0/2).

Here E>0 follows, for example, by differentiating the actual circle
identity (4): `E=(1+c+u0)*F_q'(theta)>0`. The strict actual C port
`Q_C.d0<1/2` consequently implies the exact further condition

    z>2*(G/E)*(D*v0+u0/2)-q.                        (17)

Equation (17), its circle identity (4), all original hub equations and
all nine physical units are retained. This source does not assert an
unproved uniform lower bound for the right side of (17). B radial,
including the overlap where both endpoints are radial, also remains a
separate mask of the original far-return feature. The previous generated
37,182-node cover is neither replayed nor credited as a hand proof here.

All calculations above are displayed elementary identities, positive
denominator comparisons and continuous monotonicity arguments. No Lean,
CI, computational exclusion certificate, remote write or original-flag
change is part of this source.
