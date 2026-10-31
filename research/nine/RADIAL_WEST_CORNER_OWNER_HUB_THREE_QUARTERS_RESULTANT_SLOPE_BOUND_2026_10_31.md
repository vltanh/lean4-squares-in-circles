# A three-quarters resultant-slope bound at a radial West endpoint

Date: October 31, 2026 UTC.

**Status: complete hand inequality for the entire stated physical chart.**
The unchanged resultant at a physical radial V makes a uniformly bounded
angle with any physical radial B joined through the indicated owner hub:
the signed ratio in (7) is strictly less than 3/4. The proof needs neither
a return classification at the other hub nor an equation at B's other
neighbor. It retains the actual side-interior B port, including both
original physical circle vertices and their original nonnegative weights.

This is an inequality, not by itself an exclusion of a radial endpoint.
A caller pairing it with another endpoint theorem must identify the same
resultant, directions and normalization literally.

## 1. Original physical entry and the same-nine radius bound

Retain all nine original unit squares, their closed physical contacts,
the original positive graph, true degrees, positive contact magnitudes,
full stars, original means, physical circle vertices and every individual
nonnegative circle weight. The hand same-nine radius route is

* `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3;
* `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6;
* `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.

Those printed analytic proofs give a radial measure of total mass
8997/1000 and mass at least one on every actual contained open unit
square in D_2. The nine disjoint original interiors therefore force R>2.
No historical checking program is a premise here. With the original
upper radius bound, put

    R^2=(d+1)^2+1/4,
    117/125<d<61/60.                              (1)

The lower rational comparison is
`15/4-(242/125)^2=119/62500>0`.

Assume the following unchanged physical corner/owner-hub data:

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    h=(c,-s), e=Jrot(h), c^2+s^2=1,
    3/4<c<1, s>0,
    A=P+[-1,0]*h+[y-1,y]*e, 0<y<1,
    K=P-h+y*e,
    b=(-m*h+e)/p, w=Jrot(b),
    m>0, p=sqrt(1+m^2).                           (2)

Here AV has its original A-owned normal h; the other V contact has the
original East normal at Q. The actual unchanged AB contact K is a
genuine relative-interior point of B's minimum-b side. In the present
mask B is physically radial along b:

    B=[d,d+1]*b+[-1/2,1/2]*w.                    (3)

Thus the actual physical inequalities are

    K.b=d, -1/2<K.w<1/2.                        (4)

The full original V force and torque give, for its unchanged positive
AV and DV magnitudes mu,nu,

    B0=P.e=d*s+c/2>0,
    nu*t=mu*B0,
    r=mu/nu=t/B0 in (0,1/(2*B0)],
    R_V=nu*(East+r*h).                           (5)

The sign convention is that R_V is the physical outward circle
resultant. All its original corner weights are retained; (5) is only
their full original resultant. In particular the last endpoint
`t=1/2` is included.

For a West/strict original caller, the complete hand low-c exit is
`PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md`,
Section 6. It supplies c>3/4. No generated return or endpoint cover is
used in this lemma.

## 2. Exact radial-port and resultant formulas

Put

    q0=1-P.h=1-d*c+s/2,
    T=B0+y,
    kappa=atan(m), alpha=atan(s/c).

In the actual (h,e) coordinates, K=(-q0,T). The first equality in
(4) therefore gives

    T=d*p-m*q0.

Consequently the same original transverse coordinate is

    X=-K.w=(m*T-q0)/p=d*m-q0*p<1/2.             (6)

The argument needs only the displayed upper endpoint of (4), so it
does not replace the actual transverse mean by an endpoint or assume
X positive. Dividing (6) by p gives

    d*sin(kappa)-(1/2)*cos(kappa)<q0.

The actual resultant satisfies

    R_V.w=-nu*(c+m*s+r)/p<0,
    z_B=R_V.b/R_V.w
       =[m*(c+r)-s]/[c+r+m*s].                  (7)

**Theorem 2.1.** Under the entire physical domain (1)--(5),

    z_B<3/4.                                    (8)

The ratio is allowed to be nonpositive; that case already satisfies
(8). No additional positivity assumption on its numerator is needed.

## 3. Reducing the entire force-mean interval to one angular test

For fixed original m,c,s, the derivative of the right side of (7)
with respect to r is

    s*(1+m^2)/(c+r+m*s)^2>0.

It is therefore enough to use the closed comparison
`r=1/(2*B0)`. This is a scalar comparison, not a new choice of original
V mean or corner weights.

Define

    w0=c+d*s,
    L=sqrt(w0^2+s^2/4),
    epsilon=atan(s/(2*w0)),
    zeta=atan(3/4),
    kappa0=alpha-epsilon+zeta.                  (9)

Both alpha and zeta lie in (0,pi/4), and
`0<epsilon<alpha`. In particular `0<kappa0<pi/2`.
The elementary tangent subtraction formula gives

    atan(s/(c+1/(2*B0)))=alpha-epsilon.

Thus if (8) failed, strict monotonicity of tangent on the actual
angular interval would imply `kappa>=kappa0`. The function

    kappa -> d*sin(kappa)-(1/2)*cos(kappa)

is strictly increasing on (0,pi/2). By (6), a contradiction follows
once we prove

    F(d,alpha)=d*sin(kappa0)-(1/2)*cos(kappa0)
                    -(1-d*c+s/2)>0.            (10)

For fixed alpha, epsilon has derivative

    partial epsilon/partial d=-s^2/(2*L^2),
    partial kappa0/partial d=s^2/(2*L^2)>0.

All signs are on the actual interval in (9), so

    partial F/partial d
      =sin(kappa0)+c
        +(d*cos(kappa0)+(1/2)*sin(kappa0))
                                    *s^2/(2*L^2)>0.

It suffices to prove (10) at the single rational comparison

    d0=117/125.                                 (11)

This monotonicity uses no change of pose, contact, radius or mean in
the original packing.

## 4. Removing the remaining square root by a continuous hand bound

In this section only set d=d0. Write

    A1=1-s^2/2+d0*s*c,
    A2=s*(d0*s+c/2).

Then `cos(alpha-epsilon)=A1/L` and
`sin(alpha-epsilon)=A2/L`. Since
`cos(zeta)=4/5`, `sin(zeta)=3/5`, direct expansion gives

    5*L*F(d0,alpha)=Z-5*q0*L,
    Z=(3*d0-2)+(4*d0^2+1)*s^2
                       +(3*d0^2+3/4)*s*c.      (12)

The original c>3/4 implies

    0<s<sqrt(7)/4<53/80,
    q0=1-d0*c+s/2>1-d0>0.

The last rational sine comparison follows from
`7<(53/20)^2`. Also

    (1-c)/s=s/(1+c)<(53/80)/(7/4)=53/140<2/5,
    w0=c+d0*s>1+(d0-2/5)*s>1+s/2.

The square-root tangent inequality, with its positive arguments,
therefore yields

    L=sqrt(w0^2+s^2/4)
       <=w0+s^2/(8*w0)
       <w0+s^2/(8+4*s).                        (13)

Multiply the lower bound for (12) resulting from (13) by the
positive factor 8+4s. It is

    R(s,c)=(8+4*s)*(Z-5*q0*w0)-5*q0*s^2.

Set

    K0=8*d0^2-7/4,
    L0=4*d0^2-(15/2)*d0+1.

The fully expanded linear expression in c is

    R(s,c)=(8+4*s)*(8*d0-2-5*d0*s+L0*s^2)
              -5*s^2-(5/2)*s^3+C(s)*c,
    C(s)=-40+(8*K0-20)*s+(4*K0+5*d0)*s^2.      (14)

Its coefficient of c is negative over the entire comparison interval:
the two positive coefficients are respectively less than 23 and 26,
and `s<=53/80<2/3`, so

    C(s)<-40+23*(2/3)+26*(4/9)=-118/9<0.

For `0<=s<=53/80` one has the exact upper square-root comparison

    c=sqrt(1-s^2)<=1-s^2/2-s^4/8.

Indeed the expression on the right is positive, and its square minus
`1-s^2` equals `s^6/8+s^8/64>=0`. Because C(s)<0, substituting
this upper bound for c into (14) is a lower bound, not an upper one.
The resulting polynomial is exactly

    P(s)=3.904+6.582144*s+1.870144*s^2
            -23.597536*s^3-7.857536*s^4
            -2.758768*s^5-3.214384*s^6.         (15)

Every terminating decimal in (15) is an exact rational number. For
an independent expansion check its coefficients, in ascending order,
are

    64*d0-56,
    64*d0^2-8*d0-42,
    64*d0^2-75*d0+16,
    -16*d0^2-30*d0+37/2,
    -16*d0^2-(5/2)*d0+17/2,
    -8*d0^2+17/4,
    -4*d0^2-(5/8)*d0+7/8.

No pose sample or generated polynomial certificate is involved.

## 5. One endpoint comparison proves positivity of the whole polynomial

The constant, linear and quadratic coefficients of P are positive,
and all its higher coefficients are negative. For s>0 the function
`P'(s)/s` is strictly decreasing: differentiating its explicit expansion
gives the negative contribution from `6.582144/s`, together with
strictly negative contributions from every term of degree at least
three in P. Hence P' has at most one positive zero. Since P'(0)>0,
P first increases and then, if a zero occurs, decreases. Its minimum
on the whole interval `[0,53/80]` is therefore at an endpoint.

The first endpoint is `P(0)=3.904>0`. Put `s0=53/80=.6625`.
Direct rational multiplication gives

    s0^2>.4389,
    s0^3<.2908, s0^4<.1927,
    s0^5<.1277, s0^6<.0846.

These are exact comparisons of the respective powers of 53/80 with
the printed terminating rationals. Using the signs in (15),

    P(s0)
      >3.904+6.582*(.6625)+1.87*(.4389)
          -23.598*(.2908)-7.858*(.1927)
          -2.759*(.1277)-3.215*(.0846)
       =.0844697>2/25>0.                        (16)

This proves P>0 on the full continuous interval. Equations
(12)--(16) prove F(d0,alpha)>0. The strict monotonicity in d then
proves (10) for every original d in (1). It contradicts (6) whenever
z_B>=3/4, completing Theorem 2.1.

## 6. Exact endpoint-pair normalization for later callers

Suppose a complete original chorded-six-cycle caller also supplies
another exterior axis c_ext clockwise from b, with its unchanged
angle Theta in (0,pi), and positive exterior magnitudes p_B,p_C.
Adding its complete unloaded hub stars gives exactly

    R_V=p_C*c_ext-p_B*b.

Since `c_ext.w=-sin(Theta)`, the same ratio in (7) is then

    z_B=(p_B-p_C*cos(Theta))/(p_C*sin(Theta)).    (17)

If such a caller has an acute radial-B/unique-C side pair, reflection
and exchange of the full physical endpoint labels may identify (17)
with the standard radial-endpoint slope. That transfer must retain
the actual inner-corner channel applications and full endpoint stars;
it is not inferred merely from the words radial and unique.

For the original West/strict opposite return, the already derived
ratios are `p_B=nu*q*p`,
`p_C=nu*sqrt(c^2+(s+q)^2)`, and `r=m*q`. Equation (17) becomes
precisely

    z_B=[q*m^2+m*c-s]/[c+m*(s+q)]<3/4.           (18)

All original degrees, applications, means, physical circle corners,
individual circle coefficients and the full nine-unit completion
remain. No Lean, CI, script-generated exclusion or remote write is
part of this proof.
