# A three-quarters lower slope for every radial/unique side channel

Date: October 31, 2026 UTC.

**Status: complete hand theorem on the entire stated physical chart.**
One actual radial endpoint and one actual unique-circle endpoint force the
unchanged exterior resultant to have slope strictly greater than 3/4 in
the normalization below. The argument uses the full original endpoint
stars, their genuine side ports and both physical circle equations. It
does not require an equation, degree or owner classification at either
other exterior neighbor. A seven-row rational table covers continuous
intervals by explicit monotonicity; no sampled configuration or generated
cover is a premise.

## 1. Physical entry, signs and exact normalization

Retain every original unit, contact application, positive force magnitude,
full star, mean, physical circle corner and individual nonnegative circle
coefficient. Let the original radius satisfy

    2<R<=sqrt(1105)/16,
    D=sqrt(R^2-1/4)-1,
    Dlo=117/125<D<Dhi=61/60.                       (1)

In a nine-unit caller, the lower radius bound is supplied entirely by the
printed measure argument in `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`
Sections 1--3, `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md` Sections
2--6, and `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md` Section 3. Their
mass is 8997/1000<9, and each actual contained open unit square has mass
at least one. No checking program is a premise. The lower rational
comparison in (1) follows from
`15/4-(242/125)^2=119/62500>0`; the upper follows by squaring the two
positive sides of `sqrt(1041)/16<121/60`.

Use an oriented orthonormal frame `(d0,n)`, with origin unchanged. The
actual radial endpoint C is

    C=[-1/2,1/2]*d0+[-D-1,-D]*n.

Its original exterior contact is at `Q_C=(chi,-D)`, with
`-1/2<chi<1/2`, and its original exterior force is `-P_C*n`, `P_C>0`.
Both of its physical circle vertices and both original coefficients are
retained. Its other original contact is the side channel at

    U=(-1/2,-D).

The actual other endpoint B has a unique physical circle corner and owns
the normal

    f=(-a,b), w=Jrot(f)=(-b,-a),
    q=b/a>=0, P=sqrt(1+q^2), a=1/P, b=q/P.

At its genuine original side port Q its actual unit is

    B=Q+[0,1]*f+[-(1-beta),beta]*w,
    0<beta<1,
    T=Q+beta*w, T-U=u, |u|=1.

The unchanged channel direction lies strictly between n and f. Put

    u=(-y,x)=(-sin(theta),cos(theta)),
    Theta=pi/2-atan(q), 0<theta<Theta,
    delta=Theta-theta.

Normalize all original force magnitudes by the same positive factor so
that the exterior force at B is `P*f=(-1,q)`. Write the positive channel
magnitude as ell. Thus the full original B2 force is

    P*f+ell*u=kappa*Z_B, kappa>0,
    Z_B=T+f-w.                                    (2)

The radial C2 channel force is `-ell*u`. These are premises about the
original true2 stars, not a reduction of a larger star. A caller with
extra forces at B, C or the transmitter must first justify this exact
entry and cannot discard those forces.

The sum of the two exterior forces is `(-1,q-P_C)`. Define the unchanged
opposite resultant and its slope by

    F=(1,z), z=P_C-q.                             (3)

**Theorem 1.1.** Every actual configuration in this entire chart satisfies

    z>3/4.                                       (4)

The frame, direction of F and force normalization in a caller must be
identified literally. This is not a claim about an arbitrarily chosen
component ratio.

## 2. Whole angular range and the two-circle identity

Put

    c=(1+q)/P, d=(1-q)/P.

Here c,d are scalars; d is distinct from the frame vector d0. Taking the
full original B torque about its unique physical circle corner gives

    P*(1-beta)=ell*(sin(delta)-cos(delta)).

Consequently `delta>pi/4`, `q<1`, and

    0<theta<Theta-pi/4.                           (5)

The actual circle corner in (2) is

    Z_B=(-1/2-y-d,-D+x+c).

Subtracting its circle equation from
`R^2=(D+1)^2+1/4` gives exactly

    D=F_q(theta)
      =[2+d+2*c*x+(1+2*d)*y]/[2*(1+c+x)].         (6)

Sections 2--3 of
`TYPE_II_FAR_RETURN_RADIAL_UNIQUE_ANGLE_AND_ROOF_SLOPE_HAND_REDUCTION_2026_10_31.md`
prove, from precisely (2),(5),(6), that F_q is strictly increasing on
`[0,Theta-pi/4]` and that `q>=1/3` would force `D<117/125`.
These are local hand identities and inequalities, independent of the
far-return caller in that source. The formulas remain valid at the
closed comparison q=0, where Theta=pi/2; the exclusion of q>=1/3 needs
no q=0 endpoint argument. Thus the entire actual domain has

    0<=q<1/3.                                    (7)

No endpoint in (5) is promoted to a new original contact mean.

## 3. The full endpoint moments give the exact slope to be bounded

Define

    h=D*y+x/2,
    K=d*x-c*y=sin(delta)-cos(delta),
    E=h+K=(1/2+d)*x+(D-c)*y,
    G=P-D-q/2+x-q*y.

Both h and K are positive on the actual domain; K may be zero only at
the scalar comparison endpoint `theta=Theta-pi/4`. Taking the determinant
of (2) with Z_B gives the exact full force identity

    ell=G/E.

Every original circle force has zero moment about the original origin.
The full C2 origin moment, including all its original radial-circle
coefficients, is therefore

    P_C*chi=ell*h=:M,
    M=G*h/E.                                     (8)

In particular `chi>0`. Its genuine side-interior upper bound `chi<1/2`
then gives

    z=P_C-q>2*M-q.                               (9)

We shall prove `2*M-q>3/4` on the full circle domain. No equality of
C's two circle weights, replacement of chi by an endpoint, or equation
at an exterior neighbor is used.

## 4. Two continuous derivative comparisons over the enlarged domain

For this section allow the closed comparison ranges

    Dlo<=D<=Dhi, 0<=q<=1/3,
    0<theta<=Theta-pi/4.

All comparison denominators are positive. In fact
`x-q*y=P*sin(delta)>=P/sqrt(2)`, and therefore

    G>=P*(1+1/sqrt(2))-D-q/2
      >1+7/10-61/60-1/6=31/60>0.                (10)

First M strictly decreases with D at fixed q,theta. Direct differentiation
of (8) gives

    E^2*M_D=-h^2+K*(G*y-h).

Since `P<16/15`, `D>=117/125` and `x<=1`,

    G*y-h
      =y*(P-2*D-q/2+x-q*y)-x/2
      <y/5-x/2<0.

The penultimate comparison uses
`16/15-234/125+1=73/375<1/5`; the final one uses `y<=x`.
Thus

    M_D<0.                                       (11)

Second M strictly increases with theta at fixed D,q. Put

    A=x-q*y>0, J=y+q*x>0, K0=D*d+c/2>0.

One has

    h_theta=D*x-y/2>=(D-1/2)*x>0,
    h_theta*E-h*E_theta=K0,
    E^2*M_theta=N=G*K0-J*h*E,
    N_theta=-2*J*h_theta*E-A*h*E<0.              (12)

The last identity follows by differentiating N and using the preceding
Wronskian identity, so it does not assume the sign it proves. N is
smallest at `theta=Theta-pi/4`. There

    x=c/sqrt(2), y=d/sqrt(2),
    h=E=K0/sqrt(2), J=P/sqrt(2),
    Gend=P*(1+1/sqrt(2))-D-q/2,
    Nend=K0*[Gend-P*K0/(2*sqrt(2))],
    P*K0=D*(1-q)+(1+q)/2.

In the bracket, first use `P>=1`, then `D<=61/60`. The resulting affine
function of q decreases because its q coefficient is
`-1/2+(61/60-1/2)/(2*sqrt(2))<0`. At q=1/3 it is

    (59/sqrt(2)-33)/180>83/1800>0.              (13)

Here `1/sqrt(2)>7/10`. Thus N>0 over the entire enlarged domain and

    M_theta>0.                                  (14)

These are partial derivative comparisons on a rectangle with a varying
upper angular bound. They are not derivatives along the circle curve.
Each use below keeps its comparison angle within every relevant interval.

For fixed D,theta one also has

    G_q=q/P-1/2-y<0,
    E_q=-[(1+q)*x+(1-q)*y]/P^3<0.               (15)

Consequently on a q interval `[q_l,q_h]`, at one fixed comparison angle,
the numerator G can be bounded below at q_h and the denominator E above
at q_l. The factor h does not depend on q.

## 5. Seven lower angles, each justified on its whole interval

Every terminating decimal below denotes the displayed exact rational.
The seven q intervals cover [0,1/3]. For each row let
`theta_l=asin(y_l)`. The table gives positive square-root comparisons

    P_l<=sqrt(1+q_l^2), P_h<sqrt(1+q_h^2),
    x_m<=sqrt(1-y_l^2)<=x_p.

The equality P_l=1 at q_l=0 and the exact cosine .96 at y_l=.28 are
intentional. All other bounds follow by squaring the two positive sides.

| q_l | q_h | y_l | P_l | P_h | x_m | x_p |
|---|---|---|---|---|---|---|
| 0 | 1/20 | .200 | 1 | 1.0012 | .9797 | .9798 |
| 1/20 | 1/10 | .230 | 1.0012 | 1.0049 | .9731 | .9732 |
| 1/10 | 3/20 | .250 | 1.0049 | 1.0111 | .9682 | .9683 |
| 3/20 | 1/5 | .280 | 1.0111 | 1.0198 | .9600 | .9600 |
| 1/5 | 1/4 | .325 | 1.0198 | 1.0307 | .9457 | .9458 |
| 1/4 | 3/10 | .360 | 1.0307 | 1.0440 | .9329 | .9330 |
| 3/10 | 1/3 | .410 | 1.0440 | 1.0540 | .9120 | .9121 |

Each comparison angle lies in every relevant angular range because
`y_l<=.41<1/sqrt(5)`, the latter being the sine of the smallest upper
angle `Theta(1/3)-pi/4`.

To prove that every actual theta in a row exceeds theta_l, rewrite
`F_q(theta_l)<Dlo` using (6). After multiplying by its positive
denominator, it is equivalent to

    Jcirc(q,x,y)
      =P*[Dlo*(1+x)-1-y/2]
         +(1+q)*(Dlo-x)-(1-q)*(1/2+y)>0.         (16)

The bracket multiplying P is positive at all these comparison angles.
For fixed x,y its q derivative is positive: its first term is
`(q/P)*[Dlo*(1+x)-1-y/2]>=0`, and the remaining term is
`Dlo-x+1/2+y>0`. The x coefficient is
`Dlo*P-(1+q)<0`. A valid rowwise lower bound is therefore

    J_l=P_l*[Dlo*(1+x_p)-1-y_l/2]
         +(1+q_l)*(Dlo-x_p)-(1-q_l)*(1/2+y_l).

Here are the complete exact rational products, with a convenient smaller
positive reserve in the last column:

| Row | J_l, exactly | Strictly greater than |
|---|---|---|
| 1 | .0092928 | 9/1000 |
| 2 | .00023349824 | 1/5000 |
| 3 | .01031371112 | 1/100 |
| 4 | .011669616 | 1/100 |
| 5 | .00005242224 | 1/20000 |
| 6 | .0073571416 | 7/1000 |
| 7 | .0045235264 | 1/250 |

Thus `F_q(theta_l)<Dlo<D=F_q(theta)` for every q in its complete row.
The strict monotonicity of F_q proves

    theta>theta_l.                               (17)

This establishes the angular lower bounds independently of the slope
comparisons; no sampled or estimated solution of (6) is used.

## 6. The endpoint comparisons and their rational reserves

Apply (11), then (14),(17), and finally the separate numerator and
denominator comparisons (15). They give for the entire row

    M(D,q,theta)
      >G(Dhi,q_h,theta_l)*h(Dhi,theta_l)
                                  /E(Dhi,q_l,theta_l).

To display every numerical comparison without a hidden radical, define

    g=60*P_h-61-30*q_h+60*x_m-60*q_h*y_l,
    h60=61*y_l+30*x_m,
    E60=P_l*(61*y_l+30*x_p)
                 +60*(1-q_l)*x_p-60*(1+q_l)*y_l.

Then `G(Dhi,q_h,theta_l)>=g/60` and
`h(Dhi,theta_l)>=h60/60`. For E, note that
`(1-q_l)*x-(1+q_l)*y_l>0`, since theta_l is strictly below its upper
angle. Replacing its positive divisor P by the lower bound P_l, and
then x by x_p, gives

    E(Dhi,q_l,theta_l)<=E60/(60*P_l).

All of g,h60,E60 are positive in the following table. Therefore

    2*M-q-3/4
       >[2*g*h60*P_l-60*(q_h+3/4)*E60]/(60*E60).

Denote the numerator on the right by Ftilde. Its complete exact products
are:

| Row | g | h60 | E60 | Ftilde, exactly | Strictly greater than |
|---|---|---|---|---|---|
| 1 | 55.754 | 41.591 | 88.382 | 395.393228 | 395 |
| 2 | 53.300 | 43.223 | 84.2602712 | 315.82705496 | 315 |
| 3 | 51.008 | 44.296 | 80.3042651 | 204.6130342064 | 204 |
| 4 | 48.428 | 45.880 | 76.029268 | 159.410665408 | 159 |
| 5 | 45.209 | 48.196 | 71.1517402 | 174.9656773744 | 174 |
| 6 | 42.134 | 49.947 | 66.468465 | 150.6347685372 | 150 |
| 7 | 38.760 | 52.370 | 61.005612 | 272.9854056 | 272 |

These are direct rational additions and multiplications of the preceding
table. For example row 1 has
`2*55.754*41.591-48*88.382=395.393228`; the printed formulas specify
every operation in every other row. The strict reserves prove

    2*M-q>3/4

over all seven continuous intervals. Equation (9) now proves (4).

## 7. Scope of the completed theorem

The theorem retains the original true2 radial and unique endpoint stars,
the actual side-channel geometry, genuine exterior side applications,
all physical circle corners and every original circle coefficient.
The radial endpoint's transverse application is constrained by its full
moment and remains its original mean throughout. The two exterior
neighbors may have arbitrary unchanged degrees; no equation at them was
used. A parallel channel endpoint, where the asserted U may cease to be
the actual application, requires its own literal limiting-side argument
and is not silently included in the strict chart of Section 1.

The seven-row table proves bounds on complete intervals by hand
derivatives and rational arithmetic. It is not a configuration table,
computer-generated exclusion, or substitute for a full-star hypothesis.
No Lean or CI is involved. This reusable inequality changes no original
fine-row flag by itself.
