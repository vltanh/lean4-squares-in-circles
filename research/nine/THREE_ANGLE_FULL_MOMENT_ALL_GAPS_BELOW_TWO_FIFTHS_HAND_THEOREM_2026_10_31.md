# All three full-moment contact gaps are strictly below two fifths

Date: October 31, 2026 UTC.

**Status: complete hand scalar theorem, with a literal all-mask A-only application.** This strengthens the earlier simultaneous one-half gap bound. One choice of the largest gap, one monotone comparison in the other two angles, and three short rational rows plus a concave cubic prove the entire continuous domain. No pose cover or external calculation is a proof premise.

## 1. The generic theorem

Let A,B,C belong to (pi/4,pi/2), with A+B+C=pi. Suppose lambda>0, all three numbers

    g_A=1-lambda*sin(A),
    g_B=1-lambda*sin(B),
    g_C=1-lambda*sin(C)

are positive, and the exact full-moment identity is

    g_A*g_B*g_C
      =(sin(A)-cos(A))*(sin(B)-cos(B))*(sin(C)-cos(C)).  (1)

Then, simultaneously,

    0<g_A,g_B,g_C<2/5.                                (2)

The names in this scalar statement are angles, not physical squares.

## 2. Reduce the largest gap to a symmetric comparison

If (2) were false, choose a largest gap and call its angle A. Sine is increasing on the stipulated angle interval, so A is a smallest angle. Therefore

    pi/4<A<=pi/3, g_A>=2/5,
    lambda<=lambda0:=3/(5*sin(A))<1.

All factors at lambda0 are positive. Their product decreases strictly with lambda while positive. Equation (1) consequently implies

    (2/5)*(1-lambda0*sin(B))*(1-lambda0*sin(C))
      <=(sin(A)-cos(A))*(sin(B)-cos(B))*(sin(C)-cos(C)). (3)

Set

    z=sin(A/2), h=cos(A/2), y=cos((B-C)/2),
    delta=sin(A)-cos(A)>0.

Then 0<y<=1, and the elementary sum/product identities give

    sin(B)+sin(C)=2*h*y,
    sin(B)*sin(C)=y^2-z^2,
    (sin(B)-cos(B))*(sin(C)-cos(C))=2*y^2-1-sin(A).

Thus the left side minus right side of (3) is

    F(y)=(2/5)*(1-2*lambda0*h*y+lambda0^2*(y^2-z^2))
              -delta*(2*y^2-1-sin(A)).                 (4)

We have lambda0<h. Indeed

    sin(A)*cos(A/2)>=(1/sqrt(2))*(sqrt(3)/2)
                       =sqrt(6)/4>3/5,

where the last positive squared comparison is 6/16>9/25. Now

    F'(y)=2*((2/5)*lambda0^2-2*delta)*y
                    -(4/5)*lambda0*h<0

for 0<y<=1. If the first coefficient is nonpositive this is immediate. Otherwise use y<=1 and discard the negative -2*delta contribution to bound the derivative above by

    (4/5)*lambda0*(lambda0-h)<0.

Therefore F(y)>=F(1). It suffices to prove F(1)>0; this would contradict (3). No actual angles have been replaced: y=1 is solely a scalar lower comparison.

## 3. A single half-angle interval

Put x=sqrt(1-z^2). Since pi/4<A<=pi/3,

    sin(pi/8)<z<=1/2,
    z>3/8.

For the second inequality, sin(pi/8)^2=(2-sqrt(2))/4>9/64 follows from sqrt(2)<23/16.

At the symmetric comparison B=C=(pi-A)/2, formula (4) becomes

    F(1)=L(z)-D(z)*H(z),
    L(z)=(2/5)*(1-3/(10*z))^2,
    D(z)=2*z*x+2*z^2-1,
    H(z)=1-2*z*x.                                  (5)

Both D,H are positive on this interval. L and D increase with z; H decreases. For D this follows equally from D=sin(A)-cos(A) and A=2*asin(z). For H, differentiate z*sqrt(1-z^2), whose derivative is positive for z<=1/2.

Here is the complete lower-interval comparison table. Every terminating decimal denotes an exact rational.

| z interval | Lower bound for L | Upper bound for D | Upper bound for H | Strict positive comparison |
| --- | --- | --- | --- | --- |
| sin(pi/8)<z<=2/5 | L>2/125 | D<4/75 | H<3/10 | D*H<2/125<L |
| 2/5<=z<=41/100 | L>=1/40 | D<17/200 | H<27/100 | D*H<459/20000<1/40 |
| 41/100<=z<=5/12 | L>=242/8405 | D<1/9 | H<51/200 | D*H<17/600<242/8405 |

The entries have the following direct checks.

* First row: L increases and z>3/8. At z=2/5, x=sqrt(21)/5<11/12, with squared reserve 121/144-21/25=1/3600. Hence D<11/15+8/25-1=4/75. Also H=1-sin(A)<1-1/sqrt(2)<3/10.
* Second row: at z=41/100, x<913/1000 because .913^2=.833569>.8319. Thus D<.82*.913+2*.41^2-1=.08486<17/200. At z=2/5, x>73/80 because 21/25>(73/80)^2; hence H<1-(4/5)*(73/80)=27/100. The positive reserve 1/40-459/20000 is 41/20000.
* Third row: at z=5/12, x=sqrt(119)/12<11/12. Thus D<55/72+25/72-1=1/9. At z=41/100, x>91/100 because .91^2=.8281<.8319, so H<1-.82*.91=.2538<51/200. Finally 242*600-17*8405=2315>0.

Monotonicity proves each entry throughout its whole interval, not merely at its endpoint. The table includes both joining endpoints.

## 4. The remaining interval is one concave-cubic comparison

Let 5/12<=z<=1/2. From (5),

    D(z)=2*z^2-H(z),
    D(z)*H(z)=z^4-(H(z)-z^2)^2<=z^4.             (6)

The cubic

    J(z)=10*z-3-16*z^3

is concave, since J''(z)=-96*z<0. At its two endpoints,

    J(5/12)=1/108>0, J(1/2)=0.

It follows that J(z)>=0 on the entire closed interval. Since z>0,

    (10*z-3)^2>=256*z^6>250*z^6,
    L(z)=(10*z-3)^2/(250*z^2)>z^4.              (7)

Equations (6)--(7) prove F(1)>0 on the remaining interval, including z=1/2. Together with Section 3, this contradicts (3) in every possible largest-gap case and proves (2).

## 5. Literal A-only application

Retain every original unit, positive force and complete moment, normal, physical application and mean, physical circle corner and individual coefficient in the unique-V A-only side chart. The full positive stars remain A3,D3,V2,B2,C2,N2. Use

    alpha,beta>pi/4,
    pi/2<alpha+beta<2*pi/3,
    H=sin(alpha+beta), k=-cos(alpha+beta), p=H-k,
    s=sin(alpha), c=cos(alpha), S=sin(beta), C=cos(beta),
    u=1-omega*S/H,
    t=1-omega*s/H,
    w=1-omega,
    0<u,t,w<1.

The exact three full moments are

    rho*u=mu*(s-c),
    nu*t=rho*p,
    mu*w=nu*(S-C), mu,nu,rho>0.

Multiplication, cancelling only the positive product mu*nu*rho, gives

    u*t*w=(s-c)*(S-C)*p.

Set gamma=pi-alpha-beta and lambda=omega/H. The three angles alpha,beta,gamma all lie in (pi/4,pi/2), their sum is pi, and

    t=1-lambda*sin(alpha),
    u=1-lambda*sin(beta),
    w=1-lambda*sin(gamma),
    p=sin(gamma)-cos(gamma).

The theorem applies literally and proves

    0<u,t,1-omega<2/5                             (8)

for every physical endpoint mask and every original angle. The exact input identities are in `TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md`, Sections 1--2, and `FULL_A_ONLY_HUB_MOMENTS_FORCE_STRICT_CONTACT_SUM_BOUND_2026_10_29.md`, Sections 1 and 5. The high-angle entry is the complete hand theorem `TYPE_II_A_ONLY_ENTIRE_HIGH_ANGLE_SIDE_EXCLUSION_BY_ORIGINAL_SUPPORT_WIDTH_2026_10_29.md`.

This is a simultaneous full-domain theorem, not a claim that the A-only physical family is already excluded. It uses no endpoint-circle equation or radius and can be used by any larger caller establishing exactly the same full-moment identity. No original ledger flag is changed. No Lean, CI, generated exclusion table or external mathematical calculation is used as a proof premise.
