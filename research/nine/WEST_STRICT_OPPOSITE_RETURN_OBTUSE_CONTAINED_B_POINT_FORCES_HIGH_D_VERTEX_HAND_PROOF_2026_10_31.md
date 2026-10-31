# The actual contained B point forces the opposite D exterior vertex beyond radius 5/4

Date: October 31, 2026 UTC.

**Status: complete hand theorem for the whole stated closed obtuse
opposite-return chart.** The actual original point K+b_ext forces
t+u>123/100. Consequently the actual exterior D vertex
J=(d-v,-t-u) has norm strictly greater than 5/4. The proof uses
continuous monotonicity and three explicit hand comparison intervals;
it does not use a generated parameter cover or a sampled pose.

## 1. Exact original scope and all retained data

Retain all nine actual squares, unchanged disk and origin, all original
positive forces and selected normals, common applications, full means,
physical circle masks and every individual nonnegative circle weight.
The original component is the West/strict A-owned perpendicular
singleton with the opposite D-vertex return, on
A--V--D--C--N--B--A and its positive AD chord.

Use the hand chart and whole closed-obtuse consequences of

    WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md,
    WEST_STRICT_OPPOSITE_RETURN_OBTUSE_ANGLE_AND_ACTUAL_POINT_MONOTONICITY_2026_10_31.md,
    WEST_STRICT_OPPOSITE_RETURN_OBTUSE_RADIAL_MASKS_AND_COMPLETE_DIAGONAL_HAND_EXCLUSION_2026_10_31.md.

The particular consequences needed here are

    P=(d,1/2), Q=(d,-t), H=t+1/2 in (1/2,1],
    R^2<=1105/256, 117/125<d<61/60,
    h=(c,-s), e=(s,c), c^2+s^2=1,
    alpha=atan(s/c), c>3/4, 1/5<s<2/3,
    a^2+b^2=1, 0<b<2/5,
    theta=alpha+atan(b/a),
    u=cos(theta)=a*c-b*s,
    v=sin(theta)=a*s+b*c,
    8/15<v<1/sqrt(2),
    0<alpha<theta<pi/4,
    x=1-a+H*s, y=1-H*c+b, 0<x,y<1,
    m=x/y, p=sqrt(1+m^2),
    K=P-h+y*e,
    b_ext=(-m*h+e)/p.                            (1)

The original closed obtuse aperture gives

    m>=(s+q)/c>s/c,
    gamma=atan(m)-alpha in (0,pi/2).             (2)

The original owner at K is B, and K is an actual relative-interior
point of its minimum-b_ext side. Hence

    K+b_ext belongs to the same actual B,
    |K+b_ext|<=R.                                (3)

No physical B circle-mask distinction, N application, endpoint force
deletion or additional degree-two assumption at B is needed for (3).
All original force and torque equations remain in place. The hand
all-nine radius-two measure proof in the entry sources supplies the
stated lower bound on d; no generated measure certificate is used.

The exact actual D is

    D=Q+[0,1]*(-u,v)+[0,1]*(-v,-u).

Its exterior vertex between the opposite ports Q,L is

    J=Q+(-v,-u)=(d-v,-t-u).                     (4)

We prove the stronger scalar statement

    t+u>123/100.                                 (5)

## 2. A scalar height comparison reduces a shallow D to a fixed formula

Suppose, for contradiction, that t+u<=123/100. Set

    L0=173/100, H_*=L0-u>=H,
    w=L0-u-v.

Keep the original alpha,theta,a,b fixed and increase only the
auxiliary scalar H from its actual value to H_*. No auxiliary
square or physical packing is asserted. At the terminal scalar,

    x_*=1-u*c+w*s,
    y_*=1-u*s-w*c.                               (6)

Write x,y for these terminal quantities through Sections 3--7;
they are auxiliary numbers, not altered original applications.
Set

    R0=sqrt(x^2+y^2), kappa=atan(x/y),
    gamma_*=kappa-alpha,
    Y_*=1/2+s+c*y+cos(gamma_*).                  (7)

We will prove Y_*>52/25.

Put

    theta0=asin(8/15), u0=sqrt(161)/15,
    w0=L0-u0-8/15=359/300-u0.

The following elementary positive radical bounds will be used:

    8459/10000<u0<423/500<17/20,
    7/20<w0<351/1000,
    3/10<w<=w0<351/1000.                         (8)

The first lower squared comparison has numerator reserve
161*100000000-225*8459^2=196775>0. The upper u0 bound
is the hand entry's strict radical comparison. The bounds on w0
then follow directly from w0=359/300-u0. The function
cos(theta)+sin(theta) increases up to pi/4; hence w<=w0.
Also w>=L0-sqrt(2)>3/10, using sqrt(2)<143/100.

All auxiliary x,y are strictly positive on the enlarged angle
rectangle alpha in [asin(1/5),pi/4], theta in [theta0,pi/4].
Indeed x>1-u>3/20, and, using s<3/4,c<=1,

    y>1-(17/20)*(3/4)-351/1000=23/2000>0.        (9)

We also have gamma_*>0 throughout this enlarged rectangle.
Put r0=c+s and z0=c-s, so z0>=0, r0^2+z0^2=2. Then

    F:=c*x-s*y
       =z0-u*cos(2*alpha)+w*sin(2*alpha)
       >z0*(1-17*r0/20)+(3/10)*(r0^2-1)>0.      (10)

For the last sign, if 1-17*r0/20>=0 it is immediate.
Otherwise use z0<=1 to bound the expression below by

    (3/10)*r0^2-(17/20)*r0+7/10
      =(3/10)*(r0-17/12)^2+47/480>0.

Since c*y+s*x>0, (10) gives 0<gamma_*<pi/2.

For the original fixed alpha,a,b and auxiliary H parameter,
the ordinary height of the point in (3) has the exact form

    Y(H)=1/2+s+c*y(H)+cos(gamma(H)),
    dY/dH=-c^2-sin(gamma(H))*(s*y+c*x)/(x^2+y^2)<0.    (11)

Here y stays positive up to the terminal value (9), x stays
positive, and atan(x/y) increases with H. Thus (2) keeps
gamma(H)>0 along the entire scalar interval. Formula (11)
therefore yields the justified one-sided comparison

    (K+b_ext)_Y=Y(H)>=Y(H_*)=Y_*.                (12)

In particular H_*>1 causes no physical or root-selection assertion;
it is only the explicit scalar endpoint in (11).

## 3. Three whole-interval lower bounds for the contact-point height

Put Y_K=1/2+s+c*y at the terminal scalar. Holding theta
fixed, direct differentiation of (6) gives

    x_alpha=1-y, y_alpha=x-1,
    (Y_K)_alpha=c*x-s*y=F>0.                    (13)

Holding alpha fixed instead gives

    y_theta=v*s+(u-v)*c>0,
    (Y_K)_theta=c*y_theta>0.                    (14)

Thus a lower bound on a whole alpha interval is obtained at
theta=theta0 and its left alpha endpoint. The following are
strict rational comparisons. In each row use u0<423/500,
w0<351/1000 and the displayed lower bound for c. The identity
being bounded is

    Y_K=1/2+s+c*(1-u0*s)-w0*(1-s^2).

| Actual s interval | Comparison s | Lower c bound | Resulting lower Y_K | Convenient consequence |
| --- | ---: | ---: | ---: | ---: |
| 1/5<s<=3/10 | 1/5 | 39/40 | 117307/100000 | Y_K>117/100 |
| 3/10<=s<=9/20 | 3/10 | 953/1000 | 5958593/5000000 | Y_K>119/100 |
| 9/20<=s<2/3 | 9/20 | 89/100 | 2442509/2000000 | Y_K>61/50 |

For example the first row is exactly

    7/10+(39/40)*(2077/2500)
              -(351/1000)*(24/25)=117307/100000.

The other two rows are, respectively,

    4/5+(953/1000)*(3731/5000)
              -(351/1000)*(91/100)=5958593/5000000,
    19/20+(89/100)*(6193/10000)
              -(351/1000)*(319/400)=2442509/2000000.

The three lower c comparisons follow by positive squaring of
sqrt(24)/5, sqrt(91)/10, and sqrt(319)/20. Equations
(13)--(14) justify every interior point of each interval.

## 4. Reduce the complete auxiliary angle maximum to four boundaries

For fixed alpha define

    Dtheta=x*y_theta-y*x_theta
       =u*(c+s)+v*(L0-2*c)-1.                  (15)

Its derivative is strictly negative:

    (Dtheta)_theta=-v*(c+s)+u*(L0-2*c)
       <-8/15+33/100<0.                         (16)

Here c>=1/sqrt(2)>7/10 and c+s>1. If L0-2c is
negative, its contribution is already negative; otherwise u<=1
gives the displayed upper bound. Since

    (gamma_*)_theta=-Dtheta/R0^2,

an interior stationary point as theta increases can only be a
minimum. Hence every maximum over the original allowed interval
occurs at one of its endpoints

    max(theta0,alpha)<=theta<=min(pi/4,alpha+psi0),
    psi0=asin(2/5).                              (17)

These inequalities preserve the original b=sin(theta-alpha)<2/5;
the closed endpoints in (17) are only scalar comparisons.
It remains to compare four boundary curves:

    theta=theta0, theta=alpha,
    theta=pi/4, theta=alpha+psi0.                 (18)

Let alpha1=asin(3/10), alpha2=asin(9/20), and
alpha_c=pi/4-psi0. Their order is

    asin(1/5)<alpha1<alpha_c<alpha2<theta0<pi/4.

Indeed 1/3<sin(alpha_c)<3/8 follows from
sin(alpha_c)=(sqrt(21)/5-2/5)/sqrt(2), using
9/10<sqrt(21)/5<23/25 and 7/5<sqrt(2)<3/2.
The other comparisons are direct comparisons of positive sines.

### 4.1. The theta0 boundary increases with alpha

On this boundary put C0=u0^2+w0^2<17/20. The identities

    x+y=(R0^2+2-C0)/2,
    (gamma_*)_alpha=(2-C0-3*R0^2)/(2*R0^2)       (19)

follow directly from (6). Also R0^2 is convex in alpha, since
its second derivative is 2[u0(c+s)+w0(c-s)]>0.

At alpha=asin(1/5), bounds u0>169/200, w0>7/20,
c>39/40 and (8) give x<1/4 and y<1/2. Thus
R0^2<5/16. At alpha=theta0, H0=L0-u0 satisfies
221/250<H0<177/200, and

    x=H0*(8/15)<19/40,
    y=1-H0*u0<13/50.

Their squared sum is less than 5/16, with rational reserve
771/40000. Convexity gives R0^2<5/16 on the whole intervening
alpha interval. Equation (19) now makes gamma_* strictly
increasing there, since 2-17/20-15/16=17/80>0.

### 4.2. The b=2/5 boundary increases with alpha

Here a0=sqrt(21)/5, b0=2/5, theta=alpha+psi0 and
H_*=L0-cos(theta). Its relevant interval is
asin(1/5)<=alpha<=alpha_c. Direct differentiation gives

    R0^2*(gamma_*)_alpha
      =H_*[3(c-s+v)-2H_*]
          +v*(c+s-u)-(3-2*a0+2*b0).             (20)

Use 9/10<a0<23/25, so 3-2a0+2b0<2 and
1-a0>2/25. The full interval splits as follows.

If s<=3/10, then c>19/20, 9/10<H_*<1, and

    c-s+v=(1+b0)c-(1-a0)s>13/10,
    v>14/25,
    c+s-u=(1-a0)c+(1+b0)s>89/250.

The concave expression H_*(39/10-2H_*) is greater than
189/100 on [9/10,1]. Equation (20) is therefore greater
than

    189/100+(14/25)*(89/250)-2=1117/12500>0.

If s>=3/10, still on this boundary, then s<3/8 and
c>23/25. The latter follows from
cos(alpha_c)^2=1/2+(2/5)a0>43/50>(23/25)^2.
Also 19/20<H_*<21/20, and

    c-s+v>5/4,
    v>63/100,
    c+s-u>49/100.

The concave expression H_*(15/4-2H_*) is at least
693/400 on [19/20,21/20]. Thus (20) exceeds

    693/400+(63/100)*(49/100)-2=103/2500>0.

For clarity, the H_* bounds used here are scalar bounds on this
fixed b0 curve: in the first range
u<a0*(49/50)-(2/5)*(1/5)<83/100 and
u>(9/10)*(19/20)-(2/5)*(3/10)>73/100.
In the second, u<(23/25)*(24/25)-(2/5)*(3/10)<39/50,
whereas u>=1/sqrt(2)>7/10. These imply all the displayed
H_* intervals without imposing the original full torque there.

This proves strict increase along the entire b0 boundary,
including its joining s=3/10 endpoint.

### 4.3. The pi/4 boundary increases up to alpha2 and has a global coarse angle bound

Put sigma=1/sqrt(2), w45=L0-sqrt(2), and
k0=sqrt(2)*L0-2. Exact radical comparisons give

    11/25<k0<9/20,
    C45=sigma^2+w45^2<61/100.                    (21)

For the first pair, use 1413/1000<sqrt(2)<99/70;
for the second use 7/5<sqrt(2)<71/50.

On alpha_c<=alpha<=alpha2 put phi=pi/4-alpha.
Here

    R0^2=2+C45-2[cos(phi)+k0*sin(phi)].

The bracket is concave in phi and exceeds 27/25 at both
endpoints. At phi=psi0 use sqrt(21)/5>91/100 and
k0>11/25. At phi=pi/4-alpha2, use c2=sqrt(319)/20>89/100,
sqrt(2)<71/50 and k0>11/25 to get

    cos(phi)+k0*sin(phi)
       >67/71+(11/25)*(22/71)=27/25.

Thus R0^2<9/20. The analogue of (19), with C45 in place
of C0, proves that gamma_* increases with alpha on this
whole interval, since 2-61/100-27/20>0.

We also need one bound on the entire pi/4 boundary. Let
f=sin(phi), g=cos(phi), so 0<=f<=2/5 and g>9/10.
Direct substitution in (6) gives

    tan(gamma_*)=N45/D45,
    N45=k0+2*f[(1-g)-k0*f],
    D45=1+2*g[(1-g)-k0*f].                       (22)

If f>0 then (1-g)/f=f/(1+g)<4/19<k0; at f=0
the same bracket is zero. Hence N45<=k0<9/20.
Using 1-g=f^2/(1+g)>=f^2/2 and 2k0<9/10 gives

    D45>=1+g*(f^2-2*k0*f)>4/5.

Indeed f^2-(9/10)f>=-1/5 on [0,2/5], and
multiplication of a negative number by 0<g<=1 can only
increase it. At f=0, D45=1. Therefore

    tan(gamma_*)<9/16<7/12                       (23)

throughout the whole relevant pi/4 boundary.

### 4.4. The theta=alpha boundary decreases after theta0

Here b=0,a=1,H_*=L0-c and

    x=H_*s, y=1-H_*c.

Direct differentiation along this boundary gives

    R0^2*(gamma_*)_alpha
       =-(3c-2L0)*(2c-L0)<0.                   (24)

Both factors are negative because alpha>=theta0 implies
c<=u0<423/500<L0/2. Thus its maximum is at alpha=theta0.
The closed b=0 comparison is not asserted to be a physical
original port.

## 5. Four explicit endpoint comparisons and one exact linear reserve

Equations (15)--(24) reduce the desired angle bounds to the
following finite hand comparisons, all at fixed endpoint constants.
Let F=cx-sy and N=sx+cy>0, so tan(gamma_*)=F/N.
For a proposed rational k,

    F-kN=(c-k*s)*x-(s+k*c)*y.                   (25)

Every number in the next table is a strict rational bound in its
stated direction. The last column is the resulting upper bound
in (25).

| Boundary and comparison s | k | Upper x | Lower y | Upper c-ks | Lower s+kc | Upper F-kN |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| theta=theta0, s=3/10 | 2/5 | 3/10 | 2/5 | 22/25 | 17/25 | -1/125 |
| b=2/5, s=3/10 | 2/5 | 377/1000 | 117/250 | 167/200 | 17/25 | -689/200000 |
| theta=theta0, s=9/20 | 1/2 | 403/1000 | 61/200 | 67/100 | 179/200 | -593/200000 |
| theta=pi/4, s=9/20 | 1/2 | 511/1000 | 39/100 | 67/100 | 179/200 | -167/25000 |

Here are explicit checks of the table's only radical substitutions.
In addition to (8), use

    953/1000<sqrt(91)/10<477/500,
    893/1000<sqrt(319)/20<447/500,
    1833/2000<sqrt(21)/5<23/25,
    707/1000<sigma<177/250,
    31/100<w45<79/250.                           (26)

Each follows by positive squaring; for example the first lower
bound for sqrt(319)/20 has squared reserve 51/1000000,
and the lower bound 1833/2000 for sqrt(21)/5 has squared
reserve 111/4000000.

For the first row, (8), (26) give

    x<1-(8459/10000)*(953/1000)+(351/1000)*(3/10)<3/10,
    y>1-(423/500)*(3/10)-(351/1000)*(477/500)>2/5.

For the second row, H_*=37/20-a0*sqrt(91)/10 satisfies

    H_*<37/20-(1833/2000)*(953/1000)<4883/5000.

Thus x<1-1833/2000+(3/10)*(4883/5000)<377/1000 and
y>7/5-(4883/5000)*(477/500)>117/250.

For the third row,

    x<1-(8459/10000)*(893/1000)+(351/1000)*(9/20)<403/1000,
    y>1-(423/500)*(9/20)-(351/1000)*(447/500)>61/200.

For the fourth row,

    x<1-(707/1000)*(893/1000)+(79/250)*(9/20)<511/1000,
    y>1-(177/250)*(9/20)-(79/250)*(447/500)>39/100.

The coefficient bounds in the table follow immediately from (26).
Multiplying its rational columns gives the four printed negative
reserves; no interval enumeration is being invoked.

At the remaining corner theta=alpha=theta0, put H0=L0-u0.
Then

    F=(8/15)*[(173/50)*u0-547/225],
    N=(322/225)*u0-16781/22500.

The exact linear reserve is

    7N-12F=(232613-272840*u0)/22500>0,            (27)

because u0<423/500 and

    232613*500-272840*423=895180>0.

Thus tan(gamma_*)<7/12 at this corner as well.

## 6. The angle bounds cover every original alpha and theta

We record the complete joining argument, to make clear that the
four endpoint calculations do not omit an angular interior.

If s<=3/10, equation (17) has lower endpoint theta0 and
upper endpoint alpha+psi0. The theta0 curve increases by
Section 4.1, and the upper curve increases by Section 4.2.
The first two table rows therefore give

    tan(gamma_*)<2/5.                            (28)

If 3/10<=s<=9/20, the lower endpoint is still theta0 and
is bounded at alpha2 by Section 4.1. Before alpha_c the
upper endpoint is the increasing b=2/5 curve; after alpha_c
it is the increasing pi/4 curve from Section 4.3. These meet
at the same comparison point. The last two table rows give

    tan(gamma_*)<1/2.                            (29)

If s>=9/20, the upper endpoint is always pi/4 and obeys
(23). The lower endpoint first follows the increasing theta0
curve up to alpha=theta0 and then the decreasing theta=alpha
curve from (24). Its unique maximum is therefore the corner
in (27). Thus

    tan(gamma_*)<7/12.                           (30)

The no-interior-maximum theorem (15)--(17) transfers these
boundary bounds to every allowed original theta. All three
s ranges include their joining endpoints, and b=0 or b=2/5
was used only as an explicitly closed scalar comparison.

## 7. The actual contained point contradicts every shallow D

The positive cosine bounds from (28)--(30) are respectively

    cos(gamma_*)>5/sqrt(29)>23/25,
    cos(gamma_*)>2/sqrt(5)>89/100,
    cos(gamma_*)>12/sqrt(193)>43/50.              (31)

The final comparisons follow by positive squaring, with integer
numerator reserves 284,79,3143 after their respective common
denominators. Combining (31) with the whole-interval height
table in Section 3 gives, in the three ranges,

    Y_*>117/100+23/25=209/100>52/25,
    Y_*>119/100+89/100=52/25,
    Y_*>61/50+43/50=52/25.

Thus Y_*>52/25 throughout the whole assumed shallow domain.
But

    (52/25)^2-1105/256=1599/160000>0,

so the actual physical containment (3) says

    (K+b_ext)_Y<=R<52/25.

This contradicts (12). The assumption t+u<=123/100 is
therefore impossible, proving (5), including its equality case.

Finally v<1/sqrt(2)<177/250 and d>117/125 give

    d-v>57/250.

The unchanged actual exterior vertex (4) consequently satisfies

    |J|^2>(57/250)^2+(123/100)^2
           =25/16+149/62500>25/16.              (32)

This is the required full-domain exterior-vertex bound.

## 8. Scope and hand-proof boundary

The result uses the exact original A3/D3 chart, its closed obtuse
aperture, the already hand-proved whole-chart component and angle
bounds, and the actual contained point supplied by the genuine
B owner. Every original full force/torque equation, mean, physical
corner and zero individual coefficient is retained. No selected
auxiliary root of the hub torque is imposed.

The auxiliary H endpoint and all closed angular boundary curves
serve only the displayed one-sided scalar comparisons. They are
not candidate physical squares and are never substituted into
an original equilibrium equation. Every interior is covered by
the continuous derivative and convexity arguments above.

In particular (32) supplies the actual exterior-vertex premise
for a separate literal D-pocket geometric transfer. That transfer
must still verify its genuine endpoint moments, proper rays and
original protected pocket order. No original fine/coarse count or
whole load-row closure is inferred solely from (32).

No generated certificate, external mathematical proof script,
sampled configuration, angle mesh, normal reselection, altered
physical mean, Lean/Lake invocation or CI is a proof input.
