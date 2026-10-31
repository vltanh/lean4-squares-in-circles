# A uniform lower bound on the AD-owning hub's roof coordinate

Date: October 31, 2026 UTC.

**Status: complete hand scalar theorem for the entire regular hub
chart.** The unchanged A3, D3 and V2 equations force

    y>11/25.

No equation, physical circle mask, side coordinate or true degree at B,
C or N is used. In particular the theorem applies before the exterior
physical-mask and side/diagonal classifications. It does not prove a
corresponding lower bound on 1-rho or exclude a completing square by
itself.

## 1. Original data and conclusion

Retain the full actual regular, two-strict, both-hub-owned roof chart
from
`TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md`
and its owner-side continuation
`TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`.
Use their unchanged notation

    alpha,beta>0, theta=alpha+beta in (0,pi/4),
    c=cos(alpha), s=sin(alpha),
    C=cos(beta), S=sin(beta),
    H=sin(theta), J=cos(theta), F=J-H>0,
    0<rho<1,
    x=1+s-H*rho in (0,1),
    y=1-c+J*rho in (0,1),
    m=x/y>0, n=F/(1-rho)>0.

The actual original radius window supplies

    1/2<d<61/60,

and the complete unchanged V torque is

    m*B0=n*D0,
    B0=d*s+c/2,
    D0=d*S+C/2.                                    (1)

Both actual V circle coefficients remain in their full nonnegative
intervals. No equality of those coefficients is assumed. The A3 and
D3 equations have supplied precisely the original definitions of m,n,
x,y above. No application or mean is moved.

**Theorem 1.1.** These entire original assumptions imply y>11/25.

## 2. The same positive force ratio has a uniform upper bound

The function

    f(t)=d*sin(t)+(1/2)*cos(t)

is strictly increasing for 0<=t<=theta<pi/4. Indeed its derivative
is d*cos(t)-(1/2)*sin(t)>0 because d>1/2 and cos(t)>sin(t)
throughout this interval. Consequently

    B0>1/2,
    D0<d*H+J/2,
    D0/B0<2*d*H+J<(61/30)*H+J.                    (2)

Put

    z=tan(theta) in (0,1).

Multiplying (1) by 1-rho and using n*(1-rho)=F gives the exact
original force-ratio identity

    m*(1-rho)=F*D0/B0.

Thus (2) implies

    m*(1-rho)
      < (1-z)*(1+(61/30)*z)/(1+z^2).              (3)

Every divided factor is positive. This is a bound on the same original
force ratio, rather than a replacement equilibrium.

## 3. A hypothetical small roof coordinate gives the opposing bound

Suppose y<=11/25. Since c<1, the actual identity for y gives

    rho<y/J<=(11/25)/J.

The actual identity for x, and s>0, then give

    m=x/y>1/y-H/J>=25/11-z,
    1-rho>1-(11/25)*sqrt(1+z^2)>0.                (4)

The first factor 25/11-z is positive as well. The elementary exact
inequality

    sqrt(1+z^2)<=1+z^2/2

therefore yields

    m*(1-rho)
      >(25/11-z)*(14/25-(11/50)*z^2).             (5)

The second factor in (5) is positive for the entire interval 0<z<1;
it is at least 17/50 there. No sign is lost on multiplying the bounds.

The difference between the right side of (5), multiplied by 1+z^2,
and the numerator of the upper bound (3) is exactly

    P(z)=3/11-(239/150)*z+(463/165)*z^2
         -(17/50)*z^3-(1/2)*z^4+(11/50)*z^5.    (6)

The following two continuous interval comparisons prove P(z)>0
throughout (0,1). They are ordinary hand inequalities; there is no
sampling or computed exclusion table.

## 4. The whole lower half-interval

For 0<=z<=1/2, the two negative higher-degree terms satisfy

    -(17/50)*z^3 >= -(17/100)*z^2,
    -(1/2)*z^4 >= -(1/8)*z^2.

Dropping the nonnegative fifth-degree term in (6) therefore gives

    P(z) >= 3/11-(239/150)*z+(16573/6600)*z^2
         > 27/100-(8/5)*z+(5/2)*z^2
          = (5/2)*(z-8/25)^2+7/500
         > 0.                                     (7)

The coefficient comparisons in the strict middle bound are

    3/11>27/100,
    239/150<8/5,
    16573/6600>5/2.

They include z=0 and z=1/2. In particular P(1/2)>0 is already
proved with a positive rational reserve.

## 5. The whole upper half-interval

For 1/2<=z<=1, differentiate the exact polynomial (6):

    P'(z)=-239/150+(926/165)*z-(51/50)*z^2
           -2*z^3+(11/10)*z^4.

Use z^3<=z^2, drop the last nonnegative term, and compare
239/150<8/5 and 926/165>28/5. This gives

    P'(z)>-8/5+(28/5)*z-(151/50)*z^2=:Q(z).       (8)

The quadratic Q is concave. Its two endpoint values are

    Q(1/2)=89/200>0,
    Q(1)=49/50>0.

It is therefore strictly positive on the entire interval [1/2,1].
Thus P is strictly increasing there. Together with P(1/2)>0 from
(7), this proves

    P(z)>0 for every 0<=z<=1.                     (9)

## 6. Contradiction and exact scope

Equations (6),(9) say the lower bound (5) is strictly greater than
the upper bound (3), because their common multiplier 1+z^2 is
positive. Both bounds refer to the same original positive quantity
m*(1-rho), a contradiction. Hence y>11/25, as claimed.

The proof retains all original units, degrees, loads, physical circle
masks, individual coefficients, actual applications and shared means.
It has used only the literal original regular A3/D3/V2 consequences
and the already accepted radius window. It requires neither the
two-unique endpoint alternative nor the unloaded side-transmitter
equations. The reflected whole chart gives the corresponding bound
for the roof coordinate on whichever hub owns the perpendicular AD
normal, with the entire original data exchanged.

This does not assert 1-rho>11/25 for the other hub. No central-pocket
or outer-pocket exclusion follows without its additional geometric
argument. No external mathematical script, pose computation, proof
certificate, normal reselection, mean replacement, Lean/Lake build
or CI was used in the new theorem.

## 7. Exact geometric consequences on the radius-5/4 circle

The following corollary was supplied and checked by the root continuation.
Restore the full original radius consequence 9/10<d<61/60, and put

    r=5/4, P=(d,1/2), Q=(d,-1/2),
    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    P_h=d*c-s/2, B0=d*s+c/2,
    R_A=P+y*e, K=P-h+y*e.

The actual outer A roof is P--R_A--K. Its upper-right vertex always
lies strictly outside this one comparison circle. Indeed B0>1/2 and
the complete theorem give

    |R_A|^2=d^2+1/4+y^2+2*y*B0
       >(9/10)^2+1/4+(11/25)^2+11/25
        =2117/1250>25/16.

The last positive difference is 1311/10000. Also |P|<r, since
(61/60)^2+1/4<25/16. Thus the actual segment P--R_A crosses
the r-circle exactly once.

Its crossing has own coordinates

    P_h*h+sqrt(r^2-P_h^2)*e.

Here P_h>0, and the positive square root exceeds B0 because
P_h^2+B0^2=d^2+1/4<r^2. In ordinary coordinates its argument is

    phi_A=acos(P_h/r)-alpha.

For fixed d the derivative of this scalar expression with respect to
alpha is B0/sqrt(r^2-P_h^2)-1<0. Consequently

    0<phi_A<acos(d/r)<pi/4.

The last comparison follows from d/r>18/25>1/sqrt(2), whose
positive squared comparison is 648>625. The positivity follows from
the actual roof's strictly positive ordinary height. This is an angle
of a fixed circle intersection, not a changed physical contact.

The two actual inner A vertices also lie strictly inside this circle.
For u=1-y in (0,1), they are

    P-u*e and I_A=P-h-u*e.

For the first, |P-u*e|^2=|P|^2+u^2-2*u*B0<|P|^2<r^2.
The squared norm of the second is convex in u. At u=0, monotonicity
of d*c-s/2 in alpha and of d^2+5/4-sqrt(2)*(d-1/2) in d>9/10
give

    |P-h|^2<d^2+5/4-sqrt(2)*(d-1/2)
       <(61/60)^2+5/4-(7/5)*(31/60)
        =25/16-1/450<r^2.

At u=1, use P_h+B0=d*(c+s)+(c-s)/2>d to get

    |P-h-e|^2=d^2+1/4+2-2*(P_h+B0)
       <(d-1)^2+5/4<63/50<r^2.

Convexity proves |I_A|<r throughout the entire actual interval.
The reflected calculation, with alpha replaced by beta and u by rho,
puts both inner D vertices Q+rho*v and Q-k+rho*v strictly inside
the same circle. It does not assert that the D outer roof vertex is
outside it: that assertion would need its own argument.

These are exact whole-chart circle and angle bounds. Any claim about
the remaining free interval between the A roof and B still requires
both actual B face alternatives and the original pocket winding.
