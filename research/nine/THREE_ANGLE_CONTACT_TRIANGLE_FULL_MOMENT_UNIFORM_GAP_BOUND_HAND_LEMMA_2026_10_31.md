# A uniform bound for all three contact gaps from one full-moment triangle

Date: October 31, 2026 UTC.

**Status: complete hand theorem.** A single strictly concave scalar
comparison handles every triangle in the stated full-moment domain. In
the original A-only owner it strengthens all three simultaneous contact
gap bounds to a common constant less than one half. No circle radius,
endpoint mask, exterior aperture or equation at an exterior neighbor is
used.

## 1. Generic three-angle theorem

Let A,B,C be three angles satisfying

    A+B+C=pi, pi/4<A,B,C<pi/2.

Suppose that one positive number lambda gives three positive gaps

    g_A=1-lambda*sin(A),
    g_B=1-lambda*sin(B),
    g_C=1-lambda*sin(C),

and that the unchanged full-moment identity is

    g_A*g_B*g_C
      =(sin(A)-cos(A))*(sin(B)-cos(B))*(sin(C)-cos(C)).    (1)

Then

    lambda>=sqrt(3)-1,                                  (2)

with equality only when A=B=C=pi/3. In particular every original gap has
the strict common upper bound

    0<g_i<1-(sqrt(3)-1)/sqrt(2)<1/2.                     (3)

The theorem does not replace any original gap by a comparison value.

## 2. One concavity argument proves the entire domain

Put k=sqrt(3)-1. Then 0<k<3/4, and for pi/4<x<pi/2 define

    f(x)=log[(sin(x)-cos(x))/(1-k*sin(x))].

Every logarithm argument is positive. Twice differentiating gives

    f''(x)=-2/(sin(x)-cos(x))^2
              +k*(k-sin(x))/(1-k*sin(x))^2<0.           (4)

Here is a complete sign check for the whole interval. If sin(x)>=k,
the second term is nonpositive and the first strictly negative. If
sin(x)<k<3/4, then cos(x)>1/2, so

    0<sin(x)-cos(x)<1/4.

The first term in (4) is then strictly less than -32. The positive
second term is bounded above by

    k^2/(1-k)^2<9.

Thus (4) is strict in this second case as well. There is no omitted join
at sin(x)=k.

Strict concavity at the common mean pi/3 now gives

    f(A)+f(B)+f(C)<=3*f(pi/3)=0,                        (5)

with equality only when A=B=C=pi/3. The final equality follows from

    1-(sqrt(3)-1)*sin(pi/3)
      =1-(sqrt(3)-1)*sqrt(3)/2
      =(sqrt(3)-1)/2
      =sin(pi/3)-cos(pi/3).

Exponentiating the positive quantities in (5) gives

    product_i(sin(i)-cos(i))
       <=product_i(1-k*sin(i)).                        (6)

On the interval where all its factors are positive, the function
`L -> product_i(1-L*sin(i))` strictly decreases: each positive factor
strictly decreases. Both the original lambda and k are in this interval.
Equations (1),(6) therefore imply lambda>=k. If the three angles are not
all equal, (5),(6) are strict, and lambda>k. This proves (2).

Since every original sine exceeds 1/sqrt(2), (2) gives the first strict
upper bound in (3). For its final comparison,

    (sqrt(3)-1)/sqrt(2)>1/2

is equivalent to `sqrt(6)-sqrt(2)>1`. Positive squaring reduces this to
`3>2*sqrt(2)`, whose squared reserve is 1. Thus the entire common upper
bound is strictly less than one half.

## 3. Literal original A-only contact-triangle entry

Retain every original unit, force, moment, owner, genuine side
application, full mean and physical circle coefficient in the A-only
side chart. Use the unchanged definitions

    alpha,beta>pi/4,
    pi/2<alpha+beta<2*pi/3,
    H=sin(alpha+beta), k0=-cos(alpha+beta), p=H-k0,
    s=sin(alpha), c=cos(alpha), S=sin(beta), C=cos(beta),
    u=1-omega*S/H,
    t=1-omega*s/H,
    w=1-omega,
    0<u,t,w<1.

These are the actual contact parameters from

    TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md
    FULL_A_ONLY_HUB_MOMENTS_FORCE_STRICT_CONTACT_SUM_BOUND_2026_10_29.md.

Their three complete original hub moments are

    rho*u=mu*(s-c),
    nu*t=rho*p,
    mu*w=nu*(S-C),
    mu,nu,rho>0.

Multiplying these exact equations and cancelling only the common
positive product mu*nu*rho gives

    u*t*w=(s-c)*(S-C)*p.                              (7)

Put

    gamma=pi-alpha-beta, lambda=omega/H.

Then pi/3<gamma<pi/2, so alpha,beta,gamma all lie in (pi/4,pi/2),
their sum is pi, and

    sin(gamma)=H, cos(gamma)=k0,
    u=1-lambda*sin(beta),
    t=1-lambda*sin(alpha),
    w=1-lambda*sin(gamma).

Equation (7) is precisely the generic full-moment identity (1).
Because gamma>pi/3, the three angles cannot all equal pi/3. Therefore

    omega/H>sqrt(3)-1,
    0<u,t,1-omega<1-(sqrt(3)-1)/sqrt(2)<1/2.            (8)

The actual contact triangle P,R_A,W has side lengths
`1-u,1-t,1-w`, opposite angles beta,alpha,gamma respectively. The
parameter lambda is twice its original circumradius. This geometric
interpretation is not needed for the algebraic proof; it confirms that
the common parameter and all three original gaps have been retained.

## 4. Scope

The generic theorem applies to any unchanged full-moment configuration
that establishes exactly the three-angle and positive-gap identity (1).
The application in Section 3 covers all original A-only physical endpoint
masks and every exterior aperture. It uses all three full hub moments
together and does not impose an unloaded equation at an exterior unit.

These uniform bounds are necessary inequalities, not a claim that the
A-only owner, an original graph/load row, or the nine-square theorem has
been excluded. No numerical configuration, generated cover, external
calculation, Lean or CI is used as a proof premise.
