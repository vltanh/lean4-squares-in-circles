# Analytic closure of the five-corner family: working argument

## Status and objective

This note continues `HUMAN_FIVE_CORNER.md`, using its notation and proved
lemmas. The objective is to identify the least stationary radius selected
there with the specified candidate root, by a global analytic argument.
The identification is not claimed until the remaining sign and global
continuation arguments are proved. No numerical box cover is used here.

Write `q=R^2`, `q0=2257/576`, and

    r=sqrt(q-u^2),          w=sqrt(q-v^2),
    U=sqrt(q-(2-u)^2),      V=sqrt(q-(2-v)^2),
    U+V=3,                 p=-v'(u)>0,
    c=cos(t),              s=sin(t),
    k1=2-c*(r-1)+s*u,       k2=1+c*v-s*(w-1),
    F=k1^2+k2^2-q.

Position derivatives are taken with respect to `u`, keeping `q,t` fixed.
The attained least-family-radius configuration satisfies

    121/32 <= q < q0,       0<t<pi/4,
    F=F_u=F_t=0,
    u<1, v<1, r>1, w>1.

## 1. Every feasible simultaneous stationary point has an ordered position

### Proposition 1

If

    121/32 <= q <= q0,
    0<=t<=pi/4,
    F<=0,        F_u=F_t=0,

then

    1/2<v<u<1,        1/2<p<1,        r<w.                (1)

#### Proof of the order

The earlier Lemmas 10 and 11 give `u,v<1`. Feasibility gives `r,w>1`.
For `h=tan(t)`, position stationarity makes the sign of `F_t` equal to the
sign of

    N(h)=p*(1+h*v/w)*(u+h*(r-1))
               -(h+u/r)*((w-1)+h*v).

Suppose first that `u<v`. Then `p>1` and `r>w`. The constant and linear
coefficients of this quadratic are

    C0=(u/r)*(p*r-w+1)>0,
    C1=p*(r-1)-(w-1)+u*v*(p/w-1/r)>0.                   (2)

If its quadratic coefficient is nonnegative, (2) gives `N(h)>0` for
every `h>=0`. If the quadratic coefficient is negative, `N` is concave,
so on `[0,1]` it suffices to check its two endpoint values.

For the value at 1, recall the strictly decreasing function proved in
Lemma 4 of the earlier note:

    g(x)=sqrt(q-(2-x)^2),
    rho(x)=sqrt(q-x^2),
    H(x)=x+rho(x),
    Phi(x)=rho(x)*g'(x)*(H(x)-1)/H(x).

Its decrease holds on the entire radical domain in the present radius
range. Direct substitution, with `p=g'(u)/g'(v)`, gives

    N(1) = H(u)*H(v)/(r*w*g'(v)) * (Phi(u)-Phi(v)) > 0.   (3)

Thus `N>0` on `[0,1]` in either case, contradicting `F_t=0`.

If `u=v`, then `r=w`, `p=1`, and

    N(h)=(u/r)*(1-h^2).

This is positive for `h<1`. At `h=1`, the two position derivative
coefficients `a=s+c*u/r` and `B=c+s*v/w` agree, whereas `k1-k2=1`.
Hence `F_u/2=a*(k1-k2)=a>0`, contradicting position stationarity.
This proves `u>v`, and hence `p<1` and `r<w`.

#### The remaining bounds

At the domain point `u=1` the involution gives

    v=2-sqrt(6*sqrt(q-1)-8)>=1/2,

since `q<=q0`. Its strict decrease with `u`, together with `u<1`, gives
`v>1/2`. Applying the same involution after exchanging `u,v` gives
`u>1/2`.

Finally `p=-v'` strictly decreases with `u`, because `v''>0`. At `u=1`,
the earlier rational bounds give `p>=62/123>1/2`. Thus `u<1` implies
`p>1/2`, proving (1).

## 2. Bounds for the tangent ratio

At an interior simultaneous stationary point, write

    a=s+c*u/r,             B=c+s*v/w,
    d=s*(r-1)+c*u,         e=c*(w-1)+s*v.

The two derivative vectors are positive scalar multiples:

    k_u=(a,-p*B),
    k_t=(d,-e)=kappa*k_u.

The earlier note proves

    kappa=r-h/(h+u/r),        h=tan(t),
    r-1<kappa<r.

On the ordered stationary region, this improves to

    kappa>1.                                                (4)

Indeed let `m=2-sqrt(q-9/4)` be the symmetric position, where `U=V=3/2`.
The order `u>v` implies `u>m`; also `m<1`. Since `r+u` increases with
`u<R/sqrt(2)`, and `u<1<R/sqrt(2)` in the present radius range,

    r+u > sqrt(q-m^2)+m
         = sqrt(25/4-4*m)+m > 5/2.

The final inequality follows on squaring from `m>m^2`. Also `r>5/3`,
because `u<1` and `q>=121/32`. Since `0<h<1`,

    kappa >= r-1/(1+u/r)
            = r*(1-1/(r+u))
            > (3/5)*r > 1.

## 3. The sign which still needs to be proved

At a simultaneous stationary zero define

    A0=|k_u|^2,
    S0=k1*k1_uu+k2*k2_uu,
    T0=(k1/B)*(1-u*v/(r*w)),
    U0=2*k1+k2-q.

Then the exact formula from the earlier note is

    det(Hess(F))/4
      = A0*(S0*kappa^2-2*T0*kappa+U0)+S0*U0-T0^2.         (5)

The new order and tangent bounds narrow the region on which this sign
must be studied, but (5) is not asserted positive here. A proof of its
positivity must also be accompanied by a global argument excluding
distinct feasible components, or by a stronger curvature statement along
the entire relevant minimized envelope.
