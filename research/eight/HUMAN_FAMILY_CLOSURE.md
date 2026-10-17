# The sharp five-corner radius: an analytic uniqueness and optimality proof

## Theorem and scope

This note continues `HUMAN_FIVE_CORNER.md`, using its notation and proved
lemmas. It proves that the sharp five-corner radius is selected by the
**unique admissible stationary solution** in

    (79/40)^2 <= q <= 9789/2500.

The proof is global within the conditional family. It uses the exact
support enclosure in `HUMAN_FAMILY_ENCLOSURE.md` and the explicit rational
chain in `ANALYTIC_RATIONAL_CONSTRUCTION.md`. Every critical point of the
minimized envelope in the relevant strip is a strict minimum, including
critical points whose defect is positive. This yields uniqueness of the
envelope minimum, and strict radius monotonicity yields uniqueness of the
stationary root.

No numerical box cover or tiny root-isolating interval is part of this
proof. The unrestricted reduction from arbitrary eight-square packings
to the five-corner chain remains a separate structural problem.

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

## 3. The Hessian identity used in the closure

At a simultaneous stationary zero define

    A0=|k_u|^2,
    S0=k1*k1_uu+k2*k2_uu,
    T0=(k1/B)*(1-u*v/(r*w)),
    U0=2*k1+k2-q.

Then the exact formula from the earlier note is

    det(Hess(F))/4
      = A0*(S0*kappa^2-2*T0*kappa+U0)+S0*U0-T0^2.         (5)

Proving (5) positive only at zero-defect stationary points would leave a
global issue: distinct feasible components might contain distinct strict
minima. Section 4 proves the stronger statement required to avoid that
issue. It establishes a positive definite Hessian at every envelope
critical point in the analytically enclosed strip, without a feasibility
assumption. Thus there is at most one envelope critical point at each
radius, and radius monotonicity completes the global selection argument.

## 4. Closure on the analytically enclosed strip

The curvature estimate in this section applies at **every**
critical point of the minimized envelope in the strip, including critical
points whose defect is positive. This is the property which addresses
the global issue identified above.

Set

    q_minus=6241/1600=(79/40)^2,
    q_plus=9789/2500,
    alpha=arctan(1/5),
    q_minus<=q<=q_plus,        0<=t<=alpha.                 (6)

The support argument in `HUMAN_FAMILY_ENCLOSURE.md` proves that every
feasible five-corner chain with `q<=q_plus` has `q>q_minus` and `t<alpha`.
The explicit five vertices in `ANALYTIC_RATIONAL_CONSTRUCTION.md` supply
a feasible chain at `q_plus`. Both inputs are proved by exact inequalities.

For a fixed `q,t` let `u_q(t)` denote the unique minimizing position from
Lemma 2 of `HUMAN_FIVE_CORNER.md`, and put

    M(q,t)=F(q,-u_q(t),t).

It is smooth throughout (6), since the position minimum is interior and
`F_uu>0`.

### Proposition 3: every minimizing position in the strip has u>87/100

Evaluate the position derivative at `u=87/100`, where `2-u=113/100`.
The following bounds hold for all `q` in (6). The decimals are exact
terminating rational numbers.

| Quantity | Lower bound | Upper bound |
| --- | ---: | ---: |
| `r` | 1.773 | 1.778 |
| `U` | 1.619 | 1.625 |
| `V=3-U` | 1.375 | 1.381 |
| `Y=2-v` | 1.411 | 1.424 |
| `v` | .576 | .589 |
| `w` | 1.885 | 1.894 |
| `p` | .671 | .684 |

All bounds are strict. They follow successively by squaring the positive
endpoints in

    r^2=q-.7569,
    U^2=q-1.2769,
    V=3-U,
    Y^2=q-V^2,
    v=2-Y,
    w^2=q-v^2,
    p=1.13*V/(U*Y).

For example the bounds for `Y^2` are

    1.993464=q_minus-1.381^2
        < Y^2 < q_plus-1.375^2=2.024975,

which lie strictly between `1.411^2` and `1.424^2`. For the last row,

    p>1.13*1.375/(1.625*1.424)>.671,
    p<1.13*1.381/(1.619*1.411)<.684.

Write `x=u/r`, `y=v/w`. At this comparison position direct expansion gives

    F_u/2=Ls*s+Lc*c+Qs*s^2-Qc*c^2+J*c*s,

where

    Ls=2-p*y,
    Lc=2*x-p,
    Qs=u+p*(w-1)*y,
    Qc=(r-1)*x+p*v,
    J=u*x-(r-1)-p*v*y+p*(w-1).

The displayed bounds give `Qs,Qc>0`, `Ls>7/4`, `Lc<1/3`, and

    J>17/40-.778-.127+.59=.11>0.

Since `c>s` on our angle interval, differentiating shows

    F_ut/2=Ls*c-Lc*s+2*(Qs+Qc)*c*s+J*(c^2-s^2)>0.

Thus it suffices to bound `F_u` at `t=alpha`. There `h=s/c=1/5`, and
`1/c=sqrt(26)/5` lies between `1.019` and `1.020`. Substitution gives

    F_u/(2*c^2)
      =[2/c-(r-1)+h*u]*(h+x)
              -p*[1/c+v-h*(w-1)]*(1+h*y)
      < (1441/1000)*(691/1000)
              -(671/1000)*(1416/1000)*(53/50)
      < -1/100 < 0.                                      (7)

The first product uses `x<.491`; the second uses `y>.3`. Strict convexity
in the position now puts its minimum to the right of `87/100`, proving
the proposition.

### Proposition 4: all envelope critical points lie in the ordered interior

Suppose `M_t(q,t)=0` in (6). Then, without any assumption about the sign
of `M`,

    87/100<u<1,
    1/2<v<u,
    1/2<p<1,
    17/10<r<16/9,
    r<w<48/25.                                           (8)

To prove the upper bound `u<1`, use Step 3 of Lemma 11 in the earlier
note. That step proves, at `u=1`,

    p*r<w-1

whenever `31/8<=q<=q0`. The product `p*r` decreases with `u`, and `w`
increases, so this inequality persists for `u>=1`. Lemma 10 gives `v<1`
at every minimizing position. Therefore `u>=1` would imply `u>v`,
`p<1`, and `r<w`. The three coefficients of `N(h)` in (2) and the earlier
note are then all negative. If `r<=1`, their signs remain negative:
`p*(r-1)<0<w-1`; if `r>1`, use `p*(r-1)<r-1<w-1`.
Thus `F_t<0` at any position-stationary point with `u>=1`, a contradiction.
This exclusion does not use feasibility.

The lower bound for `u` is Proposition 3. The involution at `u=1` gives
`v>1/2` when `u<1`, and the comparison table gives `v<.589` when
`u>.87`. Thus `u>v`, which gives `p<1` and `r<w`; monotonicity of `p`
and its value at `u=1` give `p>1/2`. Finally,

    r^2>q_minus-1>(17/10)^2,
    r^2<q_plus-(87/100)^2<(16/9)^2,
    w^2<q_plus-1/4<(48/25)^2.

We shall also use the following consequence on the entire position
interval `[87/100,1]` at these radii:

    v''>1,
    p>3/2-u,
    u*(1+p)>141/100.                                     (9)

Indeed `U<171/100`, `129/100<V<7/5`, `2-v<3/2`, and `p>1/2`. The
derivative formula from the earlier note gives

    v''=q*V/((2-v)*U^3)+q*p^2/((2-v)*V^2)
        > (39/10)*(129/100)/((3/2)*(171/100)^3)
             +(39/10)*(1/4)/((3/2)*(7/5)^2)
        > 67/100+33/100=1.

As `p'=-v''`, integration from `u` to 1 and `p(1)>1/2` give
`p>3/2-u`. The concave quadratic `u*(5/2-u)` has minimum on
`[87/100,1]` at an endpoint, so

    u*(1+p)>u*(5/2-u)>=14181/10000>141/100,

proving (9).

### Proposition 5: every minimizing position in the strip has |k|<2

This assertion also makes no feasibility assumption. Use the fixed trial
position `u=15/16`. At `q=q_minus` its radicals satisfy

    r^2=19339/6400,
    U^2=17739/6400,

and hence

    r>1.738,
    1.664<U<1.665,
    1.335<V<1.336,
    .544<v<.546,
    w>1.898.

These inequalities follow by successive squaring exactly as in the
comparison table above. At `t=0` they give

    k1<1.262,       k2<1.546,
    |k|^2<1.262^2+1.546^2=3.982760<4.                   (10)

At `t=alpha`, use `5.09<sqrt(26)<5.10` in

    k1=2+[15/16-5*(r-1)]/sqrt(26),
    k2=1+[5*v-(w-1)]/sqrt(26).

The same bounds give

    k1<1.461,       k2<1.360,
    |k|^2<1.461^2+1.360^2=3.984121<4.                   (11)

The endpoint tests fill the whole angle interval analytically. At this
fixed radius and position put `f(t)=|k|^2-4=F+q_minus-4`. Lemma 3 in the
earlier note gives

    f''+4*f>91/45+4*q_minus-16=5849/3600>0.

Its proved change of variable makes `f/cos(2*(t-pi/8))` strictly convex.
By (10)-(11) this transformed function is negative at both endpoints,
and hence throughout the interval. Thus the trial position has `|k|<2`
for all `t` in (6) when `q=q_minus`.

At fixed `u,t`, the earlier formula `F_q<-1` says
`(|k|^2)_q<0`. The trial position remains in the radical domain as `q`
increases through (6), so its squared norm decreases. Finally the
minimizing position has no larger squared norm than the trial position.
This proves the proposition at every `q,t` in the strip.

### Proposition 6: every envelope critical point in the strip is a strict minimum

At a critical point use `a,B,d,e` as in section 2, and put

    x=u/r,       y=v/w,       h=tan(t),
    b=p*B,       A0=a^2+b^2,
    S0=k1*k1_uu+k2*k2_uu,
    T0=k1*k1_ut+k2*k2_ut,
    U0=2*k1+k2-|k|^2.

The use of `|k|^2` instead of `q` in `U0` is essential here: the defect
need not be zero. Let

    sigma=S0/k1,       tau=T0/k1,       nu=U0/k1.

As `F_u=F_t=0`, the derivative vectors are positive multiples,
`k_t=kappa*k_u`, and the exact Hessian formula becomes

    det(Hess(F))/(4*k1^2)
      = (A0/k1)*(sigma*kappa^2-2*tau*kappa+nu)
             +sigma*nu-tau^2.                            (12)

We prove the following uniform bounds:

    kappa>7/5,
    0<tau<7/8,
    nu>9/100,
    A0/k1>17/50,
    kappa*sigma>3,
    sigma>27/16.                                         (13)

#### The tangent and mixed terms

From (8),

    x>x0:=783/1600,
    y>25/96,
    r>17/10,
    r<16/9.

The identity `kappa=r-h/(h+x)` and `h<=1/5` give `kappa>7/5`;
for example `x>x0>7/15` makes `h/(h+x)<3/10`.

Also

    B=(1+h*y)/sqrt(1+h^2)>=1.

Indeed, after squaring, the difference of the two sides' positive
numerators is `h*(2*y-h*(1-y^2))>=0`, since `y>1/4` and `h<=1/5`.
The mixed derivative cancellation gives

    tau=(1-x*y)/B.

It is positive by `r*w>u*v`, which here follows already from
`u,v<1` and `q>3.9`. Since

    x*y>(783/1600)*(25/96)=261/2048>1/8,

we have `tau<7/8`.

#### The normal term

Angle stationarity gives

    k1/k2=e/d=[(w-1)+h*v]/[u+h*(r-1)]>6/7.              (14)

For a complete proof of the inequality, on the interval `[.87,1]` the
function `w-1-6*u/7` strictly decreases: its derivative is
`p*v/w-6/7<0`. At `u=1` we have `w>19/10`. One elementary verification is
that `q>39/10` gives `r>17/10`, then
`2-v=sqrt(6*r-8)>37/25`, and finally
`w^2>39/10-(13/25)^2>(19/10)^2`.
Consequently

    w-1-6*u/7>9/10-6/7=3/70.

At the same time `v-(6/7)*(r-1)>1/2-2/3=-1/6`, by `r<16/9`.
The numerator of `e-(6/7)*d`, divided by `c`, is therefore greater than

    3/70-(1/5)*(1/6)=1/105>0,

proving (14).

Moreover `k2=1+c*(v-h*(w-1))>1`. Proposition 5 gives `k1<|k|<2`, so
`z=k2/k1` lies in `(1/2,7/6)`. Thus

    nu=2+z-|k|*sqrt(1+z^2)
       >2+z-2*sqrt(1+z^2)>9/100.                         (15)

For the last comparison, the function on the middle line is concave in
`z`. At the two endpoints its values are
`5/2-sqrt(5)>1/4` and `(19-2*sqrt(85))/6>9/100`.
The rational inequalities `sqrt(5)<9/4` and `sqrt(85)<923/100` verify
these comparisons.

#### The positive derivative norm

Position stationarity gives `k1*a=k2*b`, so

    k1=|k|*b/sqrt(A0),
    A0/k1=A0^(3/2)/(|k|*b).

Here `a=s+c*x>=x>x0>489/1000` and `b=p*B>1/2`. The first inequality uses
`0<x<1` and `c+s>=1`, by writing `a=x*(c+s)+(1-x)*s`.
Replacing `|k|` by its
strict upper bound 2, first decreasing `a` to `489/1000`, and then
decreasing `b` to `1/2`, gives

    A0/k1>((489/1000)^2+1/4)^(3/2)>17/50.                (16)

The second decrease is legitimate because
`(a0^2+b^2)^(3/2)/b` increases for `b>=1/2` when `a0=489/1000`:
its derivative has the sign of `2*b^2-a0^2>0`.
For the final rational comparison in (16), the quantity inside the power
is greater than `489/1000`, its square root is greater than `699/1000`,
and their product exceeds `17/50`.

#### The position curvature

The formulas for `k1_uu,k2_uu`, together with position stationarity, give

    sigma >= c*q/r^3+a*Z,
    Z=v''/p=q/((2-u)*U^2)+p*q/((2-v)*V^2).

The maximum of `X*(q-X^2)` on `0<X<sqrt(q)` is
`2*q^(3/2)/(3*sqrt(3))`. Therefore

    Z>=K*(1+p),       K=3*sqrt(3)/(2*R)>13/10.

For the stated rational bound on `K`, use `R<99/50`, which gives
`K>25*sqrt(3)/33>13/10`; the last comparison follows by squaring.

Multiplication by `kappa`, using `kappa*a=d`, gives

    kappa*sigma
      >=kappa*c*q/r^3+d*K*(1+p).                         (17)

We have `q/r^2=1+x^2` and `q/r^3<4/5`; the latter follows from
`r>17/10`, `u<1`, since

    q/r^3=(1+(u/r)^2)/r
           <(1+(10/17)^2)/(17/10)=3890/4913<4/5.

Use `kappa=r-h/(h+x)`, `d=c*(u+h*(r-1))`, and (9) in (17).
It follows that

    kappa*sigma
      > c*[1+x0^2+1833/1000+(273/200)*h
                                -(4/5)*h/(h+x0)].         (18)

Here `x0=783/1600`. For positive numbers `A,B,x0`, elementary
arithmetic-geometric mean gives

    A*h-B*h/(h+x0)
      =A*(h+x0)+B*x0/(h+x0)-A*x0-B
      >=-(sqrt(B)-sqrt(A*x0))^2.

Apply this with `A=273/200`, `B=4/5`. Since

    16/25<A*x0<4/5<81/100,

the square on the right is less than `1/100`. Also
`1+x0^2+1833/1000>3.072` and `c>49/50`. Thus (18) gives

    kappa*sigma>(49/50)*3.062
                      =75019/25000>3.                    (19)

Finally `kappa<r<16/9`, so `sigma>27/16`. This completes (13).

#### The determinant

Substitution of (13) in (12) is now strict in the correct directions:

    sigma*kappa^2-2*tau*kappa+nu
       =kappa*(kappa*sigma-2*tau)+nu
       >(7/5)*(3-7/4)+9/100=46/25>0.

Consequently

    det(Hess(F))/(4*k1^2)
       >(17/50)*(46/25)+(27/16)*(9/100)-(7/8)^2
        =237/20000>0.                                    (20)

Since `F_uu>0`, the Hessian is positive definite. The envelope formula
therefore gives

    M_tt=F_tt-F_ut^2/F_uu
         =det(Hess(F))/F_uu>0                             (21)

at every critical point of `M` in the strip. No sign assumption about
`F` or `M` was used in Propositions 3-6.

### Theorem: a unique stationary root selects the sharp family radius

For each fixed `q` in (6), the function `t -> M(q,t)` has at most one
critical point on `(0,alpha)`. Every such point is its unique global
minimum on `[0,alpha]`.

Indeed (21) makes every critical point a strict local minimum. Two such
points would force an interior maximum between them, contradicting
(21). Also `M_t(q,0)<0`: the exact comparison at `u=1,t=0` is

    F_u/2=((3-r)/r)*(2-3/(2-v))<0,

since `q<=q_plus<q0`. Thus `u_q(0)>1`, and the negative-angle-derivative
argument in Proposition 4 gives `M_t(q,0)<0`. If an interior critical
point exists, the derivative remains negative before it and positive
after it, since there can be no second zero. This proves the global
minimum assertion.

Now put

    H(q)=min_{0<=t<=alpha} M(q,t).

Position stationarity and the earlier radius derivative give

    M_q=F_q<-1.

The functions are smooth on the compact strip and the position minimum
is always interior. It follows, either by integration at fixed `t` and
then taking the minimum, or directly by the envelope argument, that
`H` is continuous and strictly decreasing in `q`.

Let `q_hat` be the square of the sharp five-corner radius. Its existence
and stationarity were proved in Lemma 8 of the earlier note. The rational
chain at `q_plus` and the analytic enclosure give

    q_minus<q_hat<=q_plus,
    0<t_hat<alpha,
    F(q_hat,-u_hat,t_hat)=F_u=F_t=0.

The preceding theorem makes this critical point the unique global
minimum of `M(q_hat,.)` on the strip, so `H(q_hat)=0`.

Conversely, every positive-radical solution of the polynomial equations
(27)-(30) in `HUMAN_FIVE_CORNER.md`, with

    q_minus<=q<=q_plus,       c^2+s^2=1,       0<s<c,

gives a genuine feasible chain. The analytic enclosure forces its tilt
into `(0,alpha)`. Its stationary position is the unique position minimum,
and its stationary tilt is the unique global envelope minimum just
proved. Thus `H(q)=0`. Strict decrease of `H` forces `q=q_hat`.
At that radius the tilt is unique, and then the position is unique;
positivity selects all remaining radicals and the sine and cosine.

Therefore the sharp conditional family radius is specified by the
**unique admissible stationary solution in the explicit strip (6)**.
The word "least" can be removed from the earlier root selection rule
within this strip. This is a pen-and-paper uniqueness and global
optimality argument for the family. A tiny numerical isolating box is
not part of its definition or proof.

The unconditional lower bound for arbitrary eight-square packings still
requires the separate structural reduction. No family result in this
note asserts that reduction.
