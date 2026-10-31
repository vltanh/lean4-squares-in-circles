# Continuous hand bounds for the complete three-spoke hub-owner return scalar

Date: October 28, 2026. Authors: W-continuation, root, and
return_scalar_assembly.

**Status: complete candidate proof, frozen for full independent and root
review.** This source proves the complete four-output scalar theorem on
its unchanged coupled domain by differentiation, endpoint comparisons,
and explicit polynomial identities. It has no executable certificate,
interval tree, sampled sign, or unproved extremum as a premise. Adoption
and the substitution into the original physical callers are separate.
This scalar source claims no original graph or load-family closure.

The original scalar source and its two arithmetic programs are preserved
unchanged as historical records:

| Historical source | SHA-256 |
| --- | --- |
| `THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_BOUNDS.md` | `dd6ee983deaeac1cf0c02758b2ddb2501a33175fb0281702a18027f869fdbf64` |
| `certificates/three_spoke_hub_owner_return_scalar_bounds.py` | `d073ebfa7d1c27f8c4272a9d3b5c56e20f8de1a1ae310a8d7d790ff5c91acf99` |
| `certificates/review_three_spoke_hub_owner_return_fraction.py` | `fa997a188f483e06800e8c6a036749fa440fcf1ca0f3bf67d8a5ba3ba9991369` |

The proof below is self-contained real algebra and calculus. None of
those three historical files, or their 475 terminal boxes, is a proof
premise. Their hashes identify the exact theorem being replaced.

## 1. Exact unchanged domain and conclusions

Let

    a>b>0,                 a^2+b^2=1,
    p0=(a-b)/(a+b),        p0<p<P=min(b/a,(1-b)/a),
    H=b+a*p,              t=1-H,
    x=1-(b/a)*(1+p)>0,    y=a-t,
    D=1-p*H,              v=t/D,
    E=sqrt(1+x^2),        L=sqrt(1+v^2),
    g=(x+v)/(E*L),        h=(1-x*v)/(E*L),
    A0=(1+b+x*y)/E,       B0=(x*(1+b)-y)/E.                 (1)

For the original, unchanged parameter `0<lambda<=1`, put

    xi=B0+lambda*h,
    d=1-xi,
    k=1-A0+lambda*g.                                      (2)

Assume only

                              k>0.                         (3)

There is no hypothesis on the sign or upper bound of `xi`, and no
upper-bound hypothesis on `k`. In particular the original `lambda=1`
endpoint is included. An original `k=1` is excluded by the proved
conclusion, rather than being deleted from the hypotheses. The symbol
`d` always means the original scalar complement `1-xi`.

**Theorem.** On the entire domain (1)--(3),

                 d>1/3,    0<k<1/8,    h>3/5,    g>d.      (4)

We prove the stronger auxiliary statements

    d1=1-B0-h > sqrt(2)-27/25 > 1/3,
    k1=1-A0+g < 1/8,
    0<g<133/200,           h>149/200>3/5,                  (5)

on the entire domain (1), without a `k1>0` guard. On the portion of
that domain with `k1>0`, we also prove

    F=g^2-g+B0*g+h*(A0-1) > 467/40000 > 0.                 (6)

The original parameter is restored by the exact identities and
inequalities

    d>=d1,                k<=k1,
    k>0 implies k1>0,
    g*(g-d)=F+h*k.                                         (7)

Thus (5)--(7) imply (4). No division by `k`, `lambda`, `xi`, or a
possibly zero proper distance is used. The quantities `x,v,y,A0,B0`
are always the coupled expressions (1).

## 2. Elementary bounds and the closed lower-p endpoint

Set `r=b/a`. Since `p0<p<r`,

    (1-r)/(1+r)<r,
    r>sqrt(2)-1,
    0<p0<sqrt(2)-1.                                       (8)

The bound `p<1/sqrt(3)` follows from the two upper bounds in (1).
For `b<=1/2`, one has `p<r<=1/sqrt(3)`. For `b>=1/2`, one has

    p<(1-b)/a=sqrt((1-b)/(1+b))<=1/sqrt(3).

Also `r<1` and `r/(1+r^2)` is increasing for `0<r<1`. Therefore

    ab=r/(1+r^2)>1/(2sqrt(2)),
    b>ab>1/3.                                             (9)

The last comparison uses `3>2sqrt(2)`. Put `T=a-b*p`. The original
lower bound on `p` and the unit-circle relation give

    T>0,     H>T,     H^2+T^2=1+p^2,
    H>1/sqrt(2)>7/10,     0<t<3/10.                      (10)

For `q=1-p`,

    q>21/50>0,
    D=1-p*H=q+p*t>q,
    D>t>0,
    0<v<1.                                               (11)

Here `1/sqrt(3)<29/50` follows from `2500<2523`, and
`D-t=H(1-p)>0`. Furthermore

    0<x<1-r*(1+p0)=p0<sqrt(2)-1<1/2.                     (12)

Thus `x*v<1`, and, with

    gamma=atan(x),   delta=atan(v),   chi=gamma+delta,

we have

    0<chi<pi/2,   g=sin(chi)>0,   h=cos(chi)>0,
    g^2+h^2=1.                                           (13)

Whenever `a,b` are fixed and `p` is decreased through the closed
interval `[p0,p]`, all original strict upper bounds remain valid.
The positive `x` remains positive. At `p=p0`, allow `x=p0` and
`H=T`; the adequate bounds `x<=p0<sqrt(2)-1` and
`H>=1/sqrt(2)>7/10` still hold. All subsequent arguments using that
closed endpoint therefore have positive denominators.

Since `x^2<1/5`, we have `E<11/10`. Also `y=a-t>0`. By (9),

                   A0>(1+b)/E>40/33>1>g.                 (14)

## 3. Whole-domain monotonicity of the angle and k1

### 3.1. The useful positive combination B0+h

On every interval `[p0,p]` just described,

    v^2=t^2/D^2<t^2/q^2
       <[(3/10)/(21/50)^2]*t=(250/147)*t<2*t.

The convex tangent bound `(1+z)^(-1/2)>=1-z/2` for `z>=0`
therefore gives

                         1/L>=1-v^2/2>1-t=H.

Consequently

    B0+h=[x*(1+b-v/L)+t-a+1/L]/E
         >(1-a)/E>0.                                    (15)

Here `1+b-v/L>b>0` and `x>0`, while `t+1/L>1`.

### 3.2. Fixed-a,b derivatives

Keep `a,b` fixed, and differentiate with respect to `p`. Let

    M=a+b-1+t^2>0,
    K=sqrt(D^2+t^2).

The exact identities are

    x'=-r,                 y'=a,
    v'=-M/D^2,             delta'=-M/K^2,
    gamma'=-r/E^2,
    A0'=r*B0/E^2+a*x/E,
    B0'=-r*A0/E^2-a/E.                                  (16)

For example, the numerator in the derivative of `v=t/D` is
`-a*D+t*(H+a*p)=-M`; this follows from

                  M=a*D-t*(H+a*p).                       (17)

Using (13), (15), and (16),

    g'=h*(-r/E^2+delta')<0,
    k1'=-r*(B0+h)/E^2-a*x/E+h*delta'<0.                 (18)

Both `g` and `k1` therefore strictly decrease from their values at
the closed endpoint `p=p0`.

### 3.3. One continuous endpoint family

At `p=p0`, write

    z=p0,   u=1+z^2,   z_star=sqrt(2)-1.

The complete endpoint family is

    0<z<z_star,
    a=(1+z)/(sqrt(2)*sqrt(u)),
    b=(1-z)/(sqrt(2)*sqrt(u)),
    H=sqrt(u)/sqrt(2),
    x=z,
    A0=(1-z)/sqrt(u)+(1+z)/sqrt(2),
    w=tan(chi)=[1+z-u^(3/2)/sqrt(2)]/(1-z).             (19)

These expressions also make sense on the full closed interval
`0<=z<=z_star`. On that interval `A0` strictly decreases:

    dA0/dz=-(1+z)/u^(3/2)+1/sqrt(2)<0.

Indeed `z^2<1/5` gives `u^3<(6/5)^3<2`. Meanwhile `w`
strictly increases:

    dw/dz=[2-sqrt(u)*(1+3*z-2*z^2)/sqrt(2)]/(1-z)^2>0.   (20)

For the sign, `sqrt(u)<11/10`, `z<1/2`, and
`1+3*z-2*z^2<5/2` give a product less than `11/4<2sqrt(2)`.
The last comparison follows from `121<128`. The numerator defining
`w` is positive already at `z=0`, and (20) keeps it positive.

Since `g=w/sqrt(1+w^2)` increases with `w`, both `g` and
`k1=1-A0+g` strictly increase through this endpoint family.
Their upper limits occur at `z=z_star`, where

    A_star=1+sqrt(1-1/sqrt(2)),
    w_star=1+sqrt(2)-2sqrt(2-sqrt(2)),
    g_star=w_star/sqrt(1+w_star^2).                       (21)

### 3.4. Exact reserves at the endpoint

First,

    1/sqrt(2)<99/140,
    (99/140)^2-1/2=1/19600,
    1-99/140-(27/50)^2=11/8750>0.

Hence

                             A_star>77/50.                (22)

Next `w_star<8/9`. The equivalent positive-sided comparison

                 2sqrt(2-sqrt(2))>sqrt(2)+1/9

has squared left-minus-right difference

    [485-342sqrt(2)]/81>0,
    485^2-2*342^2=1297>0.

It follows that

    g_star<8/sqrt(145)<133/200,
    133^2*145-64*200^2=4905>0.                            (23)

Equations (18)--(23) prove

    0<g<133/200,
    k1<1-A_star+g_star<1-77/50+133/200=1/8.              (24)

Finally, (13) yields

    h^2>22311/40000>22201/40000=(149/200)^2,
    h>149/200>3/5.                                       (25)

These statements use no `k1>0` guard.

## 4. Whole-domain lower bound for d1

### 4.1. A polynomial controlling its derivative

Keep `a,b` fixed, and define

    N=x*D+t,
    Q=K^2-N,
    C=a*(2*b-1)+(b/a)*(1-b)-b.

A direct expansion, using `a^2+b^2=1`, is

    Q=a^2*p^4+b*(2*a-1)*p^3+(1-b-1/a)*p^2
        +C*p+b/a+b^2-b,
    Q'=4*a^2*p^3+3*b*(2*a-1)*p^2+2*(1-b-1/a)*p+C.       (26)

For this polynomial calculation `x` need not be positive. We show
`Q>0` throughout `[0,P]`, where `P=min(b/a,(1-b)/a)` and `a,b`
come from an original parameter pair. The second derivative of
`Q'` is

                     24*a^2*p+6*b*(2*a-1)>0.

Thus `Q'` is convex on `[0,P]`. It is enough to prove that it is
negative at both endpoints.

At `p=0`, it equals `C<0`. For `b<=1/2`, the first term
`a*(2*b-1)` is nonpositive, and the remaining two give

                 b*((1-b)/a-1)<0

because `a>1-b`. For `b>=1/2`, use `b/a<1` to obtain

    C<a*(2*b-1)+(1-b)-b=(a-1)*(2*b-1)<=0.

This includes `b=1/2`.

If `b<=1/2`, then `P=b/a`, and substitution in (26) gives

    a^2*Q'(P)=a*(8*b^3-2*b^2+5*b-1)-(3*b+2*b^3).        (27)

The factor `A=8*b^3-2*b^2+5*b-1` is positive: `b>1/3` and
`b<=1/2` give `A>5/3-1-1/2=1/6`. Since
`a=sqrt(1-b^2)<1-b^2/2`,

    a^2*Q'(P)
      <(1-b^2/2)*A-(3*b+2*b^3)
       =[(2*b-1)/2]*(2+3*b^2-b^3-4*b^4)<=0.              (28)

The final bracket is greater than `2-1/8-1/4=13/8`, and the
preceding strict inequality remains strict when `b=1/2`.

If `b>=1/2`, then `P=(1-b)/a`, `0<P<=1/sqrt(3)`, and

    a=2*P/(1+P^2),    b=(1-P^2)/(1+P^2).

The endpoint derivative becomes

    Q'(P)=[2*P^4+7*P^3-4*P^2+3*P-2]/(1+P^2).           (29)

Since `P^2<=1/3`, its numerator is at most

                      -(10/3)*P^2+(16/3)*P-2.

This quadratic increases on `[0,1/sqrt(3)]`; its endpoint value
is `(16sqrt(3)-28)/9<0`, using `sqrt(3)<7/4`.

Both cases prove that `Q'` is negative on `[0,P]`. Thus
`Q(p)>=Q(P)` there. We now verify `Q(P)>0`.

For `b>=1/2`, at `p=P` we have `t=0`, `D=q=1-P>0`, and
`P<=b/a`. Consequently

    x=1-(b/a)*(1+P)<=1-P*(1+P)=q-P^2,
    Q(P)=q*(q-x)>=q*P^2>0.                              (30)

For `b<=1/2`, temporarily write `p=P=b/a`. Then

    sqrt(2)-1<p<=1/sqrt(3),
    a=1/sqrt(1+p^2),    b=p/sqrt(1+p^2),
    H=2*p/sqrt(1+p^2),  x=1-p-p^2,
    Q(P)=p*[1+5*p-2*(1+p)*sqrt(1+p^2)].                 (31)

The squared comparison in the final bracket is

    G(p)=(1+5*p)^2-4*(1+p)^2*(1+p^2)
        =-3+2*p+17*p^2-8*p^3-4*p^4.

It strictly increases on `[sqrt(2)-1,1/sqrt(3)]`, since

    G'(p)=2+p*(34-24*p-16*p^2)>0.

For example `p<3/5` makes the bracket greater than `346/25`.
At the left endpoint,

    G(sqrt(2)-1)=34-24sqrt(2)>0,
    34^2-2*24^2=4>0.

Both sides being squared in (31) are positive. Thus (31) is
positive. Together with (30), this proves

                              K^2>N                       (32)

on the entire original domain.

### 4.2. d1 increases with p

From (16) and `h=cos(gamma+delta)`,

    d1'=a/E+r*(A0-g)/E^2-g*M/K^2.                        (33)

Equations (17), (1), and (13) give

    0<M=a*D-t*(H+a*p)<a*D<a*K,
    g=N/(E*K),
    N>0.

By (32), `N*M<a*K^3`. Therefore

    a/E-g*M/K^2=[a*K^3-N*M]/(E*K^3)>0.

The middle term in (33) is positive by (14). Hence `d1'>0`
on `[p0,p]`, so it remains to bound `d1` at `p=p0`.

### 4.3. The entire lower-p endpoint

Use `z,u` from (19). At this endpoint,

    B0=(1+z)/sqrt(u)-sqrt(2).

Let `psi=atan(z)`. Define

    S=h+(1+z)/sqrt(u)
      =cos(psi+delta)+cos(psi)+sin(psi).

Then

                          d1=1+sqrt(2)-S.                 (34)

We prove `S<52/25` on the full closed interval `[0,z_star]`.
For `0<=z<=1/8`, (20) shows that `h<=h(0)`, and

    h(0)^2=2/(5-2sqrt(2))<35/38<(24/25)^2.

The first rational comparison uses `sqrt(2)<99/70`; the second
has reserve `13/23750`. Since `(1+z)/sqrt(1+z^2)` increases,

    (1+z)/sqrt(u)<=9/sqrt(65)<28/25,
    28^2*65-9^2*25^2=335>0.

Thus `S<24/25+28/25=52/25` on this interval.

For `1/8<=z<=z_star`, we have `v>5/16`. Its positive-denominator
formula makes that comparison equivalent to

    H*(16-5*z)<11,
    sqrt(1+z^2)*(16-5*z)<11sqrt(2).                     (35)

The expression on the left strictly decreases on `[0,z_star]`:
the derivative has the sign of `16*z-10*z^2-5`, whose largest
value on that interval is `36sqrt(2)-51<0`. Here
`sqrt(2)<17/12` suffices. At `z=1/8` the squared reserve in
(35) is

                     242-(65/64)*(123/8)^2=7847/4096>0.

Since `(1-v)/sqrt(1+v^2)` decreases for `v>=0`,

                 cos(delta)-sin(delta)<11/sqrt(281).

Cauchy--Schwarz applied to `(cos(psi),sin(psi))` gives

    S=(1+cos(delta))*cos(psi)+(1-sin(delta))*sin(psi)
      <=sqrt(3+2*(cos(delta)-sin(delta)))
       <sqrt(3+22/sqrt(281))
       <6sqrt(3)/5
       <52/25.                                          (36)

The penultimate inequality uses `sqrt(281)>50/3`, with squared
reserve `29/9`; the last uses `sqrt(3)<26/15`, with squared
reserve `1/225`. Both endpoints of the second interval are
included. Thus (34)--(36) prove

    d1>sqrt(2)-27/25>1/3,
    2-(106/75)^2=14/5625>0.                              (37)

Monotonicity (33) transfers this endpoint bound to every original
`p`. No `k1>0` guard has been used in Section 4.

## 5. The necessary k1>0 guard gives one uniform ratio bound

For Sections 5--8 only, assume `k1>0`. By (18), the lower-p
endpoint value is larger than the original value. By (19)--(20),
that endpoint value increases with `z=p0`. We show that it is
negative at `z=3/10`.

At that value, `u=109/100` and

    sqrt(u)<21/20,    1/sqrt(2)>70/99,
    A0>(7/10)*(20/21)+(13/10)*(70/99)
       =2/3+91/99=157/99>19/12.                         (38)

Also `sqrt(u)>26/25`, so

    u^(3/2)/sqrt(2)
       >(109/100)*(26/25)*(70/99)>4/5.

The last difference is `19/12375`. Formula (19) now gives

    w<5/7,
    g<5/sqrt(74)<7/12,
    49*74-25*144=26>0.

Hence the endpoint value of `k1` at `z=3/10` is less than
`1-19/12+7/12=0`. An original `k1>0` therefore forces

    p0>3/10,
    r=b/a<7/13,
    b<7/sqrt(218)<19/40.                                 (39)

The final squared reserve is `19^2*218-7^2*40^2=298>0`.
In particular

    a>7/8,
    1-(19/40)^2-(7/8)^2=7/800>0.                        (40)

These necessary consequences are derived from the coupled guard;
they are not added restrictions on the original theorem.

## 6. The guarded lower bound A0>77/50

From `p<r` and (39),

    x=1-r*(1+p)>1-r-r^2>29/169.                          (41)

From `p>p0`, we have

    x<(1-r)/(1+r),
    r<(1-x)/(1+x),
    29/169<x<sqrt(2)-1.                                  (42)

Eliminating `p` in (1) yields the exact formula

    A0=[1-x+((1+x)*r^2+x*(1-x))/(r*sqrt(1+r^2))]/E.      (43)

For fixed `x`, put

    A=1+x,    B=x*(1-x),    C=A-2*B=1-x+2*x^2,
    f(r)=(A*r^2+B)/(r*sqrt(1+r^2)).

Then

                    f'(r)=(C*r^2-B)/(r^2*(1+r^2)^(3/2)).

If `x>=1/3`, the numerator at the largest allowed ratio
`r_max=(1-x)/(1+x)` is

    C*r_max^2-B=(1-x)*(1-3*x)*(1+x^2)/(1+x)^2<=0.

Since `C>0`, this proves that `f` decreases throughout the
allowed ratio interval. Therefore (43) is at least its value at
`r=r_max`. That is precisely the endpoint (19) with `z=x`;
Sections 3.3--3.4 prove that this value is greater than `77/50`.

If `x<=1/3`, the identity

    f(r)^2-4*B*(A-B)
       =[(A-2*B)*r^2-B]^2/[r^2*(1+r^2)]>=0

and positivity give `f(r)>=2*sqrt(B*(A-B))`. Since
`A-B=1+x^2=E^2`,

    A0>=J(x)=(1-x)/sqrt(1+x^2)+2*sqrt(x*(1-x)).          (44)

The function `J` is strictly concave on `[29/169,1/3]`:

    J''(x)=(2*x^2+3*x-1)/(1+x^2)^(5/2)
             -1/[2*(x*(1-x))^(3/2)]<0.

Indeed the first term is at most `2/9`, while the second
subtracted positive quantity is at least `4`. At the left endpoint,

    (1-x)/sqrt(1+x^2)=140/sqrt(29402)>4/5,
    2*sqrt(x*(1-x))=2*sqrt(4060)/169>3/4.

The squared reserves are respectively `19568` and `2791` after
cross multiplication. At the right endpoint,

    (1-x)/sqrt(1+x^2)=2/sqrt(10)>5/8,
    2*sqrt(x*(1-x))=2sqrt(2)/3>15/16.

The squared reserves are respectively `6` and `23` after cross
multiplication. Thus the endpoint values of `J` are greater than
`31/20` and `25/16`, respectively. Concavity gives

                      A0>=J(x)>31/20>77/50.

Both cases establish, on the entire guarded domain,

                              A0>77/50.                   (45)

## 7. The guarded lower bound B0>-1/4

This is the only boundary-crossing argument. It does not choose a
new original mean or relax any coupling in (1).

### 7.1. Reduction to a hypothetical first crossing

Fix original `a,b` with `k1>0` and use the interval `[p0,p]`.
By (16) and (14), `B0` strictly decreases with `p`. At `p=p0`,

    B0=sqrt(2)*(a-1)>-sqrt(2)/8>-1/4                    (46)

by (40). Suppose, for contradiction, that the original value
satisfies `B0<=-1/4`. There is then a unique

                     p_c in (p0,p],    B0(p_c)=-1/4.

All strict upper bounds and `x>0` remain valid at this crossing.
By (18), `k1(p_c)>=k1(p)>0`. We prove instead that `k1(p_c)<0`.

Throughout Sections 7.2--7.5, the symbols in (1) refer to this
hypothetical crossing. Define the new auxiliary quantity

                         c=1+x+E/4.

It is not the original scalar `d`. From `B0=-1/4` and (1),

    y=x*(1+b)+E/4,
    b=(1-x)/c,
    a=sqrt(1-b^2),
    p=a*c-1,
    t=a-x*(1+b)-E/4,
    (1+p)^2=R_x=c^2-(1-x)^2
                    =4*x+(1+x)*E/2+E^2/16.              (47)

For the formula for `b`, one may first eliminate `p` from (1) to
get

    y=(1/b-1)-(1/b-b)*x,
    B0=[(1+b)*x-(1-b)]/(b*E).

The crossing equation then rearranges exactly to `b*c=1-x`.
The formula `p=a*c-1` follows from `r*(1+p)=1-x=b*c`.

### 7.2. The whole crossing interval lies between 1/4 and 7/20

The function `b(x)=(1-x)/c` strictly decreases, because

              b'(x)=-[2+(1+x)/(4*E)]/c^2<0.              (48)

If `x<=1/4`, then `E<33/32`, `c<193/128`, and

                         b>96/193>19/40,

contradicting (39). Thus `x>1/4`.

All terms defining `R_x` in (47) increase with `x>0`, so
`p(x)=sqrt(R_x)-1` strictly increases. Meanwhile
`r(x)=b(x)/sqrt(1-b(x)^2)` strictly decreases. At `x=7/20`,

    b<13/32,
    r<13/sqrt(855)<9/20,
    R_x>7/5+27/40+449/6400>(29/20)^2,
    p>9/20.

Here the comparison for `r` has squared reserve `1655`, and the
comparison for `R_x` has reserve `273/6400`. Therefore the original
strict bound `p<r` forces `x<7/20`. We have proved

                              1/4<x<7/20.                 (49)

### 7.3. On this crossing A0>157/100

From the crossing identity for `y` in (47),

                         A0=(1+b)*E+x/4.                 (50)

On the whole closed interval `[1/4,7/20]`, formulas (47)--(48)
give

    c<13/8,    b<1/2,    x/E<1/3,
    b'<-2/c^2,
    dA0/dx=b'*E+(1+b)*x/E+1/4
             <-128/169+3/4=-5/676<0.                   (51)

For these bounds, `E<11/10` gives `c<13/8`; at `x=1/4`
one has `b<1/2`, and (48) preserves it; finally
`9*(7/20)^2<1+(7/20)^2` gives `x/E<1/3`.
At the right endpoint,

    E=sqrt(449)/20>1059/1000,
    b=52/(108+sqrt(449))>2/5.

The first comparison has squared reserve `1019/1000000`; the
second uses `sqrt(449)<22`. Equations (50)--(51) therefore yield

    A0>(7/5)*(1059/1000)+7/80
       =15701/10000>157/100.                             (52)

### 7.4. Two continuous affine upper bounds for p and t

On (49) define

    p_bar=7*x/4-1/8,
    t_bar=17/40-3*x/4.                                   (53)

Both lie in `(0,1)`. We first show `p<p_bar`.
The square-root tangent gives `E<=1+x^2/2`; hence (47) gives

    R_x<=9/16+(9/2)*x+(5/16)*x^2+x^3/4.

Subtracting this upper bound from `(1+p_bar)^2` leaves

    13/64-(23/16)*x+(11/4)*x^2-x^3/4
       >=13/64-(23/16)*x+(213/80)*x^2>0.                 (54)

The last quadratic has positive leading coefficient and negative
discriminant `-31/320`. Both sides of the square-root comparison
are positive, so (47) and (54) prove `p<p_bar`.

To prove `t<t_bar`, define

    A=(78+268*x-110*x^2)/160,
    B=(57+50*x)/160.

Using (47) and multiplying by the positive `c`, the desired
inequality is exactly

                            sqrt(R_x)<A+B*E.              (55)

Both sides are positive on `[1/4,7/20]`. On this entire interval,

    A>=221/256>6/7,
    B>=139/320>3/7,
    2*A*B-(1+x)/2>36/49-27/40=117/1960>0.               (56)

Also

                       E>=1+(12/25)*x^2,                 (57)

because `x^2<25/144` makes
`(1+(12/25)*x^2)^2<=1+x^2`.
Expanding the squared right-minus-left difference in (55),
and using (56)--(57) for its coefficient of `E`, gives

    (A+B*E)^2-R_x
      =A^2+B^2*(1+x^2)-4*x-(1+x^2)/16
          +[2*A*B-(1+x)/2]*E
      >=P5(x)/640000,                                  (58)

where the complete polynomial is

    P5(x)=95625-733500*x+1779929*x^2-1299876*x^3
                       +536120*x^4-132000*x^5.

For `x=3/10+s`, the following exact identity holds:

    P5(3/10+s)
      =469377/100+(901146/25)*s+(4319527/5)*s^2
          -775332*s^3+338120*s^4-132000*s^5.              (59)

The whole interval `[1/4,7/20]` has `|s|<=1/20`. Applying the
triangle inequality to every nonconstant term in (59) proves

    P5(x)
      >=469377/100-(901146/25)/20-(4319527/5)/20^2
            -775332/20^3-338120/20^4-132000/20^5
       =1265287/2000>0.                                 (60)

This is a single printed identity and an estimate over one whole
interval. It does not require a box cover or any sign evaluation
at sample points. Equations (55)--(60) prove `t<t_bar`.

### 7.5. The same crossing has g<57/100 and k1<0

For `0<p,t<1`, the function

                            v=t/(1-p+p*t)

strictly increases with each variable: its derivatives are

    dv/dt=(1-p)/(1-p+p*t)^2>0,
    dv/dp=t*(1-t)/(1-p+p*t)^2>0.

Thus (53)--(60) imply

                   v<t_bar/(1-p_bar+p_bar*t_bar).

Set `s=7/20-x`, so `0<=s<=1/10`. A direct identity is

    (5/8-x)*(1-p_bar+p_bar*t_bar)-t_bar
      =57/256000+(221/640)*s+(941/640)*s^2-(21/16)*s^3
      >0.                                               (61)

Indeed the constant is positive, the linear term nonnegative,
and the last two terms combine as
`s^2*(941/640-(21/16)*s)>=0`. All denominators are positive,
and `5/8-x>0`, so (61) gives

                              x+v<5/8.

Consequently `x*v<25/256`, and

    tan(chi)=(x+v)/(1-x*v)<160/231,
    g<160/sqrt(78961)<57/100,
    57^2*78961-160^2*100^2=544289>0.                     (62)

Combining (52) and (62) proves

                      k1=1-A0+g<1-157/100+57/100=0.

This contradicts the positive `k1` at the hypothetical first
crossing. The contradiction includes the case in which the
original value is exactly `B0=-1/4`. Therefore the entire
original guarded domain satisfies

                               B0>-1/4.                   (63)

## 8. The remaining coupled inequality F>0

On the original domain with `k1>0`, (25), (45), and (63), together
with `g>0`, yield

    F=g^2-g+B0*g+h*(A0-1)
       >g^2-(5/4)*g+(149/200)*(27/50)
       =(g-5/8)^2-25/64+4023/10000
       >=467/40000>0.                                  (64)

This completes the four auxiliary conclusions (5)--(6) on their
stated full domains. In particular no unchecked relation between
independently varied `A0,B0,g,h` is being assumed: all three
bounds used in (64) were proved from (1) and the single necessary
guard `k1>0`.

## 9. Restoration of the original lambda and radius consequence

Return to the exact original `0<lambda<=1`. By (13),

    d=1-B0-lambda*h>=1-B0-h=d1>1/3,
    k=1-A0+lambda*g<=1-A0+g=k1<1/8,
    h>149/200>3/5.

The original assumption `k>0` implies `k1>0`; hence (64) applies.
Expanding the expressions in (1)--(2) gives exactly

    g*(g-d)=F+h*k>0.

As `g>0`, it follows that `g>d`. This proves the complete original
four-output theorem (4), including `lambda=1`. No upper bound on
the original `k`, no new restriction on `xi`, and no replacement
of the original mean has been introduced.

For completeness, the original pure scalar radius consequence
also follows unchanged. Let `0<R<25/12`, and define

    E_R=(g-d)^2+(1+h)^2
            +2*R*((g-d)*d-(1+h)*k)/sqrt(d^2+k^2).

Since `g-d,d,k` are positive,

    E_R>(1+h)*(1+h-2*R*k/d).

The proved bounds give `k/d<3/8`, so `2*R*k/d<25/16`. Since
`1+h>8/5`, both factors in the following comparison are positive:

                 E_R>(8/5)*(8/5-25/16)=3/50>0.            (65)

This remains a scalar implication. A physical caller must identify
its actual point, original selected normal and mean, true degrees,
full force and torque equations, and every physical circle-corner
mask, including zero individual weights. Nothing in this source
replaces that task or proves a whole graph/load exclusion alone.

## 10. Construction and verification provenance

The global angle and `k1` argument and the `d1` endpoint estimate
were developed by W-continuation, with root independently deriving
the fixed-`a,b` identities and suggesting the sufficient derivative
target `a*K^3>N*M`. Root supplied the guarded-ratio reduction,
the first-crossing organization, and the affine bounds and reduction
needed to close `F`; W-continuation supplied the guarded `A0` bound
and the degree-five proof of the affine bound for `t`.
Return_scalar_assembly assembled the entire source, checked all
domain transitions and positivity conditions, and independently
expanded the identities in (58)--(61). These contributions are
construction work and do not constitute the separate independent
review required for adoption.

Exploratory scalar floating-point grids were used earlier to test
possible inequalities and reject unsuccessful approaches. In
particular an unconditional proposed bound involving
`A0+B0-g>3/4` was found to be false and withdrawn. Neither that
statement nor any numerical output appears as a premise here.
An attempted optional symbolic-library import failed; no library
was installed. Exact rational arithmetic was used during assembly
to check the displayed coefficient expansions and reserves; their
complete identities and hand bounds are printed above.

No historical 475-leaf checker was rerun for this replacement.
No Lean/Lake invocation, CI or workflow dispatch, remote write,
or global gate/count modification was performed by this source's
authors. The historical certificate is retired only after full
independent review, root adoption, and an exact same-export join
to every retained original physical caller.
