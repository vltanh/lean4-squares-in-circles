# A larger local joint cap and an exact quadratic terminal

This is a hand extension of
`research/nine/JOINT_OPPOSITE_NORMAL_LOCAL_HAND_PROOF.md`.
It proves the joint five-square cap throughout the larger slope cube
`[-1/21,1/21]^4`, with no separator-owner restriction. It also gives a
finite rational test for additional boxes inside `[-1/16,1/16]^4`.
It does not claim that the complementary slope domain is covered.

Set

    Q=1105/256, r=sqrt(Q), a=46, b=27/2,
    K=207/16, T=211/4, e0=1/16, d0=729/160.

Retain the five original physical squares and separating vectors from
Section 7 of that proof, including the original central whole-floor
condition `y_P-h_P>=1/10`. Thus

    n_L=(w_L,1),    n_R=(-w_R,1),
    m_L=(-1,z_L),   m_R=(1,z_R).

Write `D=x_E_R-x_E_L-h_E_L-h_E_R`. Every square lies in the same centered
disk of radius `R0<=r`. The norm and support expressions below refer to
these squares; no frame or center is replaced by a shared one.

## 1. Sharper scalar estimate

Use the original scalar notation

    A=sqrt((a+Kw)^2+K^2),
    B=sqrt((b-Kw)^2+(K+bz)^2),
    d=sqrt(1+w^2), e=sqrt(1+z^2), p=1+wz, q=z-w,

and

    P_E=a h_E+H_E(a e_x-Kn)+K H_E(n),
    P_S=H_S(bm+Kn)+b H_S(m)+K H_S(n).

For every physical orientation and `|w|,|z|<=1/16`, one has

    r(A+B)-P_E-P_S
      <= T-(K/2)|w|+(3K/2)z-K(z-w)_+
             +(20+23*1_{w<0})w^2+19z^2.          (1)

The expression `1_{w<0}` is one for negative w and zero otherwise. Its
choice at zero makes no difference.

### Endpoint support penalty

The same edge-alignment minimum principle gives three candidates.
The coordinate-edge value is

    E0=a+K+Kw_+.

For w>=0 the n-edge value is at least E0: its excess is
`(1+w-d)(a/d-K)>=0`. For w<=0 its value is
`a/d+Kd>=a+K-23w^2`. The diagonal value is `A+aK/A`.
Its projection conditions `K^2 d^2+aKw>0` and `a^2+aKw>0` hold throughout
this larger cube. Squaring rational endpoints gives `47<A<49`.

If w<=0, the diagonal value exceeds E0 because

    47+aK/49-a-K=163/784>0.

If w>=0, use

    A-(a+Kw)=K^2/(A+a+Kw)>K^2/(49+a+Ke0).

The diagonal value minus E0 consequently exceeds

    K^2/(49+a+Ke0)+aK/49-K
      =18362349/19229168>0.

Hence, with the sign-dependent improvement retained,

    P_E>=a+K+Kw_+-23*1_{w<0} w^2.                 (2)

### Shoulder support penalty

The three candidates are again

    N=Kd+b p/d+b q_+/d,
    M=be+K p/e+K q_+/e,
    V=B+bKp/B.

Their projection formulas hold: `p>0`, `b|q|<Kd^2`, `K|q|<be^2`, and
the diagonal projection numerators `b^2 e^2+bKq` and `K^2 d^2+bKq`
are positive. For example `|q|<=1/8`, while b and K both exceed 12.

Since `d,e<101/100`, rationalization gives

    d>=1+(100/201)w^2,    e>=1+(100/201)z^2.

Retain these positive terms, and use the original elementary estimates
`1/d>=1-w^2/2`, `1/e>=1-z^2/2`,
`|wz|<=(w^2+z^2)/2`, and `q_+<=2e0`. Then

    N>=b+K+Kq_+
        -[b(1+e0)-100K/201]w^2-(b/2)z^2,
    M>=b+K+Kq_+
        -(K/2)w^2-[K(1+e0)-100b/201]z^2.

All four quadratic coefficients are below 8. The two nontrivial
reserves are

    8-[b(1+e0)-100K/201]=199/2144,
    8-[K(1+e0)-100b/201]=16643/17152.

For the diagonal candidate write

    B0=sqrt(b^2+K^2),
    cmin=bK(1-e0^2), cmax=bK(1+e0^2).

One has `35/2<B<20` and `93/5<B0<19`.
If q<=0, the function `u+cmin/u` is increasing for `u>=35/2`, so

    V>=35/2+cmin/(35/2)>b+K.

The last reserve is `28783/28672`.
If q>=0, the identity

    B^2=B0^2+2bKq+K^2w^2+b^2z^2

gives `B-B0>=2bKq/39`. On `[B0,20]`, the derivative of
`u+cmin/u` exceeds `49/100`; indeed
`(51/100)B0^2-cmax=121743/40960>0`. Therefore

    V>=93/5+cmin/19+(49/100)(2bK/39)q.

For `0<=q<=1/8` this exceeds `b+K+Kq`. It suffices to check the upper
endpoint, whose positive reserve is `12668583/50585600`. Thus

    P_S>=b+K+K(z-w)_+-8(w^2+z^2).                 (3)

### Norm remainders

The original identities `A(0)=23r`, `B(0,0)=9r`, and
`32Q-a-b-2K=T` still hold. The lower bound A>47 and
`A''=K^4/A^3` give

    rA<=23Q+2Kw+w^2.

The exact spare amount in the unit quadratic coefficient is

    1-(21/20)K^4/47^3
      =97526109739/136082882560>0.

For B, every segment from the origin remains in this cube and has norm
above 35/2. Its Euclidean-norm Hessian therefore has operator norm at
most 2/35. Taylor's theorem gives

    rB<=9Q-(3K/2)w+(3K/2)z+11w^2+11z^2,

because the two quadratic reserves are

    11-(21/10)K^2/35=12253/12800,
    11-(21/10)b^2/35=13/200.

Subtract (2) and (3) from the sum of these norm bounds and use
`w/2-w_+=-|w|/2`. This proves (1).

For completeness, the rational norm-band reserves used above are

| Comparison | Positive reserve |
|---|---:|
| `(a-Ke0)^2+K^2-47^2` | `42081/65536` |
| `49^2-(a+Ke0)^2-K^2` | `2790303/65536` |
| `(b-Ke0)^2+(K-be0)^2-(35/2)^2` | `70817/65536` |
| `20^2-(b+Ke0)^2-(K+be0)^2` | `350047/65536` |
| `B0^2-(93/5)^2` | `23481/6400` |
| `19^2-B0^2` | `2911/256` |

## 2. A joint piecewise-quadratic deficit

Define the continuous function

    F(w,z)=(K/2)|w|+K(z-w)_+-d0 z
                 -(20+23*1_{w<0})w^2-19z^2.      (4)

For every four slopes in `[-1/16,1/16]`,

    aD+b<=2T-F(w_L,z_L)-F(w_R,z_R).               (5)

To verify this, let `S=z_L+z_R`; then `|S|<=1/8<1`. The central-triangle
bound from the original proof applies:

    |S|h_P+H_P(m_L)+H_P(m_R)>=1+|S|.

When S>=0 use the actual central whole floor; when S<0 use the top of
that same physical square. After (1) is used for the two endpoints
and shoulders, the linear deficit is

    (K/2)(|w_L|+|w_R|)+K[(z_L-w_L)_++(z_R-w_R)_+]-d0 S

in the nonnegative-S case. For negative S its last term is instead
`b(39/16-r)|S|`, which is greater than `d0|S|` since `r<21/10`.
The displayed deficit is consequently a valid lower bound in both
cases. This is precisely the linear part of the sum in (5).

If `R0<r`, the inequality obtained by replacing its original radius by
r is strict. Each endpoint center coefficient has vertical component
`-K`, so at least one strict support-radius term is present, even if all
four slopes vanish. The estimates after that step cannot remove this
strictness.

At `R0=r` there is still strictness whenever at least one slope is
nonzero. The strictly positive Taylor reserves displayed in Section 1
make (1) strict for every `(w,z)!=(0,0)`; the other estimates preserve
that strictness. Thus (5) is strict at every nonzero four-slope point.
In particular a terminal whose conservative rational reserve is zero
still excludes all its nonzero slope points at the closed radius.
More quantitatively, the unused B-remainder reserves alone are
`12253/12800` on w^2 and `13/200` on z^2. Consequently (5) strengthens to

    aD+b<=2T-F(w_L,z_L)-F(w_R,z_R)
              -(13/200)(w_L^2+w_R^2+z_L^2+z_R^2).

## 3. The complete larger cube

On `|w|,|z|<=epsilon=1/21`,

    F(w,z)>=(31/1120)(|w|+|z|).                    (6)

Here is a finite sign proof. Bound `w^2<=epsilon|w|` and
`z^2<=epsilon|z|` in (4).

If z<0, drop the nonnegative term `K(z-w)_+`. The coefficients of
`|w|` are `K/2-20epsilon` for w>=0 and `K/2-43epsilon` for w<0;
the coefficient of `|z|` is `d0-19epsilon`. All exceed 31/1120.

If z>=0 and w<0, the positive part is `z+|w|`. The two coefficients
are `3K/2-43epsilon` and `K-d0-19epsilon`, again larger than 31/1120.

If z,w>=0, split into w>=z and w<=z. In either case the coefficient
on the common part `min(w,z)` is

    K/2-d0-39epsilon=153/80-39/21=31/560.

The coefficient on the remaining excess is respectively
`K/2-20epsilon` or `K-d0-19epsilon`, both larger than 31/1120.
The common part contributes twice to `|w|+|z|`, proving (6).

By (5), throughout the whole larger cube,

    aD+b<=2T-(31/1120)(|w_L|+|w_R|+|z_L|+|z_R|).

In particular the cap holds for all four owner combinations and all
central sign combinations. Its subcritical-radius version is strict.

## 4. A finite exact terminal beyond the smaller cube

For any rational rectangle `[w0,w1] x [z0,z1]` contained in
`[-1/16,1/16]^2`, one can compute the exact minimum of F by evaluating
only the following finite set:

- the four rectangle corners;
- intersections of w=0 with the horizontal rectangle edges;
- intersections of z=0 with the vertical rectangle edges;
- intersections of z=w with every rectangle edge;
- the origin, if it belongs to the rectangle.

Keep only points in the rectangle, and discard duplicates. The three
lines w=0, z=0, z=w divide the rectangle into convex polygons. On each
one, F is a quadratic with a negative definite diagonal Hessian;
therefore it is concave and attains a minimum at a polygon vertex.
All such vertices are in the list. F agrees on the shared boundaries,
including the w=0 sign change, so no limiting value is omitted.

For a four-dimensional box B, let `f_L` and `f_R` be these exact rational
minima on its `(w_L,z_L)` and `(w_R,z_R)` rectangles. The guard

    B subset [-1/16,1/16]^4   and   f_L+f_R>=0

is thus a complete rational leaf check proving the joint cap throughout
B. The strict subcritical-radius conclusion remains valid when the
sum is exactly zero. This terminal may be added to a larger finite
cover without changing that cover's existing root partition.
