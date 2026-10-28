# A side-to-diagonal mixed cycle needs a rightward edge at its first endpoint

Use the unique-circle-vertex normal form in
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md) for the
positive component `A-U-C-V-B-A`, with precisely A,B,C loaded. Suppose
U is a side transmitter and V a diagonal transmitter. If the contact
reached on A is a vertex, then A must extend strictly to its right in
C's own coordinate frame.

This is a conditional hand reduction. It does not exclude a rightward
edge at that vertex or a contact in a side of A, and therefore does not
exclude the whole side-to-diagonal case.

## 1. The contact and force coordinates

Retain the disk center as origin, and write

```text
c_C=(a,b),         b>a>0,
Z=(A_0,B_0)=(a+1/2,b+1/2)=R(cos(phi),sin(phi)),
79/40<=R<=3/sqrt(2).
```

The two contacts on C and their outgoing unit directions are

```text
P=(a-1/2,b-1/2),         (-p,-q),
Q=(a-1/2+d,b-1/2),       (0,-1),
0<d<1,                  p>q>0, p^2+q^2=1.
```

Set `rho=q/p`. Force and torque balance on C, as derived in the normal
form, imply

```text
(B_0-A_0)/A_0 = d(1-rho)/(1-d).                         (1)
```

The width-one transmission through U reaches A at

```text
P_A=Z-(1+p,1+q).
```

The diagonal transmission through V reaches B at
`Q_B=(a-1/2+d,b-1/2-sqrt(2))`, with inward normal `(0,-1)`.
Consequently B is wholly below that horizontal line. Also its leftward
extent from Q_B is at most one, by the one-sided support bound used in
[DIAGONAL_MIXED_FIVE_CYCLE.md](DIAGONAL_MIXED_FIVE_CYCLE.md).

Suppose P_A is a vertex of A and A has no point strictly to its right.
The two incident unit edges then have directions

```text
(-cos(chi),-sin(chi)), (-sin(chi),cos(chi)),
0<=chi<=pi/2.
```

Because A touches B, their horizontal projections overlap. Hence

```text
d<=1-p.                                                (2)
```

Their vertical projections also overlap, which gives

```text
sin(chi)>=sqrt(2)-q,
q>=sqrt(2)-1,            chi>pi/4.                      (3)
```

In particular `q>2/5` and `p<23/25`.

## 2. The loaded vertex of C is close to the diagonal ray

Equations (1)--(2) imply

```text
B_0/A_0-1
 <= (1-p)(1-rho)/p
  = (sqrt(1+rho^2)-1)(1-rho)
 <= rho^2(1-rho)/2
 <= 2/27.
```

The square-root inequality follows by squaring
`sqrt(1+rho^2)<=1+rho^2/2`. The cubic has maximum `4/27` on `[0,1]`,
as follows either by differentiation or from
`4/27-rho^2(1-rho)=(rho-2/3)^2(rho+1/3)`.
Thus

```text
pi/4<phi<=phi_0:=atan(29/27).                           (4)
```

The contact point P_A itself satisfies `|P_A|<3/4`. Here are rational
bounds making this explicit. Since

```text
cos(phi_0)=27/sqrt(1570)>2/3,
sin(phi_0)=29/sqrt(1570)<3/4,
```

we have

```text
79/60<A_0<=3/2,
13/10<B_0<51/32.
```

For the lower bound on B_0 use `R>=79/40` and
`1/sqrt(2)>2/3`. Since `7/10<p<23/25` and `q<71/100`, it follows that

```text
-61/100<(P_A)_x<0,
-41/100<(P_A)_y<41/100,
|P_A|^2<(61/100)^2+(41/100)^2=2701/5000<9/16.
```

Therefore P_A and its two adjacent vertices in A have norm less than
`3/4+1=7/4<R`. Only the opposite vertex needs a further estimate.

## 3. The opposite vertex is strictly inside the circle too

Put

```text
w=p+q,      v=p-q,
c=cos(chi), s=sin(chi),
K=(1+p+c+s,1+q+s-c).
```

The opposite vertex of A is `Z-K`. Both coordinates of K are positive,
and `K_x-K_y=v+2c>0`. For fixed K, the expression

```text
|Z-K|^2-R^2=|K|^2-2R(cos(phi),sin(phi)) dot K
```

decreases with R. On the angle interval (4), its maximum occurs at
`phi=phi_0`, since K's polar angle is below `pi/4`. It is consequently
enough to bound it at `R=79/40`, `phi=phi_0`.

For this one fixed comparison point, set

```text
sigma=(79/40)(cos(phi_0)+sin(phi_0))-2,
delta=(79/40)(sin(phi_0)-cos(phi_0)).
```

Their elementary rational bounds are

```text
79/100<sigma<99/125,
0<delta<1/10.                                          (5)
```

Indeed `sigma+2=553/(5sqrt(1570))` and
`delta=79/(20sqrt(1570))`; use
`1981/50<sqrt(1570)<3963/100` and square the displayed positive
quantities. Direct expansion now gives the exact excess

```text
E=1-2sigma-sigma w+delta v
  +2[(v+delta)c+(w-sigma)s].                            (6)
```

If `q<=9/20`, then

```text
33/25<w<27/20,          v<51/100,          c<7/25.
```

For the first bounds, the function `q+sqrt(1-q^2)` increases on
`0<=q<=1/sqrt(2)`, and `q>=sqrt(2)-1>41/100`; its value at `41/100`
exceeds `33/25`, while its value at `9/20` is less than `27/20`.
Also `p<23/25` and `q>41/100` give `v<51/100`. Finally (3) gives
`s>=sqrt(2)-q>24/25`, hence `c<7/25`.
Using these estimates, (5), and `s<=1`, equation (6) gives

```text
E < 1-2(79/100)-(79/100)(33/25)+(1/10)(51/100)
    +2[((51/100)+(1/10))(7/25)+((27/20)-(79/100))]
  = -551/5000 < 0.                                     (7)
```

If `q>=9/20`, then `w>67/50` and `v<9/20`. The first follows from
`sqrt(319/400)>89/100`; for the second use `p<9/10`.
Write `z=-sigma w+delta v`. Then

```text
z<-(79/100)(67/50)+(1/10)(9/20)=-1267/1250.
```

By Cauchy's inequality, the last term of (6) is at most

```text
2sqrt((v+delta)^2+(w-sigma)^2)
 =2sqrt(2+2z+sigma^2+delta^2),
```

using `v^2+w^2=2`. Its radicand is less than

```text
2-2(1267/1250)+(99/125)^2+(1/10)^2
 =38129/62500 < (391/500)^2.
```

Consequently

```text
E < 1-2(79/100)-1267/1250+2(391/500)
  = -37/1250 < 0.                                      (8)
```

Equations (7)--(8) prove that the opposite vertex also has norm less
than R. Every vertex of A is therefore strictly inside the containing
circle, contradicting its positive circle load.

Thus a surviving S-D pattern with vertex-supported A must have an
incident edge pointing strictly right from its contact P_A.
