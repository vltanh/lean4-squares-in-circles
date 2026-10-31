# The side-side five-cycle requires a side-interior contact at A

**Status:** complete conditional hand argument; independent mathematical reviews passed (2026-10-29).

Use the unique-circle-vertex S-S normal form from
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md). Put

```
Z=(X,Y), |Z|=R, Y>X>0, 79/40<=R<=3/sqrt(2),
p>q>0, p^2+q^2=1, rho=q/p,
Q_A=Z-(1+p,1+q), Q_B=Z-(1-d,2),
Y/X=(1-d rho)/(1-d), 0<d<1.
```

A and B are supported at Q_A,Q_B with inward normals (-p,-q),(0,-1),
and have a physical contact. The horizontal support bounds give
`d<=1-p+q`; hence the
[side-transmission proximity theorem](SIDE_TRANSMISSION_VERTEX_REDUCTION.md)
gives `|Q_A|<R-1`. That note already excludes a rightward edge at a
vertex support point. The argument here excludes the complementary
vertex frames; together they force relative side-interior support at A.

Suppose Q_A is a vertex of A and neither incident edge points right.
Write the two inward unit edges as

```
e=(-c,-s), f=(-s,c), c,s>=0, c^2+s^2=1.
```

The inward-normal condition makes s>0. The contact-proximity theorem
shows that Q_A and both adjacent vertices are circle-clear. Thus the
opposite vertex `W=Q_A+e+f` is A's sole possible circle vertex.
We prove that W is circle-clear too.

## 1. Contact geometry bounds the frame

Every point (x,y) of A lies on the inward side of its edge Q_A--(Q_A+e),
so

```
-s[x-(Q_A)_x]+c[y-(Q_A)_y]>=0.
```

Every point of B has height at most
`(Q_B)_y=(Q_A)_y-(1-q)` and horizontal coordinate at least
`(Q_B)_x-1=(Q_A)_x+d+p-1`.
Apply these bounds at the actual A--B contact and divide by s>0:

```
d<=1-p-(1-q)c/s.
```

In particular

```
d<=1-p,
c/s <=(1-p)/(1-q),
c <=(1-p)/(1-q).                                      (1)
```

The last inequality uses s<=1.

As in the reviewed side-diagonal endpoint note, the central stress relation
then gives

```
Y/X-1 <=(1-p)(1-rho)/p
       <=rho^2(1-rho)/2<=2/27.
```

The polar angle phi of Z therefore lies between pi/4 and
`phi_0=atan(29/27)`.

## 2. Compare the opposite vertex with one fixed circle point

Write

```
W=Z-K,
K=(1+p+c+s,1+q+s-c),
w=p+q, v=p-q.
```

Both coordinates of K are positive, and `K_x-K_y=v+2c>0`.
Thus its polar angle is below pi/4. For fixed K, the squared-radius
excess `|Z-K|^2-R^2=|K|^2-2R(cos(phi),sin(phi)).K` decreases with R
and increases with phi on the stated ranges. It is bounded above by its
value at `R_0=79/40`, `phi=phi_0`.

For this fixed comparison point define

```
sigma=R_0(cos(phi_0)+sin(phi_0))-2,
delta=R_0(sin(phi_0)-cos(phi_0)).
```

The elementary rational brackets, also verified in
[SIDE_DIAGONAL_LEFT_ENDPOINT.md](SIDE_DIAGONAL_LEFT_ENDPOINT.md), are

```
79/100<sigma<99/125, 0<delta<1/10.
```

They follow from
`sigma+2=553/(5sqrt(1570))`, `delta=79/(20sqrt(1570))`, and
`1981/50<sqrt(1570)<3963/100`.
The exact excess at the comparison point is

```
E=1-2sigma-sigma w+delta v
       +2[(v+delta)c+(w-sigma)s].                       (2)
```

## 3. Small q: the new frame bound gives strict clearance

Suppose q<=9/20. Then p>89/100, w<27/20, and 1-q>=11/20.
By (1), v=p-q<=1-q, and s<=1,

```
(v+delta)c
 <(v+1/10)(1-p)/(1-q)
 <=[1+1/(10(1-q))](1-p)
 <=(13/11)(1-p)<13/100.
```

Since w>1>sigma and s<=1, equation (2) gives

```
E <=1-4sigma+(2-sigma)w+delta v+2(v+delta)c
  <1-4(79/100)+(121/100)(27/20)+1/10+26/100
  =-333/2000<0.
```

## 4. Large q: the existing Cauchy estimate applies

If q>=9/20, then w>67/50 and v<9/20. Put `z=-sigma w+delta v`.
The rational bounds give

```
z<-(79/100)(67/50)+(1/10)(9/20)=-1267/1250.
```

Using c^2+s^2=1 and w^2+v^2=2, Cauchy's inequality bounds (2) by

```
E<=1-2sigma+z+2sqrt(2+2z+sigma^2+delta^2).
```

The radicand is strictly less than

```
2-2(1267/1250)+(99/125)^2+(1/10)^2
 =38129/62500<(391/500)^2.
```

Consequently

```
E<1-2(79/100)-1267/1250+2(391/500)
 =-37/1250<0.
```

Both cases prove `|W|<R`, contradicting the positive circle load on A.
Thus Q_A cannot be a nonrightward vertex of A. Together with the existing
rightward-vertex exclusion, this excludes every vertex-supported A in
the S-S branch. Only relative side support at A remains.
