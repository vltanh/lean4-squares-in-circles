# Exclusion of the side-diagonal unique-circle-vertex five-cycle

**Status:** independently audited hand proof (2026-10-29).
No Lean verification is claimed.

Use the physical positive component `A-U-C-V-B-A`, with A,B,C loaded,
U a side transmitter, V a diagonal transmitter, and C having a unique
circle vertex. Work in the radius window `79/40<=R<=3/sqrt(2)` and the
normal form of [SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).

**Theorem.** This S-D component is impossible. The proof retains the
original physical contact points and forces. It does not assert the
unrestricted n=10 lower bound.

## 1. The remaining contact shape

Write C's circle vertex as Z=(X,Y), with `Y>X>0`, `|Z|=R`, and set

```
p>q>0, p^2+q^2=1, rho=q/p,
k=p-q, w=p+q,
0<d<1, tau=Y/X=(1-d rho)/(1-d).
```

The two endpoint support points are

```
Q_A=Z-(1+p,1+q),
Q_B=Z-(1-d,1+sqrt(2)).
```

Their inward support normals are respectively `n=(-p,-q)` and `(0,-1)`.
The projection bound is `d<=1-k`.
[SIDE_TRANSMISSION_VERTEX_REDUCTION.md](SIDE_TRANSMISSION_VERTEX_REDUCTION.md)
proves `|Q_A|<R-1` and, combined with the earlier no-rightward-vertex
exclusion, proves that Q_A is in the relative interior of a side of A.
Consequently, writing `t=(q,-p)`,

```
A=Q_A+[0,1]n+[-u,1-u]t,        0<u<1.
```

Denote its vertices by

```
G=Q_A-u t, E=Q_A+(1-u)t,
F=Q_A+n-u t, W=Q_A+n+(1-u)t.
```

G and E are strictly circle-clear: each has distance at most one from
Q_A, whose norm is less than R-1.

## 2. The far vertex F must carry a positive circle load

B lies below its supporting line through Q_B, whose height is
`(Q_A)_y+q-sqrt(2)`. The entire near side G--E lies strictly above B:
its minimum height is `(Q_A)_y-(1-u)p>(Q_A)_y-p`, and
`p+q<sqrt(2)`. The vertex F is above B too, since

```
F_y=(Q_A)_y-q+up>(Q_A)_y-q>(Q_A)_y+q-sqrt(2).
```

Here `2q<sqrt(2)`. Therefore an A--B contact lies on E--W or F--W,
or at W.

Suppose F carried no positive circle load. Then all positive circle load
on A would act at W, so W would be a circle vertex. Two packed squares
cannot share a point of the containing circle; the elementary proof is
in Section 1 of
[VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).
Thus the A--B contact is in the relative interior of one of those edges.

About W, the incoming force at Q_A has strictly positive torque,
proportional to `1-u`. On E--W the inward normal is -t, whose unit torque
at `E+xi n` is `1-xi>0`. That edge cannot supply torque balance.
The contact must therefore be on F--W, whose inward normal is -n.
Both contact forces on A are then parallel to n. Force balance with
the positive circle load at W forces W parallel to n, so W dot t=0.
But `F=W-t` would have squared norm `R^2+1`, outside the disk.
This contradiction proves that **F carries a positive circle load**.

## 3. Two geometric bounds on the slide u

Let

```
N=Q_A dot n, T=Q_A dot t,
c=(p+q tau)/sqrt(1+tau^2), e=(p tau-q)/sqrt(1+tau^2).
```

Then

```
N=1+w-Rc, T=k-Re,
|F|^2=(N+1)^2+(T-u)^2.
```

Horizontal A--B projection overlap gives

```
u <= U_g:=(1-d-k)/q.                                   (1)
```

Indeed A's rightmost vertex is E, while B extends left from Q_B by
at most one. The lowest point of A is W. Since A touches B, its height
cannot exceed B's supporting height, giving

```
(Q_A)_y-q-(1-u)p <= (Q_A)_y+q-sqrt(2),
u <= U_v:=1-(sqrt(2)-2q)/p.                             (2)
```

If U_v<=0, this already contradicts u>0. We may therefore assume U_v>0.
We will prove the two uniform estimates

```
0<N<27/40,
0<u-T<1.                                              (3)
```

They imply

```
|F|^2 < (67/40)^2+1=6089/1600
       <6241/1600=(79/40)^2<=R^2,
```

contradicting F's positive circle load.

## 4. The normal coordinate N is less than 27/40

Put `theta=atan(rho)` and h=theta/2, so `0<h<pi/8`. The stress and
projection bounds imply that the polar angle of Z lies between pi/4
and `pi/4+h`, as proved in the contact-proximity note. Thus

```
c>=cos(pi/4-h),
N<=J(h):=1+cos(2h)+sin(2h)-(79/40)cos(pi/4-h).
```

The second derivative satisfies

```
J''(h)=-4[cos(2h)+sin(2h)]+(79/40)cos(pi/4-h)<-2.
```

At `h_0=pi/12`,

```
J(h_0)=3/2-39sqrt(3)/80,
J'(h_0)=sqrt(3)-159/80.
```

The bound on the second derivative gives the tangent quadratic bound
`J(h)<=J(h_0)+J'(h_0)(h-h_0)-(h-h_0)^2`. Completing the square yields

```
J(h)<=J(h_0)+J'(h_0)^2/4
     =82881/25600-237sqrt(3)/160
     <86397/128000<27/40.
```

The rational comparison uses `sqrt(3)>173/100`, verified by squaring.
For the lower bound, the polar angle of Z is at least pi/4, so
`c<=w/sqrt(2)`. Therefore

```
N>=1+w-(3/sqrt(2))(w/sqrt(2))
  =1-w/2>=1-1/sqrt(2)>0.
```

## 5. Reducing the tangential extent to two endpoints

Set

```
z=(1-d)/k>=1,
a=U_v=1-(sqrt(2)-2q)/p,
C_*=(sqrt(2)-2q)/(pk),      a=1-k C_*.
```

Here k>0 and `0<a<1`. The central-square stress equation gives

```
-T = pR/sqrt(z^2+2qz+1)-k,                             (4)
U_g = k(z-1)/q.
```

For example, writing
`S_d=sqrt((1-d)^2+(1-d rho)^2)`, one has
`T=k(1-R/S_d)` and
`S_d=(k/p)sqrt(z^2+2qz+1)`, which proves (4).
Since `S_d<=sqrt(2)<R`, T<0. Thus u-T is positive.

The bounds (1)--(2) give

```
u-T <= min(U_g,a)-T.
```

The two upper bounds cross at

```
z_0=1+qa/k>=1.
```

On `[1,z_0]` the resulting expression is

```
G(z)=k(z-1)/q +pR/sqrt(z^2+2qz+1)-k.
```

It is convex: the second derivative of its nonlinear term has positive
numerator `2(z+q)^2-p^2>0`. On `[z_0,infinity)` the expression is

```
H(z)=a+pR/sqrt(z^2+2qz+1)-k,
```

which decreases. Therefore its maximum for z>=1 is bounded by the
larger of G(1) and G(z_0). The same bound holds if the physical interval
for z ends before z_0.

At z=1, using `p^2=(1-q)(1+q)` and `R<=3/sqrt(2)`,

```
G(1)<= (3/2)sqrt(1-q)-p+q
     < (1/2)sqrt(1-q)+q <1.
```

The first strict inequality uses `p>sqrt(1-q)` for 0<q<1. The second
uses q<1/sqrt(2)<3/4, so `(1/2)sqrt(1-q)<1-q`.
It remains to bound G(z_0).

## 6. Two elementary estimates at the crossing

First,

```
5/4<C_*<=sqrt(2).                                      (5)
```

Rationalization gives

```
C_*=sqrt(2)(p+q)/[p(1+sqrt(2)q)]
   =sqrt(2)(1+rho)/(1+sqrt(2)q).
```

The upper bound follows from p>=1/sqrt(2). For the lower bound, the
function `q(rho)=rho/sqrt(1+rho^2)` is concave on [0,1]. Its tangent
at rho=1/3 gives

```
q <= (1+27rho)/(10sqrt(10)).
```

Since `4-27/(2sqrt(10))<0` and rho<=1, it follows that

```
4+4rho-5q
 >=4-1/(2sqrt(10))+rho[4-27/(2sqrt(10))]
 >=8-14/sqrt(10)>5/sqrt(2).
```

For the last comparison, multiply by sqrt(10) and use

```
8sqrt(10)-14>282/25>45/4>5sqrt(5),
```

which follow from `sqrt(10)>79/25` and `sqrt(5)<9/4`.
The displayed lower bound is equivalent to C_*>5/4.

Next put

```
B_0=k z_0=p-qk C_*,
D^2=B_0^2+2qB_0 k+k^2=(B_0+qk)^2+p^2k^2.
```

We claim

```
D^2>25p^2/28.                                         (6)
```

Let `b=sqrt(2)-1<3/7`. By (5),
`B_0+qk=p+qk(1-C_*)>=p-bqk>0`. Consequently

```
D^2/p^2 >=(1-b rho k)^2+k^2.
```

If rho<=4/5, completion of the square in k gives

```
(1-b rho k)^2+k^2 >=1/(1+b^2rho^2)
                    >1225/1369>25/28.
```

If rho>=4/5, the function
`rho k=rho(1-rho)/sqrt(1+rho^2)` decreases on this interval:
its derivative has the sign of `1-2rho-rho^3<0`. Hence

```
rho k<=4/(5sqrt(41))<1/8,
```

where the strict comparison is `1024<1025` after squaring. Therefore

```
D^2/p^2 >=1-2b rho k>1-b/4>25/28.
```

This proves (6) in both cases.

## 7. Strict circle clearance and the contradiction

At the crossing point,

```
G(z_0)=a-k+pRk/D
      =1+k[pR/D-(1+C_*)].
```

By (5)--(6),

```
pR/D < (2sqrt(7)/5)R
      <=3sqrt(14)/5<9/4<1+C_*.
```

The middle strict comparison follows from `2016<2025` on squaring.
Thus G(z_0)<1. Together with G(1)<1 and Section 5, this proves
`u-T<1`. Section 4 proved the other estimate in (3). The positive-load
vertex F is consequently strictly inside the circle, the required
contradiction.

All parts of this exclusion use elementary analytic inequalities and
physical force balance. No numerical search or generated interval table
is a premise.
