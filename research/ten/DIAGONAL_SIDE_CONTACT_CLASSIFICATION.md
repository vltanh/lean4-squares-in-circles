# Contact classification at the diagonal endpoint of the D-S five-cycle

**Status:** independently audited exact conditional hand deduction.
The D-S component is not yet excluded.

Use the D-S unique-circle-vertex branch from
[DIAGONAL_SIDE_ENDPOINT_REDUCTION.md](DIAGONAL_SIDE_ENDPOINT_REDUCTION.md). Write C's loaded vertex as
`Z=(X,Y)=(a+1/2,b+1/2)`, with `Y>X>0`, `|Z|=R`, and
`79/40<=R<=3/sqrt(2)`. Put

```
rho=q/p, p=1/sqrt(1+rho^2), q=rho p,
k=sqrt(2)p-q,
0<d<=1-k,
t=Y/X=(1-d rho)/(1-d).
```

The endpoint contact reached through the diagonal transmitter is

```
Q_A=Z-(1+sqrt(2)p,1+sqrt(2)q).
```

**Claim:** `|Q_A|<R-1`. Therefore Q_A and every vertex adjacent to it
are strictly inside the containing circle. If A is vertex-supported and
loaded, its opposite vertex is its sole circle vertex.

## 1. Reducing to two scalar parameters

Since k<1, squaring `sqrt(2)sqrt(1-q^2)<1+q` gives q>1/3.
Hence `1/3<rho<1`. Also

```
1<t<=T(rho):=rho+(1-rho)sqrt(1+rho^2)/(sqrt(2)-rho).
```

We first prove the useful global bound `T(rho)<5/4`.
Put `x=1-rho`, `h=sqrt(2)-1`. The identity
`(1+h rho)^2-(1+rho^2)=2h rho(1-rho)>0` gives

```
k > (h+x)/(sqrt(2)-hx).
```

The latter lower bound exceeds `4x/(1+4x)`, because the cross-multiplied
difference is

```
h-3x+4sqrt(2)x^2
 >= h-9/(16sqrt(2))
 =23sqrt(2)/32-1 >0.
```

The last comparison follows from `23^2*2>32^2`. Consequently
`(1-k)(1-rho)/k<1/4`, which is exactly T(rho)<5/4.

The function T increases on `[1/3,2/3]`. Indeed, putting
`S=sqrt(1+rho^2)`, differentiation gives

```
T'=1+[(1-sqrt(2))S+(1-rho)rho(sqrt(2)-rho)/S]
          /(sqrt(2)-rho)^2
   >=1-(sqrt(2)-1)S/(sqrt(2)-rho)^2 >0.
```

For the last inequality use
`(sqrt(2)-1)S<(5/12)(5/4)=25/48` and
`(sqrt(2)-rho)^2>(7/5-2/3)^2=121/225>25/48`.

## 2. Monotonicity of the desired radius margin

Let

```
H(R,rho,t)=(R-1)^2-|Q_A|^2
 =2R[(1+t+sqrt(2)(p+tq))/sqrt(1+t^2)-1]
       -3-2sqrt(2)(p+q).
```

For fixed rho,t this increases with R: the bracket is positive since
`(1+t)/sqrt(1+t^2)>=1` and the remaining summand is positive.
For fixed R,rho it decreases with t>=1, because
`1+sqrt(2)p>1+sqrt(2)q`.

For fixed `1<=t<=5/4`, H(79/40,rho,t) increases with rho in `[1/3,1]`.
To see this, its rho-dependent part is

```
2sqrt(2)(A p+B q),
A=(79/40)/sqrt(1+t^2)-1>0,
B=(79/40)t/sqrt(1+t^2)-1>=A.
```

Its derivative has the sign of `B-A rho`, which is nonnegative and is
strictly positive on the intervals used below.

Thus, for rho in a row `[alpha,beta]` of the following table, it suffices
to evaluate H at R=79/40, rho=alpha, and a rational t upper bound.
For the first eight rows, monotonicity of T gives `t<=T(beta)`.
The final row uses the global t<5/4 bound.

## 3. Nine explicit rational checks

Set `D=100000` and `j=141421`; then `(j/D)^2<2`.
In the table, `u_alpha/D`, `u_beta/D`, and `v/D` are upper bounds for
`sqrt(1+alpha^2)`, `sqrt(1+beta^2)`, and `sqrt(1+(m/D)^2)`.
Each bound is verified by squaring integers. For the first eight rows,
the displayed m also satisfies the rational inequality

```
m/D >= beta+(1-beta)(u_beta/D)/(j/D-beta) > T(beta).
```

The final row sets m/D=5/4 directly.

| alpha | beta | m | u_alpha | u_beta | v | N |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 1/3 | 2/5 | 103717 | 105410 | 107704 | 144074 | 6796926173 |
| 2/5 | 9/20 | 107552 | 107704 | 109659 | 146859 | 10898674656 |
| 9/20 | 19/40 | 109384 | 109659 | 110708 | 148206 | 127392976304 |
| 19/40 | 1/2 | 111148 | 110708 | 111804 | 149513 | 218986870228 |
| 1/2 | 21/40 | 112833 | 111804 | 112944 | 150769 | 9996242795 |
| 21/40 | 11/20 | 114428 | 112944 | 114128 | 151967 | 196501795052 |
| 11/20 | 3/5 | 117293 | 114128 | 116620 | 154136 | 8751748397 |
| 3/5 | 2/3 | 120259 | 116620 | 120186 | 156405 | 8201898243 |
| 2/3 | 1 | 125000 | 120186 | 141422 | 160079 | 3185240802 |

Here is the complete integer calculation represented by the final column.
Write `alpha=A/B` in lowest terms and `u=u_alpha`. Define

```
N=79uB(D+m-v)-60uBv
       +j[79(BD+mA)-40v(A+B)].
```

The displayed N values are all positive. They give

```
H(79/40,alpha,m/D)
 >= (79/20)[(D+m)/v-1]-3
      +(2j/u)[79(BD+mA)/(40Bv)-(A+B)/B]
 = N/(20uBv) >0.
```

To justify the radical replacements in this bound, first rewrite the
rho-dependent expression as

```
2sqrt(2)/sqrt(1+alpha^2)
  *[(79/40)(1+(m/D)alpha)/sqrt(1+(m/D)^2)-(1+alpha)].
```

The bracket remains positive after replacing its square-root denominator
by v/D, since `79/40>v/D` and m/D>=1. Thus every replacement used above
has the indicated direction.

The nine intervals cover `1/3<rho<1`, so H>0 throughout the stated
parameter domain. Since R>1, this proves `|Q_A|<R-1`.

Every entry and inequality in the certificate is an explicit rational
calculation. The optional exploratory generator is not a premise of the
proof; no numerical optimization is used in this deduction.


## 4. The diagonal transmitter cannot contact a vertex of A

The vertically supported endpoint B satisfies `min_x B>=Q_B.x-1`.
Its support point differs horizontally from Q_A by `d+sqrt(2)p>1`.
Therefore every A--B contact lies strictly to the right of Q_A.

Suppose Q_A is a vertex of A. Since A reaches to its right and its
inward supporting normal is `(-p,-q)`, its incident edges have the form

```
e=(sin(psi),-cos(psi)), f=(-cos(psi),-sin(psi)),
0<psi<=arctan(q/p)<pi/4.
```

The support inequality for e is `tan(psi)<=q/p`. The other possible
rightward edge would point upward and have negative dot product with
`(-p,-q)`, so cannot occur. The opposite vertex `W=Q_A+e+f` is the sole
circle vertex by the proximity theorem. Its horizontal coordinate is
less than Q_A.x, as is that of Q_A+f. Hence the A--B contact belongs
to the two edges meeting at `E=Q_A+e`, on their portion to the right
of Q_A.

About W, every inward support force on this boundary portion has
nonnegative torque. On Q_A--E the normal is f and the torque of a unit
force at `Q_A+t e` is `1-t>=0`; on E--W the normal is -e and the torque
at `E+t f` is again `1-t>=0`. At E their nonnegative cone gives the
same conclusion.

The incoming transmitter force is a positive multiple of `(-p,-q)`
at Q_A. Its torque about W is a positive multiple of

```
(Q_A-W) cross (-p,-q)
 =p[cos(psi)+sin(psi)]-q[cos(psi)-sin(psi)]
 =(p-q)cos(psi)+(p+q)sin(psi)>0.
```

The circle force at W has zero torque about W. Thus the force system
cannot balance, a contradiction. Q_A must lie in the relative interior
of a side of A.

## 5. A necessary loaded vertex in the remaining side-support case

Put `n=(-p,-q)` and `v=(q,-p)`, an oriented orthonormal frame, and write

```
A=Q_A+[0,1]n+[-u,1-u]v, 0<u<1.
```

The two vertices on the support side have distance at most one from
Q_A and are circle-clear by the proximity theorem. Denote the opposite
vertices by

```
F=Q_A+n-u v, W=Q_A+n+(1-u)v,
E=Q_A+(1-u)v.
```

Both F and W lie strictly to the left of Q_A, because p>q. Only E is
to its right. All A--B contact points lie on the portions of the two
edges meeting at E which are to the right of Q_A.

If F carried no positive circle load, every positive circle load on A
would act at W. The incoming force at Q_A has strictly positive torque
about W, proportional to `1-u`. The A--B force has nonnegative torque:
on the near side its inward normal is n and the torque is proportional
to `1-u-t>=0` at `Q_A+t v`; on E--W its inward normal is -v and the
torque is proportional to `1-t>=0` at `E+t n`. The vertex cone at E
again preserves nonnegativity. This would contradict torque balance.
Therefore **F carries a positive circle load**. W may or may not also
lie on the circle or carry a positive load; it is not discarded.

Write `N=Q_A dot n`, `T=Q_A dot v`. The remaining side-supported case
necessarily obeys

```
R^2=(N+1)^2+(T-u)^2,
u>=T+1/2,
u q<=1-d-k.
```

The second inequality expresses containment of W relative to the loaded
F: `|W|^2-|F|^2=2(T-u)+1<=0`. The third follows from A--B horizontal
projection overlap, since `max_x A=Q_A.x+(1-u)q` and
`min_x B>=Q_B.x-1`. In particular, `d<1-k`.

Combining this result with the earlier opposite-endpoint reduction,
a surviving D-S component must have its diagonal transmitter contact
A in a side interior and its side transmitter contact a vertex of a
rotated B. These restrictions do not yet exclude that component.

The optional [exact checker](check_diagonal_side_proximity.py) verifies
all nine printed rational rows; the inequalities themselves are fully
specified in the table and do not rely on running the checker.

## 6. Two remaining load cases on the opposite side

Both N>0 and T<0. The first follows from

```
N=sqrt(2)+p+q-pX-qY >=sqrt(2)+p+q-R>0.
```

For the second, the central-square stress relation gives

```
T=(p-q)[1-X/(1-d)]<0,
```

using X=a+1/2>1 from the earlier endpoint reduction.

First suppose F carries all positive circle load on A. The total
outward circle-load vector is `lambda F`, lambda>0. Its v-component
is `lambda(T-u)<0`, whereas the incoming force at Q_A is `mu n`,
mu>0. Thus the A--B force has negative v-component. It cannot act in
the relative interior of the near side, whose inward normal is n.
The contact is therefore on E--W, including E. Write

```
P=Q_A+xi n+(1-u)v,       0<=xi<1,
f_AB=alpha n-nu v,      alpha>=0, nu>0.
```

Here alpha=0 unless P=E. Force balance gives

```
mu+alpha=lambda(N+1),       nu=lambda(u-T).
```

Taking torques about F gives

```
nu(1-xi)=u mu+alpha.
```

Substitution yields the exact restriction

```
uN+T=-xi(u-T)-(1-u)alpha/lambda<=0,
```

and therefore

```
u<=min(-T/N, (1-d-k)/q).
```

This includes the possibility that W lies on the circle but has zero
circle-load coefficient.

Alternatively, if W also carries a positive circle load, it lies on the
circle alongside F. Equality of their squared norms gives

```
u=T+1/2,
N=sqrt(R^2-1/4)-1.
```

The horizontal overlap inequality `u q<=1-d-k` still applies.
These two load cases exhaust the side-supported A, because its other
vertices are strictly circle-clear. Neither case is excluded by this
note.
