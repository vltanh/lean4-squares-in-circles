# A side transmitter cannot meet a right-extending vertex of its loaded endpoint

**Status:** exact conditional hand proof; independent mathematical audit passed (2026-10-29).

Use the unique-circle-vertex form from
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).
U is a side transmitter at C's bottom-left vertex; V may be side or
diagonal at C's bottom-side interior. Let its width be W_V, either 1
or sqrt(2). Put

```
Z=(X,Y)=(a+1/2,b+1/2), |Z|=R,
79/40<=R<=3/sqrt(2), Y>X>0,
p>q>0, p^2+q^2=1, rho=q/p,
0<d<1, Y/X=(1-d rho)/(1-d).
```

The support points of A and B are

```
Q_A=Z-(1+p,1+q),
Q_B=(X-1+d,Y-1-W_V).
```

A square supported at Q_A with inward normal (-p,-q) extends right by
at most q. A square supported at Q_B with inward normal (0,-1) extends
left by at most one. The physical A--B contact therefore gives

```
d<=1-p+q.
```

## 1. A uniform contact proximity bound

**Claim:** `|Q_A|<R-1`. Consequently Q_A and any vertices adjacent to Q_A
are strictly inside the circle. A vertex-supported loaded A can have only
its opposite vertex on the circle.

Let `theta=atan(rho)`, so p=cos(theta), q=sin(theta), and
`0<theta<pi/4`. The stress relation and projection bound give

```
Y/X <=rho+(1-rho)/(p-q)
     =rho+sqrt(1+rho^2)
     =tan(pi/4+theta/2).
```

Thus the polar angle phi of Z lies in `[pi/4,pi/4+theta/2]`.
The vector `K=(1+p,1+q)` has polar angle strictly below pi/4.
For fixed R, the scalar product Z.K decreases as phi increases on this
interval. Set h=theta/2. At the largest allowed phi,

```
(Z.K)/R =cos(phi)+sin(phi)+cos(phi-theta)
         =sqrt(2)cos(h)+cos(pi/4-h)
         =[3cos(h)+sin(h)]/sqrt(2).
```

Since `|K|^2=3+2(p+q)`, we obtain

```
(R-1)^2-|Q_A|^2
 >= H(R,h)
 :=sqrt(2)R[3cos(h)+sin(h)]-2R-2
      -2cos(2h)-2sin(2h),
0<h<pi/8.
```

H increases with R: its R derivative is
`sqrt(2)[3cos(h)+sin(h)]-2>0`.
It decreases strictly with h throughout the stated radius window. To see
this write c=cos(h), s=sin(h); then

```
H_h=sqrt(2)R(c-3s)-4[cos(2h)-sin(2h)],
cos(2h)-sin(2h)=(c-3s)(c+s)+2s^2.
```

If c-3s>=0, use sqrt(2)R<=3 and c+s>=1 to get
`H_h<=-(c-3s)-8s^2<0`. If c-3s<0, the first term in H_h is negative
and the second is nonpositive because h<=pi/8. Hence H_h<0 again.

It remains to check one endpoint:

```
H(R,h) >= H(79/40,pi/8)
 = (79/40)sqrt(10+7sqrt(2))-79/20-2-2sqrt(2)>0.
```

Here `sqrt(2)[3cos(pi/8)+sin(pi/8)]=sqrt(10+7sqrt(2))` follows by
squaring positive quantities. The final strict comparison is equivalent
to

```
79sqrt(10+7sqrt(2)) > 238+80sqrt(2).
```

Both sides are positive. Their squared difference is

```
5607sqrt(2)-7034 >5607(4/3)-7034=442>0,
```

using sqrt(2)>4/3. Therefore `(R-1)^2>|Q_A|^2`. Since R>1, this proves
the claim without numerical bounds or a finite interval table.


## 2. A rightward edge would force C close to the diagonal ray

Suppose Q_A is a vertex of A and an incident edge points strictly right.
The inward supporting normal `(-p,-q)` makes that edge point down; its
companion points left and down. Write

```
e=(sin(psi),-cos(psi)), f=(-cos(psi),-sin(psi)),
0<psi<=atan(q/p)<pi/4.
```

By Section 1, only the opposite vertex `W=Q_A+e+f` can lie on the
circle, so it carries all positive circle load on A. The incoming force
at Q_A is a positive multiple of `(-p,-q)` and has torque about W
proportional to

```
(p-q)cos(psi)+(p+q)sin(psi)>0.
```

Consequently the A--B force must have negative torque about W. Every
point of A strictly to the right of Q_A lies on the two boundary edges
meeting at `E=Q_A+e`, and their inward force cones have nonnegative
torque about W: on Q_A--E the unit normal f gives torque 1-t at
`Q_A+t e`; on E--W the normal -e gives torque 1-t at `E+t f`.
The same holds for the cone at E. Thus the actual contact point has
horizontal coordinate at most Q_A.x.

Since `min_x B>=Q_B.x-1`, horizontal overlap now forces

```
d<=1-p.                                                (1)
```

Using the central-square stress relation,

```
Y/X-1 <=(1-p)(1-rho)/p
       =(sqrt(1+rho^2)-1)(1-rho)
       <=rho^2(1-rho)/2<=2/27.
```

The last two inequalities follow from
`sqrt(1+rho^2)<=1+rho^2/2` and
`4/27-rho^2(1-rho)=(rho-2/3)^2(rho+1/3)>=0`.
Therefore the polar angle of Z obeys

```
pi/4<phi<=phi_0=atan(29/27).
```

## 3. In that narrow angle range A is circle-clear

Put `c=cos(psi),s=sin(psi),w=p+q,v=p-q` and define

```
sigma=X+Y-2, delta=Y-X.
```

The angle and radius bounds imply

```
79/100<sigma<=1,       0<delta<11/100.                  (2)
```

Indeed X+Y is at least `(79/40)(56/sqrt(1570))>279/100`;
the strict comparison follows by squaring. The upper bound uses
`X+Y<=sqrt(2)R<=3`. Also
`delta<= (3/sqrt(2))(2/sqrt(1570))=3sqrt(2)/sqrt(1570)<11/100`.

The opposite vertex W equals Z-K, where

```
K=(1+p+c-s, 1+q+c+s).
```

Expanding its squared-radius excess gives

```
|W|^2-R^2
 =1-2sigma-sigma w+delta v
    +2(w-sigma)c-2(v+delta)s.                          (3)
```

Here w>1>=sigma and v+delta>0. Since c<=1 and s>=0,

```
|W|^2-R^2
 <=1-4sigma+(2-sigma)w+delta v
 <1-4(79/100)+(121/100)(71/50)+11/100
 =-1659/5000<0.
```

We used w<=sqrt(2)<71/50 and v<1. Thus W is strictly inside the
circle. The other vertices were already circle-clear by Section 1,
contradicting the positive circle load of A. This proves the theorem:
a side transmitter cannot meet a right-extending vertex of A.

## 4. Consequences for the two remaining transmitter choices

In the S-D case,
[SIDE_DIAGONAL_LEFT_ENDPOINT.md](SIDE_DIAGONAL_LEFT_ENDPOINT.md)
already excludes a vertex-supported A having no rightward edge.
Combining the two exclusions shows that **the S-D transmitter must
contact A in a relative side interior**.

In the S-S case, this note excludes a rightward edge at a vertex contact.
A vertex contact with no rightward edge, or a side-interior contact,
remains possible under the present reductions. Neither the full S-D
component nor the full S-S component is excluded here.
