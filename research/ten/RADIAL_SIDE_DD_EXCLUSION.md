# Exclusion of the radial-side double-diagonal five-cycle

Independent mathematical review passed on 2026-10-29; this is not Lean verification.

Use the physical positive component `A-U-C-V-B-A`, with exactly A,B,C
circle-loaded and U,V unloaded diagonal transmitters. Assume the radius
window

```
5/2+sqrt(2)<R^2<=9/2.
```

The lower window and its pinned n=8 dependency are stated in
[RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md).
The actual transmission directions and the original positive A--B
contact force are retained throughout.

**Theorem.** If C has two vertices on the containing circle, this
component is impossible. Together with the earlier S-S and S-D
exclusions, this closes the radial-side central-square branch of the
three-loaded five-cycle. It does not exclude the remaining
unique-circle-vertex central-square branches or other cyclic components.

## 1. Previously proved restrictions and notation

By [RADIAL_SIDE_DOUBLE_DIAGONAL.md](RADIAL_SIDE_DOUBLE_DIAGONAL.md),
only the following domain needs treatment, after reflection:

```
C=[-L-1,-L] x [-1/2,1/2],
sqrt(2)-1/2<L<1,
0<=eta<pi/12<theta<pi/4,
2 theta+eta>=pi/4.
```

Write `p=cos(theta),q=sin(theta),r=cos(eta),s=sin(eta)`.
The upper transmission starts at C's corner, and the lower contact is
at height `-h`, where `0<h<=1/2`; if h<1/2, eta=0. Their far endpoints
and their height difference are

```
Q_A=(-L+sqrt(2)p, 1/2+sqrt(2)q),
Q_B=(-L+sqrt(2)r, -h-sqrt(2)s),
d=1/2+h, delta=theta+eta,
D_y=(Q_A-Q_B)_y=d+sqrt(2)(q+s).
```

The square A is wholly in y>0. The positive A--B contact consequently
has positive height and B reaches positive height. Exact separation of
U and V gives

```
d(p+q)>=sqrt(2)cos(delta).                              (1)
```

The vertical-projection condition for A and B to touch is
`d<=p+r-sqrt(2)(q+s)`. It implies `delta<pi/4`: if h<1/2,
then eta=0 and this is already known; if h=1/2 and delta>=pi/4,
then `q+s>=sin(delta)>=1/sqrt(2)` and `p+r<2`, contradicting
`1<=p+r-sqrt(2)(q+s)`.

A particularly useful consequence of (1) is

```
D_y >= sqrt(2)[cos(delta)/(p+q)+q+s]
     = sqrt(2)[p(r+s)/(p+q)+q]
     >= sqrt(2)[p/(p+q)+q]
     > sqrt(2).                                        (2)
```

The strict inequality follows from
`p/(p+q)+q-1=q(p+q-1)/(p+q)>0`.

For Sections 2--4, abbreviate `Q_B=(x,-y)`, where
`x=sqrt(2)r-L` and `y=h+sqrt(2)s`.

## 2. Side support cannot be both loaded and reach positive height

Put `Q=Q_B` and `n=(r,-s)`. Suppose Q is a side point.
Put `t=(s,r)` and write

```
B=Q+[0,1]n+[-u,1-u]t, 0<=u<=1.
```

Positive height in B requires `-y+(1-u)r>0`, so
`0<=u<u_*:=1-y/r`. Each labelled vertex has squared norm convex in u;
it suffices to bound its positions at `u=0` and `u=u_*`.
The parameter bounds give

```
0<x<1/2, x+r<3/2,
0<=s<3/10, r>9/10,
r+s<=sqrt(6)/2,
y+s=h+(sqrt(2)+1)s<5/4.
```

For x>0 use `sqrt(2)r>(sqrt(3)+1)/2>17/16>L`.
The upper bounds on x and x+r use `L>sqrt(2)-1/2`.
The bound on r+s follows by monotonicity on `[0,pi/12]`.
The last inequality uses `sqrt(2)+1<5/2` and `s<3/10`.

The two vertices on the support side have horizontal coordinates
between x-s and x+s, so their absolute horizontal coordinates are
less than 4/5. Their heights lie between -r and r, by `u<=u_*`.
Their squared norms are less than `41/25`.

The lower vertex of the opposite side is `Q+n-u t`.
At u=0 its coordinates `(x+r,-y-s)` give squared norm below
`(3/2)^2+(5/4)^2=61/16`.
At u=u_* its coordinates are

```
(x+r-s+ys/r, -r-s).
```

Its horizontal coordinate is positive and at most x+r<3/2,
because y/r<=1. Its squared norm is below
`(3/2)^2+(sqrt(6)/2)^2=15/4`.

The upper vertex of the opposite side is `Q+n+(1-u)t`.
At u=u_* it has coordinates `(x+r+ys/r,-s)`, whose squared norm is
less than `(9/5)^2+(3/10)^2=333/100`.
At u=0 it has coordinates `(x+r+s,r-h-(sqrt(2)+1)s)`.
If h=1/2, its height is at most 1/2 and greater than
`9/10-1/2-(5/2)(3/10)=-7/20`, so its absolute height is at most 1/2.
Its squared norm is then below `(9/5)^2+(1/2)^2=349/100`.
If h<1/2, then eta=0 and the squared norm is below
`(3/2)^2+1=13/4`.

Every displayed squared-norm bound is below
`(79/40)^2=6241/1600`, and the present lower radius window implies
R>79/40. Convexity in u proves that all four vertices are circle-clear.
Thus a loaded endpoint B reaching positive height must have vertex
support at Q.

## 3. For vertex support, only the opposite vertex can be loaded

For this subsection assume also L<1, as in the remaining low-radius DD
branch. We first show `|Q|<R-1`.

The squared norm

```
|Q|^2=2+L^2+h^2-2sqrt(2)L cos(eta)+2sqrt(2)h sin(eta)
```

increases with h and eta in the parameter range and decreases with L,
since x>0. Hence

```
|Q|^2 < ((sqrt(3)+2)/2-sqrt(2))^2+3/4
       < (181/400)^2+3/4
       =152761/160000
       <(489/500)^2.
```

The bound `((sqrt(3)+2)/2-sqrt(2))<181/400` follows from
`sqrt(3)<1733/1000` and `sqrt(2)>707/500`.
The radius hypothesis gives `R>989/500`, so `|Q|<R-1`.
Consequently Q and both vertices adjacent to Q are strictly inside the
circle. If B is loaded, its opposite vertex W is its sole circle vertex.

## 4. Torque restricts the frame at a positive-height A--B contact

Assume the opposite endpoint A is wholly in y>0, and the component has
the original positive A--B contact and physical force balance. Write
B's edges at Q as

```
e=(cos(phi),sin(phi)), f=(sin(phi),-cos(phi)),
E=Q+e, F=Q+f, W=Q+e+f.
```

Reaching positive height requires `sin(phi)>y`; support requires
`phi+eta<=pi/2`.
The component force-sum functional
`H(X,Y)=Y-X/[2(L+1)]` shows `W_y<0`: all circle vertices of A are
above zero, both circle vertices of C have H>=0, and every point of
A or B has horizontal coordinate at most `2sqrt(2)-L<L+1`.
For a circle vertex with positive height, H is strictly positive:
if its horizontal coordinate is nonpositive this is immediate; if
`0<X<L+1`, the circle equation gives `Y>1/2>X/[2(L+1)]`.
If W were above zero, its H value would also be strictly positive;
if W had height zero, then `W_x>0` (both incident edges point
right) and the circle equation would give `W_x=R>L+1`, contradicting
that horizontal bound. The sum of all positive circle loads could not
vanish unless W is below zero.

Now Q,F,W have negative heights, while E has positive height. The
positive-height A--B contact must lie on Q--E, E--W, or at E. The
inward normal on Q--E is f; its torque about W is nonnegative, and
strictly positive in the relative interior. The inward normal on E--W
is -e; its torque about W is strictly positive away from W. At E,
the inward normal cone is generated by f and -e, with torques zero
and positive respectively. Hence the A--B force has nonnegative torque
about W.

The incoming transmitter force at Q, a positive multiple of
`n=(cos(eta),-sin(eta))`, has torque about W proportional to

```
(Q-W) cross n = sin(phi+eta)-cos(phi+eta).
```

The circle force acts at W and has zero torque there. Torque balance
therefore gives

```
phi+eta <= pi/4.
```

Equality can occur only when the A--B contact is at E with inward force
parallel to f; it is not discarded without an additional argument.
For a lower-corner contact h=1/2, positive height and this frame bound
imply the strict necessary inequality

```
cos(eta)-3sin(eta)>1/sqrt(2).
```

## 5. The frame and boundary of A

Write the frame angle in B as psi, to distinguish it from A's angle.
The preceding sections give

```
e_B=(cos(psi),sin(psi)), f_B=(sin(psi),-cos(psi)),
0<psi<=pi/4-eta,
E=Q_B+e_B,
B=Q_B+[0,1]e_B+[0,1]f_B.
```

Only E has positive height. The positive-height portion of B's boundary
lies on Q_B--E and E--W. All its inward support normals have strictly
negative vertical component. Its maximal height is
`sin(psi)-h-sqrt(2)s<1/sqrt(2)`.

In contrast, `(Q_A)_y>=sqrt(3)/2`. Thus A must extend downward from
Q_A in order to touch B. If Q_A is a vertex, its inward-support
condition gives edges

```
e=(cos(phi),-sin(phi)), f=(sin(phi),cos(phi)),
0<phi<=pi/2-theta.
```

If Q_A is in a side, its frame has `phi=pi/2-theta`. Both cases can be
written in the unified form

```
A=Q_A+[a,b]e+[0,1]f,
a<=0<=b, b-a=1, 0<b<=1.
```

For vertex support, a=0,b=1. For side support the interval [a,b]
records the position of Q_A on its support side.

Containment forces the additional lower frame bound

```
phi>pi/4-theta.                                         (3)
```

It is immediate for side support. For vertex support, suppose instead
`phi<=pi/4-theta` and put `beta=pi/4-phi`, so
`theta<=beta<=pi/4`. The opposite vertex of A is

```
Q_A+e+f=(-L,1/2)+sqrt(2)n_theta+sqrt(2)n_beta,
```

where n_t=(cos(t),sin(t)). Write Q_A=(x_A,y_A). Here
`0<x_A<1/2` and `y_A>=sqrt(3)/2>x_A`. Its squared norm increases with
beta on this interval, since its derivative is
`2sqrt(2)(-x_A sin(beta)+y_A cos(beta))>0`.
At beta=theta its squared norm exceeds R^2 by

```
7-2L-4sqrt(2)L cos(theta)+2sqrt(2)sin(theta).
```

This expression decreases with L and increases with theta. Since L<1
and theta>pi/12, it is greater than its value `2-sqrt(3)>0` at
L=1,theta=pi/12. This contradicts containment and proves (3).

## 6. The contact cannot be on A's support side through Q_A

Suppose the positive A--B contact T lies on that side, so
`T=Q_A+t e` with a<=t<=b. Its height is less than 1/sqrt(2), whereas
Q_A has height at least sqrt(3)/2, so `0<t<=1`.
Because theta>eta, `(Q_A-Q_B)_x=sqrt(2)(p-r)<0`.

If T is on Q_B--E, write `T=Q_B+u e_B`, with 0<=u<=1.
The horizontal coordinate gives
`u cos(psi)<=t cos(phi)`. The vertical coordinate consequently gives

```
D_y=u sin(psi)+t sin(phi)
   <=t[sin(phi)+cos(phi)tan(psi)]
   <=sec(psi)<=sqrt(2).
```

If T is on E--W, write `T=Q_B+e_B+u f_B`. Its horizontal coordinate
gives `t cos(phi)>=cos(psi)+u sin(psi)>=cos(psi)`, hence
`phi<=psi`. Its vertical coordinate gives

```
D_y=sin(psi)-u cos(psi)+t sin(phi)
   <=2sin(psi)<=sqrt(2).
```

Both conclusions contradict (2). This excludes the whole side through
Q_A, including the lower vertex `Q_A+b e`.

## 7. The remaining contact forces make E the separating vertex

The force on B at a positive-height contact has negative vertical
component, so the equal and opposite force on A has positive vertical
component. A's vertices with e-coordinate a have height at least
`(Q_A)_y` and cannot contact B. The preceding section excludes the side
with f-coordinate zero and its remaining vertex. The relative interiors
of the sides with e-coordinate a or f-coordinate one have inward normals
e or -f, both with negative vertical component, so cannot carry this
force.

Consequently the contact is on A's side with e-coordinate b, including
its vertex with f-coordinate one. On the relative interior the inward
normal is -e. At that vertex the inward cone is generated by -e and -f;
its directions with positive vertical component have angles between
`pi-phi` and pi. The force on A, being opposite a positive-height inward
normal of B, has direction between psi and `psi+pi/2`. Therefore

```
phi+psi>=pi/2.                                         (4)
```

At equality the relevant endpoint directions are retained.
Because both phi and psi lie between zero and pi/2, (4) implies

```
e dot e_B=cos(phi+psi)<=0,
e dot f_B=sin(phi+psi)>0.
```

Thus E=Q_B+e_B minimizes the e-projection over all of B. The maximum
e-projection over A is `e dot Q_A+b<=e dot Q_A+1`.
It suffices to prove

```
F:=e dot(E-Q_A)-1
  =sin(phi)D_y+sqrt(2)cos(phi)(r-p)+cos(phi+psi)-1>0.     (5)
```

That would strictly separate the entire two squares, contradicting
T's existence.

## 8. Strict positivity of the separating gap

For fixed phi, the expression (5) decreases with psi, because
`0<phi+psi<pi`. Substituting its largest permitted value
`psi=pi/4-eta` gives the lower bound

```
F >= M sin(phi)+N cos(phi)-1,
M=d+sqrt(2)q+(3s-r)/sqrt(2),
N=(3r+s-2p)/sqrt(2).
```

Both M and N are positive. Indeed, (1) and delta<pi/4 imply
`d>1/sqrt(2)`, so `M>d-r/sqrt(2)>0`; and eta<pi/12 implies
`3r>2>=2p`, so N>0. The right side is therefore concave as a function
of phi on `[pi/4-theta,pi/2-theta]`. By (3) it suffices to prove
positivity at the two endpoints. Direct expansion gives

```
F_0=d(p-q)/sqrt(2)+cos(delta)+2sin(delta)-2,
F_1=dp+[3sin(delta)-cos(delta)]/sqrt(2)-1.
```

For the first, use (1):

```
F_0 >= 2[p cos(delta)/(p+q)+sin(delta)-1].
```

The bracket increases with delta on `[theta,pi/4]`, because its
derivative is `cos(delta)-p sin(delta)/(p+q)>0`. At delta=theta it is

```
(1-p)(1-q)/(p+q)>0.
```

Hence F_0>0.

For the second, (1) gives

```
F_1 >= [v cos(delta)+3sin(delta)]/sqrt(2)-1,
v=(p-q)/(p+q)=tan(pi/4-theta).
```

The bracket increases with delta on `[0,pi/4]` since 0<v<1.
Also `delta>=theta` and `delta>=pi/4-theta`, the latter following
from `2theta+eta>=pi/4`.

If theta<=pi/8, substitute `delta=pi/4-theta` to obtain the lower
bound `2sqrt(2)(p-q)`. Here

```
p-q>=cos(pi/8)-sin(pi/8)>1/2,
```

because the square of the latter difference is
`1-sqrt(2)/2>1/4`. Thus the bracket is greater than sqrt(2).

If theta>=pi/8, substitute delta=theta. The bracket becomes

```
(p+q)+2q^2/(p+q).
```

This increases with theta on `[pi/8,pi/4]`: p+q and q increase,
and `q/(p+q)` has positive derivative `1/(p+q)^2`. At theta=pi/8
its value is again `2sqrt(2)[cos(pi/8)-sin(pi/8)]>sqrt(2)`.
Thus F_1>0 in both cases.

Concavity now proves F>0, completing the strict separation and the
contradiction. This excludes the final radial-side D-D branch.
