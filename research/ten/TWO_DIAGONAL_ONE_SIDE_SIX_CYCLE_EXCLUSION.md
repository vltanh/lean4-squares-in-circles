# Two diagonal paths and one side path cannot form a three-loaded six-cycle

**Status:** complete hand proof; two full mathematical reviews passed on
2026-10-29, including both radial-side endpoint cases and the strict torque
inequalities.

Select the physical certificate of
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
before classifying its positive graph. Suppose a whole simple-cycle
component has three loaded bodies and three unloaded transmitters, two
of type D and one of type S. Its stable entry is

```text
C20-M06-L03-B02-T03: LSLDLD.
```

Work in `79/40<=R<=3/sqrt(2)`. The lower-radius dependencies are those
of [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

**Theorem.** This signature is impossible in the selected-certificate
lower-bound reduction for a strictly subcritical ten-square packing.

## 1. The diagonal paths fix all three loaded frames

Let C be the loaded body incident to both D paths, whose other loaded
endpoints are A and B. The S path joins A to B. The
[D graph restrictions](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md) make the
two outgoing D directions at C perpendicular. Every D contact is in a
relative side interior of its loaded neighbor. Therefore the square
frames of A,B,C are parallel.

C cannot have two circle vertices. In its radial-side frame, at least
one of two perpendicular side normals points through its top or bottom
side. The corresponding D endpoint contact then has absolute height
`1/2+sqrt(2)`, and its unit inward normal step has absolute height
`3/2+sqrt(2)>R`, a contradiction.

Thus C has a unique circle vertex. Choose its axes so the two D paths
point left and down. Force balance makes its outward circle-load vector
have positive components in both axes. Consequently

```text
Z=(X,Y),       X,Y>1/2,       X^2+Y^2=R^2,
C=[X-1,X] x [Y-1,Y].
```

Put `d=sqrt(2)` and

```text
u=2+d-X,       v=2+d-Y.
```

The parallel endpoint frames then have the form

```text
A=[-u,1-u] x [a,a+1],
B=[b,b+1] x [-v,1-v].                                (1)
```

Here u,v>1 because `X,Y<=R<1+d`. The D contacts on C and on A,B
are relative side-interior points. The two vertical intervals for C,A
therefore overlap in their relative interiors, giving `a>Y-2`.
Similarly `b>X-2`. It follows that

```text
b> X-2 > X-1-d=1-u,
a> Y-2 > Y-1-d=1-v.                                  (2)
```

B lies strictly to the right of A, and A strictly above B.

## 2. The side path joins opposite inner corners

For the parallel rectangles (1)--(2), the unique closest pair consists
of A's lower-right corner and B's upper-left corner. The width-one
transmission formula therefore gives

```text
P_A=(1-u,a),       P_B=(b,1-v),
P_B-P_A=(p,-q),    p,q>0,       p^2+q^2=1.             (3)
```

Let sigma>0 be the S force magnitude. Orient the component from C through
its left D path to A, then through S to B, then through the remaining D
path back to C. Let mu>0 be the left D magnitude and nu>0 the other.
The outward circle-load resultants on A and B are

```text
g_A=(-mu-sigma*p, sigma*q),
g_B=(sigma*p, -nu-sigma*q).                           (4)
```

Thus g_A has positive vertical coordinate, and g_B positive horizontal
coordinate. Since A lies wholly in x<0 and B wholly in y<0, (4) implies
that A's center height and B's center horizontal coordinate are
nonnegative. Write

```text
H_A=sqrt(R^2-u^2)>=1/2,
H_B=sqrt(R^2-v^2)>=1/2.
```

Loading and containment then force

```text
a=H_A-1,       b=H_B-1.                              (5)
```

When H_A>1/2, A has the unique circle vertex `(-u,H_A)`; when
H_A=1/2 it has two circle vertices. The corresponding statements hold
for B with H_B and its positive horizontal coordinate. In particular,
the two-circle boundary cases remain explicit below.

## 3. A radial-side endpoint is impossible

Suppose A has two circle vertices, so H_A=1/2 and

```text
u=sqrt(R^2-1/4),       X=2+d-u,
A=[-u,1-u] x [-1/2,1/2].
```

First suppose `R^2>=17/4`, hence u>=2. Let `L_A=u-1>=1`.
The D path from A to C starts at a relative side-interior point
`(-L_A,h)`, with `|h|<1/2`, and points right. C's horizontal interval
is `[d-L_A,d-L_A+1]`, whose endpoints are positive and whose maximum
is at most d. Its vertical interval has length one and contains h in
its relative interior, so every vertex has vertical absolute coordinate
strictly less than 3/2. Consequently every C vertex has squared norm

```text
<d^2+(3/2)^2=17/4<=R^2,
```

contradicting its positive circle load. Positivity of the first horizontal
endpoint follows from `L_A<17/16<d`, using the radius upper bound.

Now suppose `R^2<17/4`, so u<2 and X>d. Since H_B>=1/2,

```text
v^2=R^2-H_B^2<=R^2-1/4=u^2,
v<=u,
Y=2+d-v>=X>d.
```

Also `Y^2=R^2-X^2<17/4-2=9/4`, so Y<3/2. Equation (3) and (5)
give the two positive S gaps

```text
p=H_B+u-2 < H_B,
q=v-3/2 = 1/2+d-Y < 1/2.
```

Because `v=2+d-Y>1/2+d`,

```text
H_B^2=R^2-v^2
 <17/4-(1/2+d)^2=2-d.
```

Therefore

```text
p^2+q^2 < 2-d+1/4=9/4-sqrt(2)<1,
```

using `sqrt(2)>5/4`. This contradicts the unit S width in (3).

Thus A cannot have two circle vertices. Exchanging the axes and A,B
proves the same assertion for B.

## 4. Unique circle vertices force two opposite strict inequalities

Both endpoints now have unique circle vertices, so for positive alpha,beta

```text
g_A=alpha*(-u,H_A),
g_B=beta*(H_B,-v).
```

Let the D contact on A be `(1-u,y_A)`. It belongs to the relative
interior of A's right side, so `y_A<H_A`. Comparing (4) gives

```text
alpha*H_A=sigma*q,
mu=alpha*u-sigma*p.
```

Origin torque balance at A equates the torque of the incoming D force
to the outgoing S force:

```text
mu*y_A=sigma*[q(u-1)-p(H_A-1)].
```

Subtract `mu*H_A=sigma*(qu-pH_A)` to obtain

```text
mu*(y_A-H_A)=sigma*(p-q).
```

The left side is strictly negative. Hence p<q.

Similarly let the D contact on B be `(x_B,1-v)`, with `x_B<H_B`.
Using `beta*H_B=sigma*p` and `nu=beta*v-sigma*q`, its torque equation
gives

```text
nu*(x_B-H_B)=sigma*(q-p).
```

This left side is also strictly negative, so q<p. The two strict
inequalities contradict each other. Every circle-contact case has been
covered, completing the exclusion of the entire fixed signature.
