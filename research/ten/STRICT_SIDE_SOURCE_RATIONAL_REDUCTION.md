# Five circle-feature rows and a two-angle reduction for a strict side source

**Status:** complete necessary-form argument checked in this session; no
independent agent review or Lean verification is claimed. This is a uniform
reduction inside LSLSLD. The subsequent [uniform side-source closure](STRICT_SIDE_SOURCE_CAPACITY_CLOSURE.md) now completes the E_A/E_B rows; the subsequent [V_V source theorem](STRICT_VERTEX_SOURCE_CAPACITY_CLOSURE.md) closes those rows too. Radial D endpoints remain open.

Use [ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md)
after the [complete vertical-endpoint exclusion](RADIAL_VERTICAL_SOURCE_EXCLUSION.md).
Both D endpoints A,B have unique circle vertices and strict inner-corner
S supports. In its notation alpha=beta=0, and

```text
n_A=(p,q),       n_B=(-r,s),
0<p<q,          0<r<s,       p^2+q^2=r^2+s^2=1.
```

The labels q and s here are unit-vector components, not squared radii.
Let e point from Q_A toward Q_B on C's common edge, and let m be its
inward unit normal. Both n_A dot m and n_B dot m are positive. The positive
circle resultant on C is

```text
g=sigma_A*n_A+sigma_B*n_B,       sigma_A,sigma_B>0.
```

## 1. The exact circle-feature table has five rows

The resultant has g dot m>0. If C has a unique circle vertex, it must be
one of its two upper vertices in the m direction. Indeed a unique
farthest vertex in square-frame coordinates has the same coordinate
signs as its center, so a positive circle resultant component along m
selects the positive m side.

In row E_A, n_A=m and n_B dot e<0. Hence g dot e<0, selecting C's unique
upper-left vertex. In row E_B, n_B=m and n_A dot e>0, selecting its unique
upper-right vertex.

Neither E_A nor E_B permits radial-side C. Each has a side-normal S path
from C to a loaded endpoint. Section 1 of
[ONE_DIAGONAL_VERTICAL_SOURCE_TORQUE_EXCLUSIONS.md](ONE_DIAGONAL_VERTICAL_SOURCE_TORQUE_EXCLUSIONS.md)
excludes every such path from a radial-side loaded square, regardless of
the endpoint's other forces. The argument there does not require a
vertical S direction at a D endpoint.

In row V_V, Q_A,Q_B are the endpoints of the common inner edge. Two circle
vertices on either lateral side would include one of these actual contact
points; two on the bottom side would include both. A packed neighbor
cannot share a point of the containing circle. Thus the only two-circle
possibility is C's upper side.

| Source support row | Geometric circle feature at C |
| --- | --- |
| E_A | Unique upper-left vertex |
| E_B | Unique upper-right vertex |
| V_V | Unique upper-left vertex |
| V_V | Unique upper-right vertex |
| V_V | Both upper vertices; arbitrary nonnegative circle-load split |

This covers every realization in the both-unique-D-endpoint branch. It
retains both transmitter slides. The radial-D-endpoint branch remains
separate.

## 2. A strict E_A source is determined by two S-direction angles

Consider the first row. Put

```text
K=2+sqrt(2),
d=H_A-H_B,       T=H_A+H_B,
X=-1-r-q+p,     Y=1+s+p+q.
```

The D endpoint coordinates are

```text
A=[-u,1-u] x [-H_A,1-H_A],
B=[v-1,v] x [-H_B,1-H_B],       u+v=K.
```

The source contacts differ by
`Delta=(sqrt(2)-p-r,d+s-q)`. The E_A equation n_A dot Delta=0 therefore gives

```text
d=(1-sqrt(2)*p-q*s+p*r)/q.                         (1)
```

Equality of A's and B's circle radii gives d*T=K*(v-u), so

```text
u=K/2-d*T/(2K),       v=K/2+d*T/(2K),
H_A=(T+d)/2,         H_B=(T-d)/2.                  (2)
```

In this source row e=(q,-p) and m=n_A. Its upper-left circle vertex is

```text
w_C=Q_B-e+n_A=(v+X,-H_B+Y).
```

The circle vertex of B is w_B=(v,-H_B). Expanding their equal norms gives
`2v*X-2H_B*Y+X^2+Y^2=0`. With (2), this solves T explicitly:

```text
T=(K*X+d*Y+X^2+Y^2)/(Y-d*X/K).                    (3)
```

Its denominator is uniformly positive for every actual realization.
We have |d|<R-1/2<13/8, |X|<11/4, Y>5/2 and K>17/5. Therefore

```text
Y-d*X/K > 5/2-(13/8)*(11/4)/(17/5)=645/544>0.     (4)
```

Here X<-1 follows from p<q, while Y>5/2 follows from s>1/sqrt(2)>1/2
and p+q>1. No division by a potentially zero geometric factor was used.
The squared containing radius is now

```text
R^2=u^2+H_A^2=(K^2+d^2)*(K^2+T^2)/(4K^2).          (5)
```

Thus both loaded endpoints and the radius are determined by p,q,r,s.

## 3. Two residual equations and explicit core centers

Define

```text
D_A=u*q-H_A*p>0,       D_B=v*s-H_B*r>0,
N_A=H_A*((u-1)*q-(H_A-1)*p),
N_B=H_B*((v-1)*s-(H_B-1)*r).
```

The positive D magnitude is normalized to one. The two endpoint torque
identities give the same D force height h:

```text
-h=N_A/D_A=N_B/D_B.
```

In particular the first remaining scalar equation is

```text
E:=N_A*D_B-N_B*D_A=0.                              (6)
```

The S force magnitudes are sigma_A=H_A/D_A and sigma_B=H_B/D_B.
Multiply the resultant g by the positive D_A*D_B and define

```text
g'=(H_A*D_B*p-H_B*D_A*r,
    H_A*D_B*q+H_B*D_A*s).
```

The unique circle load at w_C consequently requires

```text
G:=w_C cross g'=0,       w_C dot g'>0.              (7)
```

All four centers needed for a completion argument are explicit:

```text
c_A=(1/2-u,1/2-H_A),
c_B=(v-1/2,1/2-H_B),
c_D=((v-u)/2,-N_A/D_A),
c_C=Q_B-e/2+n_A/2,
Q_B=(v-1-r,1-H_B+s).
```

The two S transmitters retain their entire intervals:

```text
c_SA=(1-u,1-H_A)+n_A/2+t_A*(q,-p),
c_SB=(v-1,1-H_B)+n_B/2+t_B*(s,r),
-1/2<=t_A,t_B<=1/2.
```

Finally put x=p/(1+q) and y=r/(1+s). Then

```text
p=2x/(1+x^2),       q=(1-x^2)/(1+x^2),
r=2y/(1+y^2),       s=(1-y^2)/(1+y^2),
0<x,y<sqrt(2)-1.
```

Every coordinate, R^2, E and G is a rational function of just x,y over
Q(sqrt(2)). Reflection swaps the two endpoints and gives the same reduction
for E_B. This avoids the square roots and the extra force-height variable
in the previous three-dimensional interval exploration.

## 4. Subsequent completion and remaining proof obligation

Equations (6)--(7) are necessary, not sufficient. Every actual core also
satisfies the radius window, strict D contact heights, positive force
magnitudes, `0<(sqrt(2)-p-r)/q<=1`, source containment, all pairwise
nonoverlap conditions, and both complete S slide constraints. Any use of
polynomial numerators must retain the nonzero denominator conditions.

The [subsequent E_A/E_B closure](STRICT_SIDE_SOURCE_CAPACITY_CLOSURE.md)
provides a complete 1,133-leaf necessary-parameter enclosure, excludes both
retained degenerate boundary roots by injectivity, and proves total capacity
at most nine uniformly over the retained interior rectangle with a 161-cell
four-center cover. Both transmitter slides remain unrestricted. The subsequent [V_V source closure](STRICT_VERTEX_SOURCE_CAPACITY_CLOSURE.md)
completes the remaining source features. Only radial D endpoints remain
open in LSLSLD.
