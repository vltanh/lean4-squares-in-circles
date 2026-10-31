# Two side transmitters are impossible when the central loaded square is radial-side

Consider the whole positive component `A-U-C-V-B-A`, with precisely
`A,B,C` loaded and U,V unloaded degree-two transmitters, in the window
`79/40<=R<=3/sqrt(2)`. Suppose C has two vertices on the containing
circle. Then U and V cannot both be side transmitters.

This treats a central-square case outside the unique-circle-vertex
normal form in
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).
It does not exclude configurations with a diagonal transmitter.

Rotate the packing so that

```text
C=[L,L+1] x [-1/2,1/2],
L=sqrt(R^2-1/4)-1,
9/10<L<17/16.
```

The inequalities follow from the stated radius window. C's two circle
vertices are its right corners. Their positive load weights need not be
equal, and the proof does not assume that they are.

## 1. Both transmission contacts lie on the left side of C

A point on the containing circle cannot belong to two squares with
disjoint interiors; the tangent-cone proof is given in Section 1 of
[VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).
Thus neither right corner of C can be a transmission contact.

At a contact in a side's relative interior, the transmission direction
is its outward normal. A contact in the top side would put the far
endpoint contact at height at least `3/2`. The square at that endpoint
is supported from below there and has vertical width at least one,
so it would have a point of height at least `5/2>R`. The bottom side
is excluded by reflection. A contact in the right side similarly puts
an endpoint-square point at horizontal coordinate at least `L+3>R`.

Consequently both contacts lie on C's left side, including its corners.
At an interior point `(L,h)` the outgoing direction is `(-1,0)`. At
the upper-left corner it has the form `(-p,q)` with `p,q>=0` and
`p^2+q^2=1`; the lower-left case is its vertical reflection.

## 2. A loaded endpoint of an upper side transmission stays above zero

Assume the transmitter has width one. First take its contact on C to
be the upper-left corner, with outgoing direction `(-p,q)`. Reflect
the horizontal coordinate for this calculation. Its far endpoint is
then

```text
Q=(p-L,1/2+q),
```

and the endpoint square K has inward supporting normal `(p,q)` at Q.
We prove that if K meets `y<=0`, all its vertices have norm less than R.

Suppose first that Q is a vertex of K. To reach `y<=0`, at least one
incident edge must point downward. The support condition makes that
edge point right; its orthogonal companion must point upward and right.
Thus the two unit edge directions have the forms

```text
(cos(phi),-sin(phi)), (sin(phi),cos(phi)),
0<=phi<=pi/2,
1/2+q<=sin(phi).
```

Write `x_0=p-L`, `y_0=1/2+q`. Then
`-17/16<x_0<1/10` and `0<y_0<=sin(phi)<=1`.
For Q and the two adjacent vertices, the horizontal absolute coordinates
are less than `11/10` and the vertical absolute coordinates at most
`sqrt(2)`: for the upper adjacent vertex use
`y_0+cos(phi)<=sin(phi)+cos(phi)<=sqrt(2)`.
Their squared norms are therefore less than `321/100`.
At the opposite vertex the horizontal absolute coordinate is less than
`1/10+sqrt(2)` and the vertical absolute coordinate at most one, since
`y_0+cos(phi)-sin(phi)<=cos(phi)<=1` and is at least `-1`.
Its squared norm is less than

```text
(1/10+sqrt(2))^2+1 < 331/100 < (79/40)^2.
```

Hence no vertex of K is on the containing circle in this case.

If Q lies in a side, the supporting normal fixes K's frame. Write

```text
K=Q+[0,1](p,q)+[-u,1-u](-q,p),       0<=u<=1.
```

Meeting `y<=0` implies `1/2+q<=up<=p`, and therefore
`p-q>=1/2`. Every point of K has horizontal coordinate between

```text
p-L-q >= 1/2-L > -9/16
```

and

```text
2p+q-L <= sqrt(5)-L < 27/20.
```

Its vertical coordinate lies between `-1` and `p+q<=sqrt(2)`:
the upper bound follows from
`1/2+q+q+(1-u)p<=p+q`.
Thus every vertex has squared norm less than

```text
(27/20)^2+2 = 1529/400 < (79/40)^2.
```

This proves the circle-clearance assertion for an upper-corner contact.
In particular a loaded endpoint must lie wholly in `y>0`.

For a contact `(L,h)` in the left side with `0<h<=1/2`, the normal
is horizontal and the endpoint becomes `Q=(1-L,h)` after reflection.
The same vertex calculation applies verbatim with `y_0=h`: reaching
zero gives `h<=sin(phi)`, and `-1/16<1-L<1/10` gives stronger horizontal
bounds. In the side-supported case K is axis-parallel; its coordinates
are bounded by `|x|<11/10` and `|y|<=1` whenever it meets zero.
Again a loaded endpoint must be wholly above zero. At `h=0`, K already
meets zero, so it cannot be loaded at all.

Vertical reflection gives the corresponding assertion for contacts on
the lower half of C's left side: their loaded endpoints must be wholly
below zero.

## 3. Torque balance forces the endpoints to opposite sides

The outgoing force at `(L,h)` has strictly positive torque about zero
when `h>0`: in the side interior it is horizontal and its torque is a
positive multiple of h; at the upper corner its torque is a positive
multiple of `Lq+p/2>0`. The corresponding torque is strictly negative
when `h<0`, and is zero precisely at the left side's midpoint.

Circle forces have zero torque about the origin. C's two contact torques
must therefore sum to zero. A midpoint contact would, by Section 2,
already make its endpoint circle-clear. Thus one contact lies above zero
and the other below zero. If both transmitters were side type, Section 2
would place the two loaded endpoint squares wholly in the two opposite
open half-planes. They could not touch, contradicting the positive edge
A--B.

This excludes two side transmitters for a radial-side central square.
