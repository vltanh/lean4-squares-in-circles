# Exact equations for one side/vertex ring pattern

This is a conditional scalar reduction for a seven-loaded physical ring.
It does not classify the possible contact patterns, and it does not prove
that every solution of the equations below is uniform. The common-offset
family is already excluded in
[REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md).

## 1. The additional contact-pattern assumptions

Let `(u_i,v_i)` be positively oriented orthonormal square frames, with
angles `theta_i`. Assume each body's unique loaded circle vertex is

```text
w_i = c_i + (u_i-v_i)/2,       |w_i|=R.
```

Its incoming contact is the lower-left corner `w_i-u_i`, and its outgoing
contact is in the relative interior of the upper side:

```text
p_(i-1)=w_i-u_i,
p_i=w_i-lambda_i u_i+v_i,      0<lambda_i<1.
```

Thus the original outgoing pair force is `f_i=mu_i v_i`, with `mu_i>0`.
These are genuine additional assumptions; in particular they exclude
corner/corner contacts and changes of contact ownership.

By [SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md), the force
polygon is strictly convex and contains the origin in its interior.
Its consecutive vertex rays therefore turn counterclockwise by angles
strictly between zero and `pi`, with total turn `2pi`. Since each `f_i`
is a positive multiple of `v_i`, choose the frame-angle lifts so that

```text
0 < delta_i = theta_i-theta_(i-1) < pi,
sum_i delta_i = 2pi.
```

Equation (3) below will strengthen the upper bound to `pi/2`. Thus
monotone acute frame turns are consequences of this ownership pattern
and physical stress; they are not extra uniformity assumptions.

Put

```text
L_i = sqrt(mu_(i-1)^2+mu_i^2
           -2 mu_(i-1) mu_i cos(delta_i)).
```

Force balance and the unique radial circle load imply

```text
w_i = (R/L_i) [mu_(i-1) v_(i-1)-mu_i v_i].                (1)
```

In the current frame this reads

```text
w_i dot u_i = R mu_(i-1) sin(delta_i)/L_i,
w_i dot v_i = R [mu_(i-1) cos(delta_i)-mu_i]/L_i.          (2)
```

The assumed farthest-vertex signs also impose
`w_i dot u_i>1/2` and `w_i dot v_i<-1/2`. They must not be dropped when
interpreting the scalar equations as possible physical packings.

## 2. Torque and contact matching

Let `tau>0` be the common torque from
[SEVEN_RING_FORCE_CIRCULATION.md](SEVEN_RING_FORCE_CIRCULATION.md).
Outgoing and incoming torque, computed at the two contact points above,
give

```text
tau = mu_i [w_i dot u_i-lambda_i]
    = mu_(i-1) [R mu_i sin(delta_i)/L_i-cos(delta_i)].
```

Consequently

```text
lambda_i mu_i = mu_(i-1) cos(delta_i),                    (3)

tau = R mu_(i-1) mu_i sin(delta_i)/L_i
       -mu_(i-1) cos(delta_i).                            (4)
```

Because both `lambda_i` and the contact magnitudes are positive, (3)
gives `cos(delta_i)>0`. The preceding angle lifts consequently satisfy
`0<delta_i<pi/2`.

The shared-point equation is

```text
w_(i+1)-u_(i+1) = w_i-lambda_i u_i+v_i.                  (5)
```

Its `u_i` component follows already from (3)--(4). Indeed, the left-hand
circle vertex has projection

```text
w_(i+1) dot u_i
 = R mu_(i+1) sin(delta_(i+1))/L_(i+1)
 = tau/mu_i + cos(delta_(i+1)),
```

while `(w_i-lambda_i u_i) dot u_i=tau/mu_i`.
Its remaining component is the exact scalar relation

```text
R [ (mu_i-mu_(i-1) cos(delta_i))/L_i
    +(mu_i-mu_(i+1) cos(delta_(i+1)))/L_(i+1) ]
 = 1+sin(delta_(i+1)).                                   (6)
```

Thus (4), (6), the total-turn condition, and the physical inequalities
above are necessary for this contact pattern. Equations (3) and (1)
reconstruct the side parameters and the loaded vertices. Nonneighbor
separation and full circle containment still have to be checked in any
attempt to construct a packing from scalar data.

Equivalently, (4) and (6) are the stationarity equations of

```text
F(mu,delta) = R sum_i L_i
             -sum_i mu_i [1+sin(delta_(i+1))],
```

where `sum_i delta_i=2pi`: the `mu_i` derivatives vanish, and the
`delta_i` derivatives all equal `tau`. This equivalence alone supplies
no convexity or uniqueness assertion.

## 3. Either one of two uniformity assumptions forces the other

First suppose all `mu_i` equal a number `mu`. Equation (4) becomes

```text
tau/mu = R cos(delta_i/2)-cos(delta_i).                    (7)
```

The right side is strictly increasing on `(0,pi/2)`. Its derivative is

```text
sin(delta_i/2) [2 cos(delta_i/2)-R/2] > 0,
```

because `R<=3/sqrt(2)` and `2cos(delta_i/2)>sqrt(2)>3/(2sqrt(2))`.
Hence all `delta_i=2pi/7`.

Conversely, suppose all `delta_i` equal `delta=2pi/7`. For positive
numbers a,b define

```text
H(b,a)=(b-a cos(delta))/sqrt(a^2+b^2-2ab cos(delta)).
```

As a function of `x=b/a`, its derivative is

```text
sin^2(delta)/(1+x^2-2x cos(delta))^(3/2)>0.
```

Thus `H(b,a)>=sin(delta/2)` when `b>=a`, with equality only when `b=a`;
the reverse inequality holds when `b<=a`.

Apply (6) at a largest `mu_i`. Both summands are at least
`sin(delta/2)`, giving

```text
R <= [1+sin(delta)]/[2sin(delta/2)].
```

At a smallest `mu_i`, both inequalities reverse and give the opposite
bound. Equality follows. At a largest `mu_i`, both neighboring weights
must therefore equal it. Propagating around the cycle shows that all
weights are equal.

In either case the common radius is

```text
R = cos(pi/7)+1/[2sin(pi/7)].                              (8)
```

Equation (2) now gives the same own-frame center coordinates on every
body:

```text
c_i dot u_i = R cos(pi/7)-1/2,
c_i dot v_i = 1/2-R sin(pi/7).
```

The frame offsets from the center rays are consequently all equal. The
uniform-ring theorem excludes its completion by three further unit
squares.

Therefore a still-possible ring satisfying this fixed contact pattern
must vary both its positive contact magnitudes and its frame gaps.
Proving that such simultaneous variation is impossible, or excluding its
three-square completion directly, remains open in this note.
