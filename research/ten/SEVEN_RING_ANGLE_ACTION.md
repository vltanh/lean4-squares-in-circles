# A seven-variable angle action for the side/vertex ring

**Handoff status:** independently reviewed exact reduction. The required
global uniqueness or completion exclusion remains open.

This is an exact reduction of the particular contact pattern in
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md). It removes the
seven force magnitudes from its stationarity equations. It does not prove
global uniqueness of the resulting critical point or reduce every loaded
ring to this contact pattern.

Fix a radius `R` in the stated window. In each body's frame write its
unique loaded circle vertex as

```text
w_i=R(cos(alpha_i) u_i-sin(alpha_i) v_i),
0<alpha_i<pi/2.
```

The farthest-vertex signs require
`R cos(alpha_i)>1/2` and `R sin(alpha_i)>1/2`. As in the preceding note,
the incoming contact is `w_i-u_i`, the outgoing contact is
`w_i-lambda_i u_i+v_i`, and `0<lambda_i<1`.

Put `beta_i=delta_i-alpha_i`. No positivity assumption on `beta_i`
is made. Since `0<delta_i<pi/2`, one has `-pi/2<beta_i<pi/2`.

## 1. One positive branch determines each frame gap

The shared contact equation in the previous frame's `v` direction is

```text
R sin(alpha_(i-1))-1-sin(delta_i)
       +R sin(delta_i-alpha_i)=0.                       (1)
```

Its derivative with respect to `delta_i` is

```text
k_(i-1)=R cos(beta_i)-cos(delta_i)>0.                    (2)
```

Indeed the torque equation gives `k_(i-1)=tau/mu_(i-1)`, and both
the common torque and the contact magnitude are positive.

For fixed consecutive angles `a=alpha_(i-1)` and `b=alpha_i`, put

```text
A=R cos(b)-1,      B=R sin(b)>0,
D=sqrt(A^2+B^2)=sqrt(R^2+1-2R cos(b)),
H=R sin(a)-1.
```

Equation (1) is `H+A sin(delta)-B cos(delta)=0`.
There is at most one root in `(0,pi/2)` at which its derivative is
positive. If `A>=0`, the derivative `A cos(delta)+B sin(delta)` is
positive throughout. If `A<0`, that derivative changes sign exactly
once, from negative to positive; the function decreases and then
increases, and has at most one root on its increasing part.

The positive branch is explicit. Let `omega` be the angle in `(0,pi)`
with `cos(omega)=A/D` and `sin(omega)=B/D`. Then

```text
delta(a,b;R)=omega+asin(-H/D),
k(a,b;R)=sqrt(D^2-H^2).                                (3)
```

Here `asin` is its principal branch in `(-pi/2,pi/2)`. Restrict to
the open domain where `|H|<D` and the displayed `delta` belongs to
`(0,pi/2)`. At a physical solution, (2) guarantees this domain and
the choice of branch, so no root is lost. Conversely (3) solves (1)
with the positive derivative `k`.

For a cyclic list of seven angles in this domain, abbreviate

```text
delta_i=delta(alpha_(i-1),alpha_i;R),
k_(i-1)=k(alpha_(i-1),alpha_i;R),
beta_i=delta_i-alpha_i.
```

## 2. The force equations are precisely criticality of an angle sum

Define

```text
S_R(alpha_0,...,alpha_6)=sum_i delta_i.                  (4)
```

Implicit differentiation of (1) gives

```text
partial_a delta(a,b;R)=-R cos(a)/k,
partial_b delta(a,b;R)= R cos(beta)/k.                  (5)
```

Thus `alpha_i` is a critical coordinate of (4) exactly when

```text
cos(beta_i)/k_(i-1)=cos(alpha_i)/k_i.                   (6)
```

Force balance in the one-chirality pattern gives

```text
mu_i/mu_(i-1)=cos(beta_i)/cos(alpha_i).
```

Together with `k_i=tau/mu_i`, this is precisely (6). Every physical
stressed ring of the stated pattern therefore satisfies

```text
grad S_R=0,             S_R=2pi.                       (7)
```

The second equality is the frame's total-turn condition. The radius is
held fixed when taking the gradient in (7).

There is also a converse at the level of the scalar contact and stress
equations. Suppose (7) holds on the positive branch, with the stated
farthest-vertex inequalities and

```text
0<lambda_i:=cos(delta_i) cos(alpha_i)/cos(beta_i)<1.     (8)
```

Choose any `tau>0` and set `mu_i=tau/k_i`. Equation (6) supplies the
displayed force ratio. Hence

```text
mu_(i-1) v_(i-1)-mu_i v_i
 = [mu_(i-1) sin(delta_i)/cos(alpha_i)]
       [cos(alpha_i)u_i-sin(alpha_i)v_i],
```

a positive multiple of `w_i`. The circle load is positive. Also (2),
(6), and (8) give

```text
k_i=R cos(alpha_i)-lambda_i,
tau=mu_i k_i=mu_(i-1) k_(i-1),
```

which are the outgoing and incoming torque equations.

The two contact points match in both frame coordinates. Their previous
`v` coordinates match by (1); their previous `u` coordinates match
because

```text
w_i dot u_(i-1)-cos(delta_i)=k_(i-1)
 =w_(i-1) dot u_(i-1)-lambda_(i-1).
```

Thus the scalar equations reconstruct the intended circle loads and
neighbor contacts, with all force witnesses kept. Nonneighbor separation
is still an additional physical requirement. This converse does not
claim that every critical point gives an actual packing.

## 3. Explicit derivatives for a remaining uniqueness argument

The reduction has a simple local derivative structure. With `a,b,delta,
beta,k,H` as above, differentiation of (2) gives

```text
partial_b k=R sin(b)/k,
partial_a k=-R cos(a) H/k.
```

For the first identity, use

```text
H cos(beta)+k sin(beta)
 =sin(delta)cos(beta)-cos(delta)sin(beta)
 =sin(b).
```

The mixed derivative of each summand in (4) is consequently

```text
partial_a partial_b delta
   =R^2 cos(a) sin(b)/k^3>0.                           (9)
```

The two pure derivatives, useful for checking any proposed global
convexity or oscillation argument, are

```text
partial_a^2 delta
 =R sin(a)/k-R^2 cos^2(a) H/k^3,

partial_b^2 delta
 =-R sin(beta) cos(delta)/k^2
   -R^2 cos(beta) sin(b)/k^3.                          (10)
```

The Hessian of `S_R` is therefore cyclic tridiagonal. Its adjacent
off-diagonal entries are positive by (9). Equations (9)--(10) alone
do not make that Hessian positive or negative definite; no such global
claim is used here.

At the uniform solution, `alpha_i=beta_i=pi/7`. The separate exact
[local-rigidity theorem](SEVEN_RING_LOCAL_RIGIDITY.md) proves this solution
is isolated after force normalization. The unresolved one-chirality
problem can now be stated using only seven angles: exclude every other
critical point of `S_R` with value `2pi` in the physical domain (8), or
exclude the corresponding three-square completion directly.
