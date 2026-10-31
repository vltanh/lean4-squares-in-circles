# The uniform side/vertex ring is locally isolated

This is a conditional hand theorem for the contact pattern in
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md). It excludes
sufficiently small nonuniform perturbations that still carry a physical
positive stress with that same pattern. It does not classify other
contact patterns or exclude nonuniform solutions far from the uniform one.

Normalize the positive contact magnitudes by

```text
sum_i mu_i = 7.
```

Put `h=pi/7`, `s=sin(h)`, `c=cos(h)`, and `C=cos(2h)`. The uniform
solution of the scalar equations is

```text
mu_i=1,   delta_i=2h,
R_0=c+1/(2s),
tau_0=R_0 c-C.
```

**Theorem.** This solution is isolated among the solutions of the torque
equations (4), contact equations (6), total-turn condition, and the above
normalization. Consequently there is a neighborhood of this uniform ring
containing no nonuniform physical stressed ring with the stated contact
ownership. The common-offset theorem already excludes the uniform ring's
completion by three further unit squares.

The neighborhood assertion concerns the normalized scalar data
`(mu_i,delta_i,R,tau)`; no numerical neighborhood size is claimed.

## 1. Linearizing the complete system

For positive `a,b` and `0<d<pi/2`, write

```text
L(a,b,d)=sqrt(a^2+b^2-2ab cos(d)),
T(a,b,d,R)=R ab sin(d)/L(a,b,d)-a cos(d),
H(b,a,d)=(b-a cos(d))/L(a,b,d).
```

The equations to be linearized are exactly

```text
T(mu_(i-1),mu_i,delta_i,R)=tau,
R [H(mu_i,mu_(i-1),delta_i)
   +H(mu_i,mu_(i+1),delta_(i+1))]
   =1+sin(delta_(i+1)),
sum_i delta_i=2pi,   sum_i mu_i=7.                 (1)
```

These are sixteen smooth real equations in sixteen real variables.
All denominators are positive near the uniform solution, since there
`L=2s>0`.

Let a vector in the kernel of their derivative have components

```text
x_i = d mu_i,   y_i = d delta_i,
rho = d R,     sigma = d tau.
```

Define the constants

```text
B=R_0 c/2,   A=B-C,
D=2sc-R_0 s/2,
E=R_0 c^2/(2s).
```

Direct differentiation of (1) gives

```text
A x_(i-1)+B x_i+D y_i+c rho=sigma,                 (2)
E(2x_i-x_(i-1)-x_(i+1))
  +B y_i+A y_(i+1)+2s rho=0,                      (3)
sum_i x_i=0,   sum_i y_i=0.                       (4)
```

For example, at `a=b=1,d=2h`, the derivatives of `T` with respect
to `a,b,d,R` are respectively `A,B,D,c`. The derivatives of
`H(b,a,d)` with respect to `b,a,d` are respectively
`c^2/(2s),-c^2/(2s),c/2`. These identities also check every coefficient
in (2)--(3).

Sum (3) over the seven indices. Equation (4) leaves `14s rho=0`,
so `rho=0`. Summing (2) then gives `sigma=0`.

## 2. Reduction to a cyclic scalar matrix

We have `D>0`. Indeed `R_0=c+1/(2s)` gives

```text
D=(3/2)sc-1/4.
```

The elementary bound `3/5<C<5/8`, proved in
[REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md), gives
`sin(2h)>3/4`, hence `sc>3/8` and `D>5/16`.

Thus (2) determines

```text
y_i=-(A x_(i-1)+B x_i)/D.
```

Substitution in (3), followed by multiplication by `D`, gives

```text
[2DE-A^2-B^2] x_i
 -(DE+AB)(x_(i-1)+x_(i+1))=0.                     (5)
```

The constants simplify exactly:

```text
DE+AB
 = R_0 c^3-R_0 c C/2
 = R_0 c/2 = B,
A+B=R_0 c-C=tau_0.
```

The cyclic shift matrix has the seven usual Fourier modes. On the mode
with index `k`, equation (5) has eigenvalue

```text
Lambda_k=4B sin^2(k pi/7)-(A+B)^2
        =2R_0 c sin^2(kh)-tau_0^2.                (6)
```

Only `k=1,...,6` are needed because (4) removes the constant mode.
Equivalently one may use the real sine and cosine vectors; the paired
indices `k` and `7-k` have the same eigenvalue.

## 3. None of the six eigenvalues vanishes

Put `z=cot(h)` and `v=s^2=1/(1+z^2)`. The same bounds on `C` imply

```text
2<z<21/10,   0<v<1/5,
R_0 c=1-v+z/2>9/5,
tau_0=v+z/2<5/4.                                 (7)
```

For the first pair of modes, exact simplification gives

```text
Lambda_1=Lambda_6
 =2(1-v+z/2)v-(v+z/2)^2
 =2v-3v^2-z^2/4
 <-3/5<0.                                        (8)
```

For the other four modes, `sin^2(kh)>=sin^2(2h)` when
`k=2,3,4,5`. Also

```text
sin^2(2h)=1-C^2>39/64.
```

Equations (6)--(7) therefore give

```text
Lambda_k > (18/5)(39/64)-(5/4)^2
         =101/160>0,       k=2,3,4,5.             (9)
```

Every nonconstant Fourier coefficient of `x` is zero by (5),
(8), and (9). The constant coefficient is zero by (4), so `x=0`.
Equation (2) now gives `y=0`; already `rho=sigma=0`. The derivative
of the full normalized system consequently has trivial kernel and is
invertible.

## 4. Local isolation and its limit

For completeness, invertibility gives isolation directly. If distinct
solutions approached the uniform solution, divide their displacement
vectors by their Euclidean lengths. A subsequence of these unit vectors
converges to a unit vector. Differentiability of (1), after dividing the
zero equation differences by those lengths, puts the limiting vector in
the derivative's kernel. Section 3 says that kernel is zero, a
contradiction.

Hence sufficiently nearby normalized solutions are uniform. This
removes the possibility that an unresolved ring of this contact pattern
is an arbitrarily small nonuniform perturbation of the known uniform
solution. It supplies neither a global uniqueness theorem nor a bound
on the distance of every physically possible ring from that solution.
