# Two compact parameter modes for every loaded-to-loaded diagonal core

**Status:** complete necessary geometric classification after generic
normal selection and the universal radial-D capacity exclusion. This
is a shared reduction, not a further whole-family exclusion. The master
ledger remains 277/336 closed, 59 open.

## 1. The shared circle-feature class is now unique/unique

Take any unloaded degree-two D transmitter with two loaded neighbors.
Endpoint degrees and the remaining graph are unrestricted. Generic
normal selection puts its contacts in the relative interiors of the
neighbor sides, so their frames are parallel. The
[radial-D three-body capacity corollary](RADIAL_DIAGONAL_THREE_BODY_CAPACITY.md)
excludes every geometric radial endpoint.

After rotations and reflections, write

```text
K=2+sqrt(2),       Q=R^2,
u+v=K,            u^2+H_A^2=v^2+H_B^2=Q,
H_A>=H_B>1/2.
```

A reflection and endpoint exchange allow H_A>=H_B. A further vertical
reflection makes A lower-loaded. Thus there are exactly two geometric
sign modes: B lower-loaded too, or B upper-loaded. No outgoing path
direction, circle coefficient, or contact ownership on a third body is
assumed.

Put d=H_A-H_B and T=H_A+H_B. Equal endpoint radii give
K*(v-u)=d*T and therefore

```text
u=K/2-d*T/(2*K),       v=K/2+d*T/(2*K),
H_A=(T+d)/2,          H_B=(T-d)/2.
```

Substitution into either circle equation gives

```text
4*K^2*Q=(K^2+d^2)*(K^2+T^2),
T=sqrt(K^2*(4*Q-K^2-d^2)/(K^2+d^2)).
```

T is the positive root. Its radicand is positive on the containing
Q,d box below; actual points retain H_B>1/2.

## 2. The two height modes

The complete physical squares and D center are

| Mode | A | B | Strict D-height interval |
| --- | --- | --- | --- |
| Same side | [-u,1-u] x [-H_A,1-H_A] | [v-1,v] x [-H_B,1-H_B] | -H_B<h<1-H_A |
| Opposite sides | [-u,1-u] x [-H_A,1-H_A] | [v-1,v] x [H_B-1,H_B] | H_B-1<h<1-H_A |

In both modes D has center ((v-u)/2,h), axes
(1,1)/sqrt(2),(-1,1)/sqrt(2), and touches the two facing vertical sides.

For the same-side mode, nonempty strict height interval is exactly d<1.
For the opposite-side mode it is T<2. Since H_B>1/2, the latter also
implies d=T-2H_B<T-1<1. Consequently both modes lie in the same fixed box

```text
6241/1600 <= Q <= 9/2,       0 <= d <= 1,       0 <= tau <= 1.
```

Actual strict cores use 0<tau<1, H_B>1/2 and the corresponding strict
height condition. Define h by

```text
same side:       h=-H_B+tau*(1-d),
opposite sides:  h=H_B-1+tau*(2-T).
```

This covers every D height without listing contact positions one by one.
The only remaining continuous parameters of these three physical squares
are Q,d,tau in these two sign modes.

## 3. Capacity inference and its current limitation

Every additional center z obeys

```text
|z| <= sqrt(Q-1/4)-1/2.
```

The three known square orientations permit the same uniform
physical-square distance exclusions as in the radial-D proof. A cover
by at most six regions of diameter below one would prove total capacity
at most nine. More generally, a finite weighted cover by regions of
diameter below one, with nonnegative weights summing to less than seven
and total weight at least one at every allowed center, would give the
same integer capacity bound: sum the pointwise inequality over added
centers, then use capacity one in each region.

No complete such cover is provided for either entire three-parameter mode.
Exploratory six-disk clustering at Q=9/2 does not attain radius below 1/2
uniformly even at individual samples. A finite-grid fractional disk-cover
experiment also did not supply total weight below seven. These are
ordinary floating numerical probes, not lower bounds on optimal covers,
counterexamples to the capacity theorem, or packing existence claims.
Neither their unresolved cells nor their candidate region family can
be deleted from a proof.

The completed radial-D table has one fewer continuous parameter because
one endpoint's two circle vertices impose R^2=u^2+1/4. Its success must
not be transferred to these larger unique/unique modes without a new
uniform certificate. A proof may also use further force/torque equations,
additional loaded bodies, or the finite cycle word to narrow these boxes.
