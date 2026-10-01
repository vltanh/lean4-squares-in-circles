# Elementary pi bounds used by the replacement notes

This appendix supplies a short human derivation of

```math
\frac{157}{50}<\pi<\frac{377}{120}<\frac{22}{7}.
```

It is included so that the coarse transition proof need not be explained by a
high-precision library enclosure. A formal integrator may reuse accepted
library bounds; this is the independent mathematical explanation.

## 1. A rational-angle identity

Let `a=arctan(1/5)` and `b=arctan(1/239)`. Double-angle identities give

```math
\tan(2a)=\frac5{12},\qquad \tan(4a)=\frac{120}{119}.
```

Consequently

```math
\tan(4a-b)=
\frac{120/119-1/239}{1+(120/119)(1/239)}=1.
```

The integer 239 is not an approximation to an unknown angle: solving this
last rational tangent equation gives it exactly. Since `0<b<a<1/5`,
`0<4a-b<4/5<pi/2`. The elementary inequality pi>2 follows, for example,
from `pi/4=integral_0^1 1/(1+t^2) dt > 1/2`. Thus there is no ambiguity
modulo pi, and

```math
\pi=16\arctan(1/5)-4\arctan(1/239).
```

## 2. Two integral remainder estimates

For positive x, integrate the identities obtained by division of
`1/(1+t^2)` to obtain

```math
x-\frac{x^3}{3}<\arctan x
 <x-\frac{x^3}{3}+\frac{x^5}{5},\qquad \arctan x<x.
```

Each error has a displayed sign: the first omitted integral is respectively
`integral t^4/(1+t^2)` or `integral t^6/(1+t^2)`.
Therefore

```math
16\left(\frac15-\frac{1}{3\cdot5^3}\right)-\frac4{239}
 <\pi
 <16\left(\frac15-\frac{1}{3\cdot5^3}+\frac{1}{5\cdot5^5}\right)
  -4\left(\frac1{239}-\frac{1}{3\cdot239^3}\right).
```

The left expression exceeds 157/50 by `107/179250`.
The right expression is smaller than 377/120; clearing its positive
denominators leaves the positive numerator 233638979 over denominator
5119469625000. These integers are optional arithmetic bookkeeping for two
explicit finite expressions, not a coefficient vector or an unexplained
success flag. Also `377/120<22/7` by a one-line cross multiplication.

Only two and three terms of an integral expansion are used. No digit-by-digit
pi computation or generated radical witness table is needed for these bounds.

## 3. What this does and does not claim

This proves the stated numerical assumptions for the human argument. It does
not purport to replace all pi lemmas imported anywhere in mathlib or to provide
a compiled Lean development of arctangent integration. The existing library's
axioms, automation, and source history are a separate formal dependency matter.
For integration, the exact same inequalities can be obtained from standard
pi-bound theorems, or this short derivation can be formalized locally.

The elementary sine/cosine Taylor inequalities used in the other notes have a
similarly transparent derivation: start from `sin x<=x` for x>=0 and integrate
successively from zero. In particular `S7(x)<=sin x<=S5(x)` and
`1-x^2/2<=cos x<=1-x^2/2+x^4/24` are whole-interval inequalities, not samples.
