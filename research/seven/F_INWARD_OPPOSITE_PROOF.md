# F — the inward-opposite inequality without a Bernstein vector

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Production target: `SquaresInCircles/Seven/InwardOppositeMinima.lean`,
`Seven.radialPolynomial_pos` and its use in `radialE_pos`.
This is a research handoff; no production file is modified.

## 1. The geometric quantity, before elimination

Let `(a,u)` be a side-labelled admissible source, `(A,v)` an axial-labelled
admissible target, and

```text
z = label(a,u) + 5v/4 - pi/6,
0 < z <= 5/8,             0 <= v <= 3/10.
```

The inward support sum is

```text
I = 1/2 - a - A sin z + (sin z)/2 + (v+1/2) cos z
  = 4z/5 + 2 remainder(a,u)/15
      - (A-1/2) sin z - (v+1/2)(1-cos z).
```

Here `remainder(a,u)=4-3a-2u` is the slack of the disk's tangent at
`(a,u)=(1,1/2)`. The existing geometric lemma `side_remainder_quadratic`
gives

```text
2 remainder(a,u)/15 >= (6/25)(z-5v/4)^2.
```

The target's far-corner disk gives

```text
A-1/2 <= sqrt(3-v-v^2)-1
       <= sqrt(3)-1-alpha v-beta v^2,
alpha=15/52,              beta=15/52+1/42.
```

The second comparison is a genuine circle-support estimate. To check it,
set `B=sqrt(3)-alpha v-beta v^2`. On this interval `B>0`, and

```text
B^2-(3-v-v^2)
 = (1-2 sqrt(3) alpha)v
   +(1-2 sqrt(3) beta+alpha^2)v^2
   +2 alpha beta v^3+beta^2 v^4 >= 0.
```

All four coefficients are nonnegative using `sqrt(3)<1733/1000`.
Thus the constants are support slopes, not unexplained positivity data.
This is the existing `circle_quadratic_upper` argument, retained unchanged.

## 2. Why a quadratic in v appears

Put `r=sqrt(3)-1`, so `73/100 < r < 733/1000`. Use

```text
sin z >= z-z^3/6,
sin z <= z-z^3/6+z^5/120,
cos z >= 1-z^2/2+z^4/24-z^6/720.
```

These bounds have the correct signs on the whole interval. They give

```text
I >= E(z,v) = B(z)+v L(z)+v^2 K(z)+(6/25)(z-5v/4)^2,

B(z) = 67z/1000-z^2/4+73z^3/600+z^4/48
       -733z^5/120000-z^6/1440,
L(z) = (15/52)(z-z^3/6)-(z^2/2-z^4/24+z^6/720),
K(z) = (15/52+1/42)(z-z^3/6).
```

This explains the polynomialization: the target circle gives a quadratic
penalty in v, and the source's tangent slack gives a second quadratic penalty.
It is useful to combine them and complete one square, rather than separately
optimizing the two states.

Writing `H=K(z)+3/8>0` and `J=L(z)-3z/5`, expansion gives

```text
4H E(z,v) = (2Hv+J)^2 + z P(z),
```

where P is the existing degree-11 polynomial:

```text
P(z) = 201/2000 -(201353/7098000)z -(3091/21840)z^2
       -(1571239/14196000)z^3 -(23103/7280000)z^4
       +(977419/182520000)z^5 -(13/6300)z^6
       -(364297/196560000)z^7 +z^8/90720+z^9/8640-z^11/518400.
```

No root of P, numerical minimum, or subdivision is needed.

## 3. The new sign argument: P is decreasing

Differentiate P. The only positive terms in P' are

```text
(977419/36504000)z^4 + z^7/11340 + z^8/960.
```

Every other nonconstant term of P' has a negative coefficient. On `0<=z<=1`,
all powers lie in `[0,1]`. Consequently

```text
P'(z) <= -201353/7098000 +977419/36504000 +1/11340 +1/960
       = -253/547560 < 0.
```

Thus P is strictly decreasing on the whole interval `[0,1]`, a stronger
monotonicity domain than we need. There is no sign case split.
The minimum on `[0,5/8]` is its right endpoint, and direct rational evaluation is

```text
P(5/8) = 125352005285647 / 418089296461824000 > 1/4000 > 0.
```

This one endpoint comparison is bookkeeping after the monotonicity argument.
It replaces the entire twelve-entry Bernstein vector. The reason for positivity
is now explicit: all positive derivative contributions together are smaller
than the magnitude of the negative constant derivative term.

Combining with the square in section 2 proves `E(z,v)>0` for every real v
when `0<z<=5/8`, and therefore proves the original inward support inequality
on its stated geometric domain.

## 4. Strictness and downstream dependencies

`P>0` holds including z=0, but the completed-square argument uses `z>0`.
Do not extend `radialE_pos` to z=0: there `E(0,v)=3v^2/8` can vanish.
The original nonpositive-turn/contact branches handle that boundary.

The following production results retain their statements and existing proofs:

- `radial_discriminant_identity`;
- `radialE_pos`;
- `circle_quadratic_upper` and `radial_trig_lower`;
- `inward_circular_pos` and its boundary-minimum applications.

Only the body of `radialPolynomial_pos` needs replacement. This preserves all
strictness information used by the fixed-gap and equality arguments.

## 5. Lean handoff

Suggested helper statements, not claims of executed elaboration:

```lean
lemma radialPolynomial_derivative_bound {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    deriv radialPolynomial z ≤ -(253 / 547560) := ...

lemma radialPolynomial_antitone :
    AntitoneOn radialPolynomial (Set.Icc 0 1) := ...

lemma radialPolynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < radialPolynomial z := ...
```

Implementation recipe: write the derivative with `HasDerivAt`, using sums and
powers; bound `z^4,z^7,z^8` by 1 with `pow_le_pow_left₀`; discard the negative
terms using `pow_nonneg`; close the rational coefficient comparison with
`norm_num`/`linarith`. Apply `Seven.antiOn_of_hasDeriv_nonpos`, then compare
with `5/8` and evaluate the single endpoint. Do not invoke the old positivity
lemma while proving its replacement.

## Validation

The derivative coefficients, the identity `-253/547560`, the completed square,
and the endpoint fraction were independently checked by exact symbolic/rational
arithmetic during this research. The proof above does not assume that check's
success. Lean compilation and kernel validation of a replacement are not yet
performed.
