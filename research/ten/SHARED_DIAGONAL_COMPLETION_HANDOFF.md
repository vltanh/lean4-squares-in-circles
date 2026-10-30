# Shared diagonal completion: frozen research handoff

**Status: NOT PROMOTED.** This records an existing, unreviewed local
argument and the remaining gap. It is not a whole-signature exclusion,
an exact existence certificate, or a completion-capacity bound. No case
count changes follow from this note.

The reviewed direction restriction is
[DIAGONAL_ENDPOINT_NONEMPTY_PATH_DIRECTION.md](DIAGONAL_ENDPOINT_NONEMPTY_PATH_DIRECTION.md);
its root and independent full reviews passed before the final handoff. That result applies to any
degree-two loaded D endpoint whose other path has width at least one.
The other path cannot point outward from the D strip. Its D/S corollary
retains both unique and radial circle features, including arbitrary
nonnegative radial circle-load splits.

## Existing local argument: opposite unique circle signs in LSLSLD

Assume the selected-certificate hypotheses of the direction note and a
three-loaded cycle with one D path A--B and single S paths A--C and
B--C. Assume **both A and B have unique geometric circle vertices**.
Use the direction note's parallel frame and suppose, for contradiction,
that A's circle vertex is lower and B's is upper:

```text
A=[−u,1−u]×[−H_A,1−H_A],
B=[v−1,v]×[H_B−1,H_B],
u+v=2+sqrt(2),       H_A,H_B>1/2.
```

The common D force height h lies strictly inside both vertical intervals,
so

```text
H_B−1<h<1−H_A,       H_A+H_B<2.                 (1)
```

By the direction restriction and vertical force balance, the unit S
directions from A and B have the forms

```text
n_A=(p,q),       p≥0, q>0,
n_B=(−r,−s),    r≥0, s>0.
```

If p>0, A's S support is its upper inner corner
`P_A=(1−u,1−H_A)`. Torque about its unique circle vertex
`Z_A=(−u,−H_A)` gives, for positive D and S magnitudes mu and sigma,

```text
mu(h+H_A)=sigma(q−p)>0.
```

Therefore q>p and q>1/sqrt(2). If p=0, the S direction is vertical and
q=1, so the same strict bound holds. Reflecting the argument at B gives
s>1/sqrt(2), including its horizontal-side support alternative r=0.

The two far S contacts belong to the same unit square C. Their heights
are respectively `1−H_A+q` and `H_B−1−s`. By (1), their vertical
separation is

```text
2−H_A−H_B+q+s > sqrt(2).
```

A unit square has vertical width at most sqrt(2), a contradiction.
Thus this argument, if independently validated, leaves only equal
upper/lower signs when both D endpoints have unique circle vertices.
It does not cover either endpoint having two geometric circle vertices,
even when one of those vertices has zero circle coefficient.

## Remaining whole-case gap

The exploratory six-body configuration in
`ONE_DIAGONAL_TWO_SIDE_COMPONENT_CANDIDATE.md` has the same unique-circle
sign at A and B, positive numerical stress, and radius about 2.03253.
It is a numerical research example, not a rigorous existence certificate;
it nevertheless shows why a claimed internal component contradiction
needs scrutiny. The desired whole LSLSLD result needs a uniform
completion-capacity bound excluding four further squares, or another
valid whole-case argument.

The next unresolved normalization is the radial endpoint branch with its
full circle-load split. The steep-direction torque identity above uses
a unique geometric circle vertex and cannot simply be transferred to
that branch. After radial cases are controlled, the remaining same-sign
geometry still requires uniform bounds on the loaded endpoints, the
central source, and both transmitter slides. The published six-center
cover only handles its stated small center regions; those regions have
not been proved to cover every LSLSLD realization.

The shared direction theorem can also constrain other D-containing
cycles. Its width-at-least-one hypothesis excludes a direct loaded edge;
no conclusion for a D endpoint's direct loaded neighbor is asserted.
