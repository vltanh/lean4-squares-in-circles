# An unconditional lower bound: R > sqrt(19/5)

This theorem concerns ALL eight-square packings, unlike the conditional
five-corner optimality theorem. It is not yet sharp.

## Theorem

Eight interior-disjoint unit squares in a closed disk of radius R satisfy

    R^2 > 19/5.

Together with the exact construction, the current rigorously established
bounds in this research are therefore

    sqrt(19/5) < optimal eight-square radius <= R*,

where R* is the isolated algebraic candidate in FIVE_CORNER_OPTIMALITY.md.
Numerically the endpoints are approximately 1.94936 and 1.97877086534.
The nonzero gap between them has NOT been closed.

## Proof

At most one open square can contain the disk center, because the square
interiors are pairwise disjoint. Therefore at least seven of the eight squares
are exterior, meaning their open interiors avoid that center.

Assume R^2<=19/5. Apply the exact pair verifier to the same label as in
SHARP_MARKER_RING.md,

    ell(a,u)=min(11u/10, 5/9+3u/5-17a/50, 157/200),

but with squared-radius ceiling 19/5 and gap ceiling 44/49. All four sign
cases pass. Thus any two disjoint exterior squares have marker distance
strictly greater than 44/49.

Choose seven exterior squares and order their markers cyclically. Every
successive gap is greater than 44/49, so

    2*pi > 7*(44/49)=44/7.

This contradicts the elementary bound pi<22/7. Hence R^2>19/5.

This argument does not suppose a central square exists, does not discard a
central separation constraint at the sharp radius, and does not assume any
common square orientations or a candidate contact graph.

## Reproducible certificate

Compile the parameterized verifier as follows:

```sh
g++ -O3 -std=c++17 \
  -DN8_Q_NUM=19 -DN8_Q_DEN=5 \
  -DN8_GAP_NUM=44 -DN8_GAP_DEN=49 \
  research/eight/verify_sharp_exterior_markers.cpp -o /tmp/n8-lower-bound
/tmp/n8-lower-bound
```

The rational gap endpoint is rounded OUTWARD to the dyadic lattice. The
verifier checks every point up to that outward endpoint, which covers the
claimed exact interval [0,44/49]. All accepted bounds still use exact integer
arithmetic, not floating-point sampling.

Executed results:

| signs | Nodes | Positive terminal boxes | Maximum depth | Minimum leaf margin numerator, denominator 2^48 |
| --- | ---: | ---: | ---: | ---: |
| -1,-1 | 93131 | 46566 | 35 | 1280109847 |
| -1,+1 | 50251 | 25126 | 30 | 25225619 |
| +1,-1 | 335245 | 167623 | 36 | 9221640 |
| +1,+1 | 136699 | 68350 | 35 | 74080590 |

Every row satisfies nodes=2*positive_leaves-1. No empty terminal leaves remain
after the sound admissibility contractions. The arithmetic and trigonometric
soundness arguments are the same as in SHARP_MARKER_RING.md. This is a
computer-assisted mathematical lower bound, not a Lean formalization.

## Why a higher-dimensional search was not used to justify this bound

Exploratory global searches also retained all eight squares and all 28 pair
constraints in a normalized 23-variable interval problem. A direct search
and a conflict-directed variant both exhausted their node budgets, even at
squared radius 37/10. Their pruning rates establish nothing about the
unresolved cells. They are NOT lower-bound certificates.

The successful argument above avoids that failure by proving a stronger
low-dimensional pair lemma and summing its consequence around the circle.
The remaining sharp-radius problem still needs additional use of the central
obstacle or a different structural invariant.
