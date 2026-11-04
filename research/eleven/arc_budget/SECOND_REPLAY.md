# Independent arithmetic replay of the weighted arc covers

The parent researcher wrote `independent_arcs.py` and
`replay_weighted_arcs.py` independently of the generator. Neither imports
`exact_arcs.py` or `generate.py`. Both exact cover trees pass this replay:
4,367 core nodes, 423 ring nodes, and all 2,037 accepted arc leaves.

The geometric rule is the same contained rectangle and four-quadrant
intersection proved in `WEIGHTED_ARC_EXCLUSION.md`. This implementation
uses square-root scale 10^16 rather than 10^14. It always reduces arcsine
by the half-angle identity. Arctangent arguments above 1/2 are transformed
by atan(t)=pi/4-atan((1-t)/(1+t)); the remaining arctangent uses twenty
alternating terms. Machin's pi enclosure uses thirty-two terms at each
argument. These are outward rational intervals, with no floating-point
acceptance test.

The replay reconstructs every box from the two root domains and midpoint
splits. It checks all domain rejection inequalities strictly, validates
all metadata against explicit constants, and recomputes each leaf bound
using the separate arithmetic implementation. It also verifies the final
weighted-budget contradiction. Optimized Python is rejected.

From this directory run:

```sh
python3 replay_weighted_arcs.py
```

This independent execution checks a continuous-domain certificate. It
does not imply that the remaining three- and four-core packing classes
have been solved or that the candidate is globally optimal.

The same separate arithmetic primitives also pass
`python3 replay_universal_bound.py`: all 2,385 nodes and 980 accepted
leaves of the unconditional q>9/2 certificate. That replay checks the
five radii and rational weights independently against their specified
values, reconstructs every domain box, and verifies the final contradiction.
