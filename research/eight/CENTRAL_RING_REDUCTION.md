# The central square and the seven-marker ring

This note records consequences of EXTERIOR_MARKER_CERTIFICATE.md. It does not identify the optimal contact graph.

## Theorem 1: unique central square at q <= 98/25

The verified pair certificate gives marker separation >4/5 for every pair of squares whose open interiors avoid the disk center. Eight such markers cannot lie on the circle because 8*(4/5)>2*pi. Thus one square contains the disk center in its open interior, and interior-disjointness makes it unique.

Translate the disk center to zero and rotate the containing square to be axis-parallel. Its center C=(cx,cy) satisfies |cx|,|cy|<1/2. Reflections and axis interchange can, if useful, impose 0<=cx<=cy<1/2. This normalization does not assume the other seven squares share its orientation.

## Theorem 2: every marker-quadrant partition has counts 2,2,2,1

Partition the circle into any four consecutive half-open arcs of length pi/2. No arc contains three exterior markers: three ordered markers would have successive separations each >4/5, so their first-to-last span would exceed 8/5>pi/2. All seven exterior markers are assigned exactly once. Since each quadrant has at most two, the counts must be a permutation of (2,2,2,1).

In particular this holds for quadrants fixed by the central square's frame. A quarter turn can place the singleton quadrant at a chosen location. This is a genuine finite reduction without choosing a numerical angle grid. It concerns MARKER directions, not a presupposed square-center/contact grid.

## Theorem 3: lower and upper bounds on every successive gap

Write the cyclic consecutive marker gaps as g1,...,g7. Each is >4/5, and their sum is 2*pi. Therefore

    4/5 < gi < 2*pi-24/5 < 52/35.

The final upper bound uses pi<22/7. Every arc of length 52/35 consequently meets at least one exterior marker. This can be used to reject proposed central-square positions that create an unavailable marker arc of that length.

## Central separation must remain an explicit constraint

The exact seven-exterior counterexample in NEGATIVE_RESULTS.md shows that the ring without the central square can fit below the candidate eight-square radius. Thus the current reduced problem is:

    central axis-parallel unit square C, |cx|,|cy|<1/2;
    seven exterior squares in q<=98/25;
    seven markers with cyclic gaps in (4/5,52/35);
    quadrant occupancy (2,2,2,1);
    every exterior square disjoint from C and from every other exterior square.

Each C/exterior pair still has the actual four-axis separating disjunction. No separator is selected merely because it occurs in the candidate. In particular, squared radius 98/25 is larger than the ceilings in the old n=6/n=7 normalization theorems, so their special OWN/cardinal exclusions and pin assignments cannot be assumed here.

## What remains to be forced

A sharp eight-square proof needs a further implication from this reduced problem to a sufficiently restrictive separator/contact structure, or a complete certificate eliminating all alternatives below the candidate. The 2,2,2,1 count alone does not establish parallelism, boundary contact, the five-corner construction polygon, or the candidate tilt.
