# Three hand arguments for the nineteen axis-aligned terminal leaves

All nineteen leaves of the six-case exact axis-aligned exclusion at
`q <= 49013/10000` contain one of three coordinate-chain structures. Ten
contain a six-square stress structure, seven contain two disjoint parallel
four-square chains, and two contain a three-square fork.

These arguments replace the final numerical contradiction of each leaf with a
short hand inequality. The current extraction of some separating edges still
uses exact interval propagation. Thus this note does **not** claim a completely
table-free derivation of the finite cover or every forced separator.

## Two disjoint four-square chains

Two disjoint four-square chains in one common coordinate direction imply
`q >= 5` for any coordinate-separable packing at `q <= 5`. This is the
two-chain stress proved in `COORDINATE_RANK_CASES.md`: the bottom endpoints
and top endpoints must separate in the perpendicular direction, and support
vectors `(plus or minus 1, plus or minus 2)` give

    4 sqrt(5q) >= 20.

For axis-aligned squares the support calculation specializes directly; all
frame-angle estimates become equalities. Every use below has four distinct
vertices in each chain and disjoint vertex sets between the chains.

## The six-square stress

Let A,B,C,D,E,F be distinct axis-aligned unit squares. The required chains give

    x_C-x_A >= 1;       x_E-x_C >= 1;
    x_F-x_B >= 3;       x_F-x_D >= 2;
    y_B-y_A >= 1;       y_D-y_C >= 3;
    y_F-y_E >= 2.

Weights `1,4,4,5,1,9,6` give the six support vectors

    (-1,-1), (-4,1), (-3,-9), (-5,9), (4,-6), (9,6).

The separation terms total 67, and the six square support terms total 29.
Consequently

    96 <= R (sqrt(2)+sqrt(17)+3sqrt(10)+sqrt(106)+5sqrt(13))
       < R * (1084/25).

The rational square-root comparisons and complete proof appear in
`AXIS_ALIGNED_COUNTEREXAMPLE_AND_TERMINAL.md`. They give

    q > 360000/73441 > 49013/10000.

Reflecting either coordinate or swapping coordinates preserves disk packing
and transfers this radius contradiction. No equality classification modulo
reflection is asserted.

## The three-square fork

Let A,B,C be axis-aligned unit squares with

    x_B-x_A >= 3;       x_C-x_A >= 3;       y_C-y_B >= 2.

Then `R >= 73/32`, and hence `q >= 5329/1024 > 5`.

Proof. A leftmost corner of A lies in the disk, so `x_A-1/2 >= -R`.
The bottom-right corner of B and the top-right corner of C consequently
both have x coordinate at least `4-R`. Their y coordinates differ by at
least 3. One therefore has absolute y coordinate at least `3/2`.
If `R < 4`, this corner yields

    R^2 >= (4-R)^2 + 9/4,

so `8R >= 73/4`, as claimed. If `R >= 4`, the claimed lower bound is
immediate. Exchanging x and y gives the perpendicular fork.

## Complete leaf assignment

Indices below refer to each case's lexicographically sorted occupied cells in
`AXIS_EXCLUSION.json`. A path is the sequence of child indices from its root.
The machine-readable `AXIS_TERMINAL_GRAPHS.json` includes the actual
selected edges at closure, the terminal labels, and the coordinate transforms.

| Empty cells | Leaf path | Terminal |
| --- | --- | --- |
| (0,0), (1,1) | 0 | Two four-chains |
| (0,0), (1,1) | 1 | Two four-chains |
| (0,0), (1,0) | 00 | Two four-chains |
| (0,0), (1,0) | 01 | Six-square stress |
| (0,0), (1,0) | 10 | Two four-chains |
| (0,0), (1,0) | 11 | Six-square stress |
| (0,0), (2,0) | 0 | Six-square stress |
| (0,0), (2,0) | 1 | Six-square stress |
| (1,0), (0,1) | 00 | Three-square fork |
| (1,0), (0,1) | 010 | Six-square stress |
| (1,0), (0,1) | 011 | Two four-chains |
| (1,0), (0,1) | 100 | Two four-chains |
| (1,0), (0,1) | 101 | Six-square stress |
| (1,0), (0,1) | 11 | Three-square fork |
| (1,0), (0,2) | 00 | Two four-chains |
| (1,0), (0,2) | 01 | Six-square stress |
| (1,0), (0,2) | 1 | Six-square stress |
| (2,0), (0,2) | 0 | Six-square stress |
| (2,0), (0,2) | 1 | Six-square stress |

For the delicate centre-plus-east-outer-arm case, the positive-y leaf uses
`A=1,B=0,C=4,D=3,E=8,F=10`. Its seven paths are

    x: 1 -> 4; 4 -> 8; 0 -> 2 -> 6 -> 10; 3 -> 6 -> 10;
    y: 1 -> 0; 4 -> 5 -> 2 -> 3; 8 -> 9 -> 10.

The other leaf is the reflection in the x axis, with
`A=3,B=0,C=7,D=1,E=10,F=8` after reversing y.

For the first fork leaf, the occupied-cell indices are `A=0,B=8,C=9`, with

    x: 0 -> 2 -> 5 -> 8; 0 -> 2 -> 6 -> 9;
    y: 8 -> 10 -> 9.

For the second fork leaf, exchange coordinates and take `A=4,B=3,C=9`:

    y: 4 -> 5 -> 2 -> 3; 4 -> 5 -> 6 -> 9;
    x: 3 -> 7 -> 9.

Every displayed path uses edges actually recorded before that leaf's interval
contradiction; the stress and fork do not assume any of the remaining unresolved
separator alternatives.
