# Complete common-coordinate exclusion in the eleven-square candidate window

**Theorem.** No eleven axis-aligned unit squares pack a disk of squared
radius q<=U=49013/10000. Consequently no eleven-square packing in this
window has a common orthogonal separating frame, even if its squares have
independent orientations.

The second statement follows from [the shrinking theorem](COORDINATE_SHRINKING_REDUCTION.md).
The first has six geometric cases and an exact interval certificate with
32 nodes and 19 contradiction leaves. A separate implementation replays every
leaf with rational intervals, different precision and simultaneous updates.
This closes the whole common-coordinate branch, including all 1105 earlier
rank masks. The unrestricted oblique lower bound remains open.

## 1. Thirteen fixed cells cover every center

An axis-aligned unit square centered at (x,y) lies in the centered disk
exactly when

    (|x|+1/2)^2+(|y|+1/2)^2 <= q.                         (D)

Partition the plane into half-open unit cells

    [a-1/2,a+1/2) × [b-1/2,b+1/2),    (a,b) in Z².

At most one center lies in each cell: two centers in a cell differ by less
than one on both coordinates, so their unit-square interiors overlap.

For q<=U<5, (D) gives |x|,|y|<2, hence only cell indices -2 through 2
can occur. If |a|=2 and |b|>=1, then |x|>=3/2 and |y|>=1/2 (with one
bound possibly strict), so (D) would give q>=4+1=5. The transposed case
is identical. Thus the only possible cells are

    S = {-1,0,1}² ∪ {(-2,0),(2,0),(0,-2),(0,2)}.

This is a cross of thirteen cells. Eleven squares occupy eleven distinct
cells and leave exactly two holes.

## 2. Twenty-eight hole pairs and six symmetry representatives

The five cells in the middle row cannot all be occupied. Their centers have
y coordinates in the same half-open unit interval, so they form an x-chain
of five unit squares. The disk would have width at least five, whereas
2sqrt(U)<5. The same argument applies to the middle column.

The two holes must therefore hit both the middle row and the middle column.
If the central cell is a hole, its companion can be any of the other twelve
cells. Otherwise one hole is on the noncentral middle row and one on the
noncentral middle column, giving 4×4=16 possibilities. Total: 28.

Coordinate reflections and interchange give precisely these six orbits:

| Case | Two representative holes | Orbit size | Binary pairs | Tree nodes | Leaves |
| --- | --- | ---: | ---: | ---: | ---: |
| A1 | (0,0), (1,1) | 4 | 10 | 3 | 2 |
| A2 | (0,0), (1,0) | 4 | 10 | 7 | 4 |
| A3 | (0,0), (2,0) | 4 | 10 | 3 | 2 |
| A4 | (1,0), (0,1) | 4 | 13 | 11 | 6 |
| A5 | (1,0), (0,2) | 8 | 12 | 5 | 3 |
| A6 | (2,0), (0,2) | 4 | 12 | 3 | 2 |
| Total | | 28 | | 32 | 19 |

**Boundary convention:** half-open cells establish injection and the forced
same-row/column separators before taking symmetries. After a reflection use
closed cell membership and transport those separators. A reflection need
not preserve the original half-open endpoint convention. No argument relies
on reassigning reflected boundary centers to half-open cells.

## 3. Exact domain for each case

Label the eleven occupied cells lexicographically. The two variables of
label i lie in the corresponding closed unit coordinate intervals. Keep
the following necessary pair constraints:

- Centers in the same original cell row must separate in x; centers in the
  same original cell column must separate in y. Their directions follow
  the cell order, and the coordinate gap is at least one.
- If cell indices differ by at least two in x or y, closed cell membership
  already gives a gap of at least one in that coordinate.
- The only remaining pairs have cell differences of absolute value one
  in both coordinates. Their exact nonoverlap condition is the disjunction
  of the directed x-gap>=1 and the directed y-gap>=1.

All original 55 pairs are accounted for. In particular, no diagonal pair is
declared separated from its picture alone. These disjunctions provide the
binary branches of the certificate. The fixed constraints, disjunctions and
closed box form an enclosing domain of every physical packing in the case.

## 4. Sound interval rules

An interval state gives lower and upper bounds for all 22 coordinates,
retaining every solution of its parent domain. The following updates preserve
that invariant.

**Disk rule.** If the smallest possible absolute value of y in its current
interval is m, then (D) gives

    |x| <= sqrt(U-(m+1/2)^2)-1/2.                           (I)

If the radicand is negative the domain is empty. Otherwise intersect the
x interval with the symmetric bound in (I), using an outward upper enclosure
for the square root. Swap x,y for the other coordinate update.

**Gap rule.** A selected directed separator z_b-z_a>=1 implies

    lower_b >= lower_a+1,       upper_a <= upper_b-1.        (G)

Intersect the bounds accordingly. It is impossible if upper_b-lower_a<1.

**Disjunction rule.** If one axis of a diagonal pair has maximum possible
gap less than one, the other axis is forced. If both fail, the domain is
empty. If neither fails, branching on both alternatives covers the parent,
including the overlap where both hold.

An empty coordinate interval is a contradiction. Iterating these rules is
sound by induction; no convergence theorem is needed. The supplied finite
certificate terminates with contradictions at every leaf.

## 5. Integer generation and independent rational replay

`axis_exclusion.py` stores outward bounds as multiples of 1/D with D=10^8.
Every disk update uses an integer radicand

    N = U*D²-(m*D+D/2)².

Here U*D² is an integer. If N>=0, `ceil_sqrt(N)` is computed by integer
square root and satisfies its defining square inequalities. The upper
bound is `(ceil_sqrt(N)-D/2)/D`; it encloses the true limit in (I).
Gap updates and contradiction comparisons use integers only. A propagation
limit or a surviving fully assigned leaf raises an error instead of claiming
closure.

The complete generated tree is `AXIS_EXCLUSION.json`. Its internal nodes
state genuine two-axis pair alternatives; its leaves record contradictions.
The separate `replay_axis_exclusion.py` imports no generator code. It:

1. enumerates all 28 admissible hole pairs and verifies their six disjoint
   symmetry orbits;
2. reconstructs all coordinate domains and separator alternatives;
3. checks every internal split is an original pair disjunction with both
   children present;
4. discards the generator's leaf summaries and independently derives a
   contradiction at each leaf, using Fraction intervals, outward square-root
   rounding to 10^-6, and simultaneous updates.

The independent replay checks all 32 nodes and 19 leaves; no leaf needs more
than 49 simultaneous rounds. Its assertions are mandatory; optimized Python
execution is rejected. Neither implementation uses floating-point arithmetic.

```sh
python3 axis_exclusion.py --check AXIS_EXCLUSION.json
python3 replay_axis_exclusion.py AXIS_EXCLUSION.json
```

The arithmetic programs check the finite certificate. Sections 1–4 prove
why that certificate covers physical packings and why its arithmetic
contradictions imply the theorem. This is an exact computer-assisted hand
argument, not Lean kernel verification.

## 6. Assembly and remaining global obligation

Every axis-aligned packing at q<=U would enter one of the six cases and a
leaf of its covering binary tree. All leaves are impossible. Thus no such
axis-aligned packing exists. The shrinking theorem maps every hypothesized
common-coordinate-separable packing in the same disk to an axis-aligned
one, so that entire larger class is impossible as well.

Since an exact unrestricted construction attains q_c<U, every unrestricted
minimizer and every packing at q<=q_c must lie in the oblique branch.
There is no common-coordinate equality case at the candidate radius.

This is a strict exclusion at U, not a claim that the whole common-coordinate
class has lower bound five. The axis-aligned counterexample below five is
consistent with this result. The next global task is the oblique reduction
and its sharp certificates; the old 1105 rank masks no longer block it.

## Hand inequalities for all terminal graphs

[Three terminal arguments](THREE_AXIS_TERMINAL_LEMMAS.md) now explain all
19 leaves: ten contain a six-square stress, seven contain two disjoint
four-chains, and two contain a three-square fork. Exact interval propagation
still supplies forced separators; the final radius contradictions are the
written support and corner inequalities. `check_axis_terminal_graphs.py`
replays every node and verifies each directed path and symmetry transform.

The [exact negative control](AXIS_ALIGNED_COUNTEREXAMPLE_AND_TERMINAL.md)
exhibits an axis-aligned packing at q<4.91. The exclusion at U is deliberately
more precise than the false guess that every such packing needs q>=5.
