# Unrestricted finite formulation and existence

This note states the remaining n=10 problem without a shared orientation,
column, contact graph, central-square, or symmetry assumption. It is an exact
hand formulation of the repository's `Packing` predicate after translating
the disk centre to zero. It is not an optimality certificate.

## Variables and constraints

For each `i=0,…,9`, let the square centre be `pᵢ=(xᵢ,yᵢ)` and its frame be

`uᵢ=(cᵢ,sᵢ)`, `vᵢ=(-sᵢ,cᵢ)`, with `cᵢ²+sᵢ²=1`.

Let `q` be the squared disk radius. To search for an optimum, the explicit
construction allows the restriction `0 ≤ q ≤ 9/2`.

**Containment: 40 vertex inequalities.** For each sign pair `ε,η ∈ {-1,1}`,

`‖pᵢ + (εuᵢ+ηvᵢ)/2‖₂² ≤ q`.

These are necessary and sufficient for whole-square containment because a
square is the convex hull of its vertices and the disk is convex.

**Nonoverlap: 45 separating-axis disjunctions.** For each `i<j`, put

`dᵢⱼ = cᵢcⱼ+sᵢsⱼ`, `eᵢⱼ = cᵢsⱼ−sᵢcⱼ`,

`Wᵢⱼ = (1+|dᵢⱼ|+|eᵢⱼ|)/2`.

Require at least one axis `a ∈ {uᵢ,vᵢ,uⱼ,vⱼ}` to satisfy

`|a·(pⱼ−pᵢ)| ≥ Wᵢⱼ`.

Along an axis owned by one square, that square has projection half-width
`1/2`; the other has half-width `(|dᵢⱼ|+|eᵢⱼ|)/2`. This explains the common
threshold on all four axes. The separating-axis theorem for rectangles makes
the disjunction equivalent to disjoint interiors. The weak inequality includes
edge and vertex contact. The repository proves the corresponding geometric
interface in `SquaresInCircles/Common/SeparatingAxes.lean`.

All norms here are Euclidean coordinate sums of squares, matching `normSq`.
The norm of Lean's product space `ℝ × ℝ` must not be substituted silently.

## An unrestricted minimizer exists

The feasible set is nonempty by the rational construction. Averaging the four
vertex inequalities for square `i` cancels the mixed terms and gives

`‖pᵢ‖₂² + 1/2 ≤ q ≤ 9/2`.

Hence `q ≥ 1/2` and `‖pᵢ‖₂ ≤ 2`; also `|cᵢ|,|sᵢ| ≤ 1`. The entire feasible
set is bounded in the finite-dimensional space of the 41 real variables
`q,(xᵢ,yᵢ,cᵢ,sᵢ)ᵢ`.

The unit-frame equations and vertex inequalities define closed sets. Each
pairwise nonoverlap condition is a finite union of closed sets, because the
functions involving absolute values are continuous and the inequalities are
weak. Their finite intersection is closed. The feasible set is therefore
compact. The continuous coordinate `q` attains a minimum on it.

Taking `R=√q` converts a minimizer back to an unrestricted `Packing`. Since a
packing at `9/2` exists, packings with larger squared radius cannot improve
this minimum. Thus this is a global existence argument, but it identifies
neither the minimum value nor its complete set of minimizers.

## The unresolved assertion

The sharp lower-bound target is:

> Every solution of the unrestricted constraints has `q ≥ 9/2`.

Equivalently, rule out all solutions with `q < 9/2`, retaining every sign,
axis-owner choice, and weak contact case. Fixing a contact graph or setting all
frames equal proves only a conditional statement unless an exhaustive reduction
is supplied. The [three-column theorem](THREE_COLUMN_THEOREM.md) closes one
such conditional class. Neither numerical optimization nor the rational
construction checker closes the remaining assertion.

After a sharp lower bound, equality necessity must be established separately.
The six-parameter sufficient family in `CONSTRUCTION.md` is a starting set of
examples, not an exhaustive equality classification.
