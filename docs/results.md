# Results

[Back to the README](../README.md)

The results for all seven cases are in the root file `SquaresInCircles.lean`,
namespace `SquaresInCircles`. The same two theorems cover `n = 1, …, 7`:

```lean
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n)

theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M
```

`IsLeast s a` is mathlib's: `a ∈ s`, and `a ≤ R` for every `R ∈ s`. So
`optimal_radius` says both that some packing of `n` unit squares fits in a disk
of radius `optimalRadius n` and that none fits in a smaller one.
`optimal_packings` says that the packings of that radius are exactly the
configurations congruent to an optimal model. `optimalPackings n` is
`{X.model}` for the case `X` of `n ≤ 6`, so the optimal packing is unique up to
a rotation about the disk centre and a relabelling, and the set of all column
packings `Set.range Seven.columnModel` for `n = 7`
([Definitions](definitions.md#the-optimal-packings)). The statements use only
the definitions in [Definitions](definitions.md).

`optimal_packings_rigid` restates the forward direction of `optimal_packings`
with the frame `pointInDirection o φ` replaced by an explicit bijection `e` of
the plane that preserves Euclidean distance and takes the origin to `o`: under
`e`, the open and the closed squares are exactly the squares of an optimal
model.

**One framework.** Each case also stands alone, in namespaces
`SquaresInCircles.One`, …, `SquaresInCircles.Seven` (folders `One/`, …,
`Seven/`), and each proves the same things:

| declaration | for `n = 3` |
| --- | --- |
| `Three.radius`, `Three.centers` | the optimal radius and the centres of the optimal model |
| `Three.model` | the axis-parallel squares at `Three.centers` |
| `Three.model_packing` | `Three.model` is a packing in the closed disk of radius `Three.radius` about the origin |
| `Three.uniqueness` | `Packing S o Three.radius → Congruent S o Three.model` |
| `Three.optimum` | the two above and a point of `Three.model` on the circle of radius `Three.radius`, as an `Optimum 3` |

`Optimum` (`Common/Optimum.lean`) bundles the optimal models, their packings, a
point of each on the circle of the optimal radius, and uniqueness. The rest
follows from them once, for every case: the lower bound
(`Optimum.optimality`), the least radius (`Optimum.isLeast`), the converse of
uniqueness (`Optimum.packing_iff`) and its rigid form. For the lower bound, a
packing in a smaller disk would also pack the optimal disk, so by uniqueness it
would be congruent to an optimal model, and the point on the circle would lie
outside the smaller disk. The root theorems are these, for the `optimum` of
each `n`.

For seven squares the optimum is not unique: `Seven.column_packing` shows that
the three middle squares of the optimal packing can take any heights at least
1 apart within `√3 - 1/2` of the centre, a range of total slack `2√3 - 3`, and
`Seven.uniqueness` shows that these column packings are all the optimal
packings, so `Seven.optimum` has the models `Set.range Seven.columnModel`.
`Seven.classification_by_slots` parametrizes the family by the four gaps of the
column, nonnegative with sum `2√3 - 3`. The pair theorem of
[seven squares](proof/seven.md#theorem-924-marker-separation) is about just two
disjoint squares that avoid the disk centre and satisfy the farthest-vertex
bound of the disk of radius `√13 / 2`: their markers are at least `π/3` apart
(`Seven.marker_separation_closed`), and exactly `π/3` apart only if they touch
as in the optimal packing (`Seven.ordered_chart_contact`).

For six squares `Six.model` has five axis-parallel squares and one turned by
`π / 4`, `Six.diagonalSquare`, so there are no `Six.centers`. `Six.uniqueness`
goes through three steps, each a theorem of its own:
`Six.Normalization.normalize_of_candidate` puts any packing of squared radius
at most `Six.qStar` in a frame of the square that contains the disk centre,
with the other five labelled by fixed pins (up to a reflection in a diagonal);
`Six.Analytic.FixedPair.complete_reduction` shows that such a normalized
packing is separated as the optimal one is and has its angles in the domains
of the stress estimate; and
`Six.Equality.AnalyticReconstruction.original_congruent_of_reduction` turns
the tight stress at the radius `Six.radius` into congruence to `Six.model`.
The case builds on seven squares: `Six.exists_containing` uses the ring of
`Seven.six_exterior_ring` to find the square that contains the disk centre,
and `Six.Normalization.strict_marker_separation` sharpens the pair theorem of
seven squares below the radius `√13 / 2`.

`Five.polygon_uniqueness` needs only interior-disjointness and the closed 12-gon
of [Definition 8.4](proof/five.md#definition-84-the-12-gon), not the disk
([Proposition 8.6](proof/five.md#proposition-86-the-12-gon-is-rigid)).

**Polygon relaxations.** Of the arc proofs of
[three to five squares](proof/README.md#14-outline-of-the-proof), only five
squares go through a statement that mentions no disk: `Five.polygon_uniqueness`,
above. The proof for three squares also uses the disk only in
[§6.2](proof/three.md#62-the-contact-polygon), through two tangent lines
and one strict tangent, but its Lean statements keep the disk. Four squares
keep the disk constraint throughout: the diamond alone would let the arc of an
exterior square shrink to nothing.
