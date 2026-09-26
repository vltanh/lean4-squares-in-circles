# Results

[Back to the README](../README.md)

The results for all six cases are in the root file `SquaresInCircles.lean`,
namespace `SquaresInCircles`. The same three theorems cover `n = 1, …, 5` and
`n = 7`:

```lean
theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)

theorem packing_iff (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ c ∈ optimalLayouts n, HasNormalForm S o c
```

`optimalLayouts n` is `{modelCenters n}` for `n ≤ 5`, so the optimal packing is
unique up to a rotation about the disk centre and a relabelling, and the set
of all positions of the middle column for `n = 7`
([Definitions](definitions.md#the-optimal-layouts)). `uniqueness` is the forward
direction of `packing_iff`, and `optimality_attainment_uniqueness` conjoins the
three. The statements use only the definitions in
[Definitions](definitions.md).

`rigid_uniqueness` restates uniqueness with the frame `pointInDirection o φ`
replaced by an explicit bijection `e` of the plane that preserves Euclidean
distance and takes the origin to `o`: under `e`, the open and the closed squares
are exactly the squares of an optimal layout.

**One framework.** Each case also stands alone, in namespaces
`SquaresInCircles.One`, …, `SquaresInCircles.Five` and `SquaresInCircles.Seven`
(folders `One/`, …, `Five/` and `Seven/`), and each proves the same things:

| declaration | for `n = 3` |
| --- | --- |
| `Three.radius`, `Three.centers` | the optimal radius and the optimal layout |
| `Three.model` | the axis-parallel squares at `Three.centers` |
| `Three.model_packing` | `Three.model` is a packing in the closed disk of radius `Three.radius` about the origin |
| `Three.uniqueness` | `Packing S o Three.radius → HasNormalForm S o Three.centers` |
| `Three.optimum` | the two above and a point of `Three.model` on the circle of radius `Three.radius`, as an `Optimum 3` |

`Optimum` (`Common/Optimum.lean`) bundles the packings of the optimal layouts,
a point of each on the circle of the optimal radius, and uniqueness. The rest
follows from them once, for every case: the lower bound
(`Optimum.optimality`), attainment (`Optimum.attainment`), the converse of
uniqueness (`Optimum.packing_iff`) and its rigid form. For the lower bound, a
packing in a smaller disk would also pack the optimal disk, so by uniqueness it
would have the normal form of an optimal layout, and the point on the circle
would lie outside the smaller disk. The root theorems are these, for the
`optimum` of each `n`.

For seven squares the optimum is not unique: `Seven.sliding_packing` shows
that the middle column of the optimal packing can take any position in a range
of total slack `2√3 - 3`, and `Seven.uniqueness` shows that these are all the
optimal packings, so `Seven.optimum` has the layouts
`Set.range Seven.slidingCenters`. `Seven.classification_by_slots` parametrizes
the family by the four gaps of the column, nonnegative with sum `2√3 - 3`.
The pair theorem of
[seven squares](proof/seven.md#theorem-715-marker-separation) is about just two
disjoint squares that avoid the disk centre and satisfy the farthest-vertex
bound of the disk of radius `√13 / 2`: their markers are at least `π/3` apart
(`Seven.marker_separation_closed`), and exactly `π/3` apart only if they touch
as in the optimal packing (`Seven.ordered_chart_contact`).

`Five.polygon_uniqueness` needs only interior-disjointness and the closed 12-gon
of [Step 1 for five squares](proof/five.md#step-1-the-contact-polygon), not the
disk.

**Polygon relaxations.** Of the arc proofs of
[three to five squares](proof/README.md#three-to-five-squares), only five
squares go through a statement that mentions no disk: `Five.polygon_uniqueness`,
above. The proof for three squares also uses the disk only in
[Step 1](proof/three.md#step-1-the-contact-polygon), through two tangent lines
and one strict tangent, but its Lean statements keep the disk. Four squares
keep the disk constraint throughout: the diamond alone would let the arc of an
exterior square shrink to nothing.
