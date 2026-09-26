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
| `Three.model_packing` | the squares at `Three.centers` form a packing of radius `Three.radius` |
| `Three.optimality` | `Packing S o R → Three.radius ≤ R` |
| `Three.uniqueness` | `Packing S o Three.radius → HasNormalForm S o Three.centers` |
| `Three.optimum` | the three above, as an `Optimum 3` |

`Optimum` (`Common/Optimum.lean`) bundles a lower bound, the packings of the
optimal layouts and uniqueness; attainment (`Optimum.attainment`), the converse
of uniqueness (`Optimum.packing_iff`) and its rigid form follow from them once,
for every case. The root theorems are these, for the `optimum` of each `n`.

For seven squares the optimum is not unique: `Seven.sliding_packing` shows
that the middle column of the optimal packing can take any position in a range
of total slack `2√3 - 3`, and `Seven.uniqueness` shows that these are all the
optimal packings, so `Seven.optimum` has the layouts
`Set.range Seven.slidingCenters`. `Seven.classification_by_slots` parametrizes
the family by the four gaps of the column, nonnegative with sum `2√3 - 3`.
Two stronger statements are proved on the way.
`Seven.six_exterior_squared_lower` gives `13/4 ≤ R^2` already for six squares
none of which contains the disk centre in its interior.
`Seven.marker_separation` is the pair theorem of
[seven squares](proof/seven.md#theorem-716-marker-separation), about just two
disjoint squares.

`Five.polygon_uniqueness` needs only interior-disjointness and the closed 12-gon
of [Step 1 for five squares](proof/five.md#step-1-the-contact-polygon), not the
disk.

**Polygon relaxations.** For three and five squares the proofs go through
stronger statements that mention no disk at all:
`Three.polygon_strict_impossible` and `Five.polygon_strict_impossible` rule out
`n` interior-disjoint squares whose centres all satisfy the strict contact
polygon of Step 1 in [the proof outline](proof/README.md#three-to-five-squares).
For four squares, `Four.diamond_impossible` needs the closed disk as well as the
strict diamond.
