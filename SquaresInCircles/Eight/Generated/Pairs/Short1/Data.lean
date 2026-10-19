module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.IntRows

/-! The data of the pair table `Short1`: its arcs, the quadratic label of each arc with its
side, its problems and its fixed-point context, checked once. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Short1
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 1, true, false, ⟨0, 1⟩, ⟨(24463/100000), (-6711/50000), (-25957/25000)⟩⟩,
      ⟨1, 2, true, false, ⟨0, 1⟩, ⟨(-2623/100000), (9133/100000), (-44037/50000)⟩⟩,
      ⟨2, 1, true, true, ⟨0, 1⟩, ⟨(613/10000), 0, (4997/5000)⟩⟩,
      ⟨3, 2, false, false, ⟨0, (6/7)⟩, ⟨(73/625), 0, (-22771/20000)⟩⟩,
      ⟨4, 2, false, false, ⟨(6/7), 1⟩, ⟨(73/625), 0, (-22771/20000)⟩⟩,
      ⟨5, 1, false, false, ⟨0, (6/7)⟩, ⟨(-14041/100000), 0, (-12419/20000)⟩⟩,
      ⟨6, 1, false, true, ⟨0, (6/7)⟩, ⟨(1603/6250), 0, (12419/20000)⟩⟩,
      ⟨7, 1, false, false, ⟨(6/7), 1⟩, ⟨(-14041/100000), 0, (-12419/20000)⟩⟩,
      ⟨8, 1, false, true, ⟨(6/7), 1⟩, ⟨(1603/6250), 0, (12419/20000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => 0
    target := fun _ => (17953/20000)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(24463/100000), (24463/100000), (-6711/50000), (-25957/25000), 0, 0⟩, true),
  (⟨(-2623/100000), (-2623/100000), (9133/100000), (-44037/50000), 0, 0⟩, false),
  (⟨(613/10000), (613/10000), 0, (4997/5000), 0, 0⟩, true),
  (⟨(73/625), (73/625), 0, (-22771/20000), 0, 0⟩, false),
  (⟨(73/625), (73/625), 0, (-22771/20000), 0, 0⟩, false),
  (⟨(-14041/100000), (-14041/100000), 0, (-12419/20000), 0, 0⟩, true),
  (⟨(1603/6250), (1603/6250), 0, (12419/20000), 0, 0⟩, true),
  (⟨(-14041/100000), (-14041/100000), 0, (-12419/20000), 0, 0⟩, true),
  (⟨(1603/6250), (1603/6250), 0, (12419/20000), 0, 0⟩, true)]

/-- The problems of the table: `wrongPairProblem .short 1 ks kt σ τ j` for the cases
`(ks, kt, σ, τ, j)` of `wrongCases .short 1`, in order. -/
def problems : List PairProblem :=
  (WordGeometry.wrongCases .short 1).map fun c =>
    WordGeometry.wrongPairProblem .short 1 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

def ctx : TableCtx :=
  ⟨100000000, 9,
    [int_rows% "../../../../../data/eight/pairs/short_1.arcs" 8 17 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/short_1.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/short_1.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 9 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 9)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.Short1
