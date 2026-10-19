module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.IntRows

/-! The data of the pair table `Common1`: its arcs, the quadratic label of each arc with its
side, its problems and its fixed-point context, checked once. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Common1
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 0, true, false, ⟨0, 1⟩, ⟨(9/100), (-13/200), (-203/200)⟩⟩,
      ⟨1, 1, true, false, ⟨0, 1⟩, ⟨(9/100), (-13/200), (-203/200)⟩⟩,
      ⟨2, 1, true, true, ⟨0, 1⟩, ⟨(-9/100), (13/200), (203/200)⟩⟩,
      ⟨3, 0, true, true, ⟨0, 1⟩, ⟨(-9/100), (13/200), (203/200)⟩⟩,
      ⟨4, 1, false, false, ⟨0, (6/7)⟩, ⟨(-511/120), (73/10), (-291/250)⟩⟩,
      ⟨5, 1, false, true, ⟨0, (6/7)⟩, ⟨(511/120), (-73/10), (291/250)⟩⟩,
      ⟨6, 1, false, false, ⟨(6/7), 1⟩, ⟨(-511/120), (73/10), (-291/250)⟩⟩,
      ⟨7, 1, false, true, ⟨(6/7), 1⟩, ⟨(511/120), (-73/10), (291/250)⟩⟩,
      ⟨8, 0, false, false, ⟨0, (6/7)⟩, ⟨(-511/120), (73/10), (-291/250)⟩⟩,
      ⟨9, 0, false, true, ⟨0, (6/7)⟩, ⟨(511/120), (-73/10), (291/250)⟩⟩,
      ⟨10, 0, false, false, ⟨(6/7), 1⟩, ⟨(-511/120), (73/10), (-291/250)⟩⟩,
      ⟨11, 0, false, true, ⟨(6/7), 1⟩, ⟨(511/120), (-73/10), (291/250)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => 0
    target := fun _ => (157/200)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(9/100), (9/100), (-13/200), (-203/200), 0, 0⟩, true),
  (⟨(9/100), (9/100), (-13/200), (-203/200), 0, 0⟩, false),
  (⟨(-9/100), (-9/100), (13/200), (203/200), 0, 0⟩, false),
  (⟨(-9/100), (-9/100), (13/200), (203/200), 0, 0⟩, true),
  (⟨(-511/120), (-511/120), (73/10), (-291/250), 0, 0⟩, false),
  (⟨(511/120), (511/120), (-73/10), (291/250), 0, 0⟩, false),
  (⟨(-511/120), (-511/120), (73/10), (-291/250), 0, 0⟩, false),
  (⟨(511/120), (511/120), (-73/10), (291/250), 0, 0⟩, false),
  (⟨(-511/120), (-511/120), (73/10), (-291/250), 0, 0⟩, true),
  (⟨(511/120), (511/120), (-73/10), (291/250), 0, 0⟩, true),
  (⟨(-511/120), (-511/120), (73/10), (-291/250), 0, 0⟩, true),
  (⟨(511/120), (511/120), (-73/10), (291/250), 0, 0⟩, true)]

/-- The problems of the table: `commonPairProblem 1 ks kt σ τ j` for the cases
`(ks, kt, σ, τ, j)` of `commonCases 1`, in order. -/
def problems : List PairProblem :=
  (WordGeometry.commonCases 1).map fun c =>
    WordGeometry.commonPairProblem 1 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

def ctx : TableCtx :=
  ⟨100000000, 12,
    [int_rows% "../../../../../data/eight/pairs/common_1.arcs" 8 20 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/common_1.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/common_1.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 12 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 12)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.Common1
