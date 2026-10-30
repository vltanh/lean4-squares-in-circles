module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the data of the pair table `FourTypeMiddleHigh`

Its arcs, the quadratic label of each arc with its side, its problems and its
fixed-point context, checked against the arcs once.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleHigh
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 0, true, false, ⟨(1/4), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨1, 1, true, false, ⟨(3/7), 1⟩, ⟨(-945985206429077/1000000000000000), (8898/15625), (-195443/500000)⟩⟩,
      ⟨2, 1, true, true, ⟨(3/7), 1⟩, ⟨(472992603214539/500000000000000), (-8898/15625), (195443/500000)⟩⟩,
      ⟨3, 0, true, true, ⟨(1/4), (19/56)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨4, 0, true, true, ⟨(19/56), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨5, 0, true, true, ⟨(1/4), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => (9/50)
    target := fun _ => (4463/5000)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, true),
  (⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩, false),
  (⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true)]

/-- The problems of the table: `fourTypeProblem .middle .high σ τ four` for the cases
`(σ, τ, four)` of `fourTypeCases`, in order. -/
def problems : List PairProblem :=
  FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .middle .high c.1 c.2.1 c.2.2

def ctx : TableCtx :=
  ⟨100000000, 6,
    [int_rows% "../../../../../data/eight/pairs/four_type_middle_high.arcs" 8 14 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/four_type_middle_high.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/four_type_middle_high.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 6 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 6)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleHigh
