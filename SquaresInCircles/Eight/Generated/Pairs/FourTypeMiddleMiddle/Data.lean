module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the data of the pair table `FourTypeMiddleMiddle`

Its arcs, the quadratic label of each arc with its side, its problems and its
fixed-point context, checked against the arcs once.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleMiddle
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 0, true, false, ⟨(1/4), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨1, 1, true, false, ⟨(1/4), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨2, 1, true, true, ⟨(1/4), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨3, 0, true, true, ⟨(19/56), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨4, 1, true, false, ⟨(19/56), (43/112)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨5, 0, true, true, ⟨(19/56), (43/112)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨6, 1, true, false, ⟨(43/112), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨7, 0, true, true, ⟨(43/112), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨8, 1, true, false, ⟨(43/112), (177/448)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨9, 1, true, false, ⟨(177/448), (13/32)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨10, 0, true, true, ⟨(43/112), (177/448)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨11, 1, true, false, ⟨(13/32), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩,
      ⟨12, 0, true, true, ⟨(177/448), (13/32)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨13, 0, true, true, ⟨(13/32), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨14, 0, true, true, ⟨(1/4), (3/7)⟩, ⟨(-85723/40000), (1489593/1000000), (1580219/1000000)⟩⟩,
      ⟨15, 1, true, false, ⟨(19/56), (3/7)⟩, ⟨(85723/40000), (-1489593/1000000), (-1580219/1000000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => (9/50)
    target := fun _ => (557/625)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(-85723/40000), (-85723/40000), (1489593/1000000), (1580219/1000000), 0, 0⟩, true),
  (⟨(85723/40000), (85723/40000), (-1489593/1000000), (-1580219/1000000), 0, 0⟩, false)]

/-- The problems of the table: `fourTypeProblem .middle .middle σ τ four` for the cases
`(σ, τ, four)` of `fourTypeCases`, in order. -/
def problems : List PairProblem :=
  FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .middle .middle c.1 c.2.1 c.2.2

def ctx : TableCtx :=
  ⟨100000000, 16,
    [int_rows% "../../../../../data/eight/pairs/four_type_middle_middle.arcs" 8 24 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/four_type_middle_middle.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/four_type_middle_middle.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 16 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 16)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleMiddle
