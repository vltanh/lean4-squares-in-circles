module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the data of the pair table `FourTypeCoreCornerLow`

Its arcs, the quadratic label of each arc with its side, its problems and its
fixed-point context, checked against the arcs once.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerLow
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 0, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (7506931/1000000), (-269343/250000)⟩⟩,
      ⟨1, 1, true, false, ⟨0, (1/4)⟩, ⟨(571311749126697/1000000000000000), (-3231/8000), (-217813/200000)⟩⟩,
      ⟨2, 1, true, true, ⟨0, (1/4)⟩, ⟨(-71413968640837/125000000000000), (3231/8000), (217813/200000)⟩⟩,
      ⟨3, 0, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (-7506931/1000000), (269343/250000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => (9/50)
    target := fun _ => (91/100)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩, true),
  (⟨(45704939930135722691397/80000000000000000000000), (457049399301357226917201/800000000000000000000000), (-3231/8000), (-217813/200000), 0, 0⟩, false),
  (⟨(-457049399301357226917201/800000000000000000000000), (-45704939930135722691397/80000000000000000000000), (3231/8000), (217813/200000), 0, 0⟩, false),
  (⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩, true)]

/-- The problems of the table: `fourTypeProblem .coreCorner .low σ τ four` for the cases
`(σ, τ, four)` of `fourTypeCases`, in order. -/
def problems : List PairProblem :=
  FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .coreCorner .low c.1 c.2.1 c.2.2

def ctx : TableCtx :=
  ⟨100000000, 4,
    [int_rows% "../../../../../data/eight/pairs/four_type_core_corner_low.arcs" 8 12 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/four_type_core_corner_low.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/four_type_core_corner_low.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 4 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 4)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerLow
