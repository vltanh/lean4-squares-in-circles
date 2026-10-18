module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public meta import SquaresInCircles.Eight.IntRows

/-! The data of the pair table `FourTypeCoreCornerHigh`: its arcs, the quadratic label of each arc with its
side, its problems and its fixed-point context, checked once. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerHigh
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 0, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (7506931/1000000), (-269343/250000)⟩⟩,
      ⟨1, 1, true, false, ⟨(3/7), 1⟩, ⟨(-945985206429077/1000000000000000), (8898/15625), (-195443/500000)⟩⟩,
      ⟨2, 1, true, true, ⟨(3/7), 1⟩, ⟨(472992603214539/500000000000000), (-8898/15625), (195443/500000)⟩⟩,
      ⟨3, 0, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (-7506931/1000000), (269343/250000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => (9/50)
    target := fun _ => (8833/10000)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩, true),
  (⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩, false),
  (⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩, false),
  (⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩, true)]

/-- The problems of the table. -/
def problems : List PairProblem := [
  ⟨⟨false, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩⟩,
    ⟨true, false, false, ⟨(3/7), 1⟩, ⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩⟩,
    .one, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩⟩,
    ⟨true, false, false, ⟨(3/7), 1⟩, ⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩⟩,
    .four, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩⟩,
    ⟨true, false, true, ⟨(3/7), 1⟩, ⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩⟩,
    .one, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, false, ⟨(6/7), 1⟩, ⟨(-52548517/12000000), (-52548517/12000000), (7506931/1000000), (-269343/250000), 0, 0⟩⟩,
    ⟨true, false, true, ⟨(3/7), 1⟩, ⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩⟩,
    .four, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩⟩,
    ⟨true, false, false, ⟨(3/7), 1⟩, ⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩⟩,
    .one, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩⟩,
    ⟨true, false, false, ⟨(3/7), 1⟩, ⟨(-2956203770090866838330807/3125000000000000000000000), (-47299260321453869400703619/50000000000000000000000000), (8898/15625), (-195443/500000), 0, 0⟩⟩,
    .four, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩⟩,
    ⟨true, false, true, ⟨(3/7), 1⟩, ⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩⟩,
    .one, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩,
  ⟨⟨false, false, true, ⟨(6/7), 1⟩, ⟨(52548517/12000000), (52548517/12000000), (-7506931/1000000), (269343/250000), 0, 0⟩⟩,
    ⟨true, false, true, ⟨(3/7), 1⟩, ⟨(47299260321453869400703619/50000000000000000000000000), (2956203770090866838330807/3125000000000000000000000), (-8898/15625), (195443/500000), 0, 0⟩⟩,
    .four, (9/50), (8833/10000), [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000), (2, false, 80000000), (2, true, 86000000)]⟩]

def ctx : TableCtx :=
  ⟨100000000, 4,
    [int_rows% "../../../../../data/eight/pairs/four_type_core_corner_high.arcs" 8 12 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/four_type_core_corner_high.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/four_type_core_corner_high.arcs" 1 8 ↦
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

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerHigh
