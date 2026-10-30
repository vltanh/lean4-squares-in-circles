module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the data of the pair table `Short3`

Its arcs, the quadratic label of each arc with its side, its problems and its
fixed-point context, checked against the arcs once.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Short3
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 3, true, false, ⟨0, 1⟩, ⟨(25433/50000), (-33147/100000), (-1417/1250)⟩⟩,
      ⟨1, 4, true, false, ⟨0, 1⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨2, 3, true, true, ⟨0, (1/16)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨3, 3, true, true, ⟨(1/16), (1/8)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨4, 3, true, true, ⟨(1/8), (1/4)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨5, 3, true, true, ⟨(1/4), (1/2)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨6, 3, true, true, ⟨(1/2), 1⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨7, 3, true, true, ⟨0, 1⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨8, 3, true, true, ⟨0, (1/8)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨9, 4, true, false, ⟨0, (1/2)⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨10, 4, true, false, ⟨(1/2), (3/4)⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨11, 4, true, false, ⟨(3/4), (7/8)⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨12, 4, true, false, ⟨(7/8), (15/16)⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨13, 4, true, false, ⟨(15/16), 1⟩, ⟨(-23483/100000), (3867/20000), (-9593/12500)⟩⟩,
      ⟨14, 3, true, true, ⟨0, (1/4)⟩, ⟨(-68803/100000), (25777/50000), (119909/100000)⟩⟩,
      ⟨15, 4, true, true, ⟨0, 1⟩, ⟨(3147/50000), 0, (71553/100000)⟩⟩,
      ⟨16, 4, false, false, ⟨0, (6/7)⟩, ⟨(3897/100000), 0, (-104073/100000)⟩⟩,
      ⟨17, 4, false, true, ⟨0, (6/7)⟩, ⟨(6453/25000), 0, (58829/100000)⟩⟩,
      ⟨18, 4, false, false, ⟨(6/7), 1⟩, ⟨(3897/100000), 0, (-104073/100000)⟩⟩,
      ⟨19, 4, false, true, ⟨(6/7), 1⟩, ⟨(6453/25000), 0, (58829/100000)⟩⟩,
      ⟨20, 3, false, false, ⟨0, (6/7)⟩, ⟨(-777/5000), 0, (-251/400)⟩⟩,
      ⟨21, 3, false, true, ⟨0, (6/7)⟩, ⟨(4149/100000), 0, (104729/100000)⟩⟩,
      ⟨22, 3, false, false, ⟨(6/7), 1⟩, ⟨(-777/5000), 0, (-251/400)⟩⟩,
      ⟨23, 3, false, true, ⟨(6/7), 1⟩, ⟨(4149/100000), 0, (104729/100000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => 0
    target := fun _ => (17953/20000)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(25433/50000), (25433/50000), (-33147/100000), (-1417/1250), 0, 0⟩, true),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-23483/100000), (-23483/100000), (3867/20000), (-9593/12500), 0, 0⟩, false),
  (⟨(-68803/100000), (-68803/100000), (25777/50000), (119909/100000), 0, 0⟩, true),
  (⟨(3147/50000), (3147/50000), 0, (71553/100000), 0, 0⟩, false),
  (⟨(3897/100000), (3897/100000), 0, (-104073/100000), 0, 0⟩, false),
  (⟨(6453/25000), (6453/25000), 0, (58829/100000), 0, 0⟩, false),
  (⟨(3897/100000), (3897/100000), 0, (-104073/100000), 0, 0⟩, false),
  (⟨(6453/25000), (6453/25000), 0, (58829/100000), 0, 0⟩, false),
  (⟨(-777/5000), (-777/5000), 0, (-251/400), 0, 0⟩, true),
  (⟨(4149/100000), (4149/100000), 0, (104729/100000), 0, 0⟩, true),
  (⟨(-777/5000), (-777/5000), 0, (-251/400), 0, 0⟩, true),
  (⟨(4149/100000), (4149/100000), 0, (104729/100000), 0, 0⟩, true)]

/-- The problems of the table: `wrongPairProblem .short 3 ks kt σ τ j` for the cases
`(ks, kt, σ, τ, j)` of `wrongCases .short 3`, in order. -/
def problems : List PairProblem :=
  (WordGeometry.wrongCases .short 3).map fun c =>
    WordGeometry.wrongPairProblem .short 3 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

def ctx : TableCtx :=
  ⟨100000000, 24,
    [int_rows% "../../../../../data/eight/pairs/short_3.arcs" 8 32 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/short_3.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/short_3.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 : boxesRange table.radius table.arcs ctx.boxes 0 24 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 24)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Pairs.Short3
