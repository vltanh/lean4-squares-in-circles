module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.IntRows

/-! The data of the pair table `Short6`: its arcs, the quadratic label of each arc with its
side, its problems and its fixed-point context, checked once. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Short6
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  { radius := (9789/2500)
    arcs := [
      ⟨0, 6, true, false, ⟨0, 1⟩, ⟨(-933/5000), (9301/50000), (-20249/25000)⟩⟩,
      ⟨1, 0, true, true, ⟨0, 1⟩, ⟨0, 0, (47383/50000)⟩⟩,
      ⟨2, 6, true, true, ⟨0, (1/16)⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨3, 6, true, true, ⟨(1/16), (1/8)⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨4, 6, true, true, ⟨(1/8), (1/4)⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨5, 6, true, true, ⟨(1/4), (1/2)⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨6, 6, true, true, ⟨(1/2), 1⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨7, 6, true, true, ⟨0, 1⟩, ⟨(-647/3125), (10913/50000), (5217/6250)⟩⟩,
      ⟨8, 0, true, true, ⟨0, (1/2)⟩, ⟨0, 0, (47383/50000)⟩⟩,
      ⟨9, 0, true, true, ⟨(1/2), 1⟩, ⟨0, 0, (47383/50000)⟩⟩,
      ⟨10, 0, false, true, ⟨0, (6/7)⟩, ⟨(3177/100000), 0, (6801/6250)⟩⟩,
      ⟨11, 0, false, true, ⟨(6/7), 1⟩, ⟨(3177/100000), 0, (6801/6250)⟩⟩,
      ⟨12, 6, false, false, ⟨0, (6/7)⟩, ⟨(7651/100000), 0, (-99173/100000)⟩⟩,
      ⟨13, 6, false, true, ⟨0, (6/7)⟩, ⟨(567/6250), 0, (23831/25000)⟩⟩,
      ⟨14, 6, false, false, ⟨(6/7), 1⟩, ⟨(7651/100000), 0, (-99173/100000)⟩⟩,
      ⟨15, 6, false, true, ⟨(6/7), 1⟩, ⟨(567/6250), 0, (23831/25000)⟩⟩]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => 0
    target := fun _ => (17953/20000)
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
  (⟨(-933/5000), (-933/5000), (9301/50000), (-20249/25000), 0, 0⟩, true),
  (⟨0, 0, 0, (47383/50000), 0, 0⟩, false),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨(-647/3125), (-647/3125), (10913/50000), (5217/6250), 0, 0⟩, true),
  (⟨0, 0, 0, (47383/50000), 0, 0⟩, false),
  (⟨0, 0, 0, (47383/50000), 0, 0⟩, false),
  (⟨(3177/100000), (3177/100000), 0, (6801/6250), 0, 0⟩, false),
  (⟨(3177/100000), (3177/100000), 0, (6801/6250), 0, 0⟩, false),
  (⟨(7651/100000), (7651/100000), 0, (-99173/100000), 0, 0⟩, true),
  (⟨(567/6250), (567/6250), 0, (23831/25000), 0, 0⟩, true),
  (⟨(7651/100000), (7651/100000), 0, (-99173/100000), 0, 0⟩, true),
  (⟨(567/6250), (567/6250), 0, (23831/25000), 0, 0⟩, true)]

/-- The problems of the table: `wrongPairProblem .short 6 ks kt σ τ j` for the cases
`(ks, kt, σ, τ, j)` of `wrongCases .short 6`, in order. -/
def problems : List PairProblem :=
  (WordGeometry.wrongCases .short 6).map fun c =>
    WordGeometry.wrongPairProblem .short 6 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

def ctx : TableCtx :=
  ⟨100000000, 16,
    [int_rows% "../../../../../data/eight/pairs/short_6.arcs" 8 24 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/pairs/short_6.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/pairs/short_6.arcs" 1 8 ↦
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

end SquaresInCircles.Eight.Generated.Pairs.Short6
