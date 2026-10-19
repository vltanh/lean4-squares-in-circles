module

public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the fixed-point context of the affine table `TUpperAffine`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TUpperAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 102,
    [int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 104 110 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 102 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 102)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[1, 0, 2, 3],
    [11, 10, 9, 8, 7, 6, 5, 4, 12, 13, 14, 15, 16, 17, 18, 19]],
   [[20],
    [27, 26, 25, 24, 23, 22, 21]],
   [[29, 28, 30, 31],
    [39, 38, 37, 36, 35, 34, 33, 32, 40, 41, 42, 43, 44, 45, 46, 47]],
   [[49, 48, 50, 51],
    [59, 58, 57, 56, 55, 54, 53, 52, 60, 61, 62, 63, 64, 65, 66, 67]],
   [[68, 69],
    [70, 71]],
   [[73, 72, 74, 75],
    [83, 82, 81, 80, 79, 78, 77, 76, 84, 85, 86, 87, 88, 89, 90, 91]],
   [[93, 92],
    [101, 100, 99, 98, 97, 96, 95, 94]]]

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den, ⟨760000000000000000000000, 1723185840707964601769912⟩,
    [⟨0, 0⟩, ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩],
    [-70000000000000000000000000000000, -70000000000000000000000000000000,
     -70000000000000000000000000000000, -70000000000000000000000000000000,
     -70000000000000000000000000000000, -70000000000000000000000000000000,
     -70000000000000000000000000000000],
    [70000000000000000000000000000000, 70000000000000000000000000000000,
     70000000000000000000000000000000, 70000000000000000000000000000000,
     70000000000000000000000000000000, 70000000000000000000000000000000,
     70000000000000000000000000000000],
    int_rows% "../../../../../data/eight/affine/T_UPPER_AFFINE.arcs" 8 110 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 102 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 102)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.TUpperAffine
