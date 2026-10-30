module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the fixed-point context of the affine table `DUpperAffine`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 199,
    [int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 200 207 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange table.radius table.arcs ctx.boxes 120 79 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 79)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    [31, 30, 29, 28, 27, 26, 25, 24, 32, 33, 34, 35, 36, 37, 38, 39]],
   [[47, 46, 45, 44, 43, 42, 41, 40],
    [54, 53, 52, 51, 50, 49, 48]],
   [[66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76,
     77, 78],
    [86, 85, 84, 83, 82, 81, 80, 79, 87, 88, 89, 90, 91, 92, 93, 94]],
   [[106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 107, 108, 109, 110, 111, 112, 113,
     114, 115, 116, 117, 118],
    [126, 125, 124, 123, 122, 121, 120, 119, 127, 128, 129, 130, 131, 132, 133, 134]],
   [[135, 136, 137, 138, 139, 140, 141, 142],
    [143, 144, 145, 146, 147, 148, 149]],
   [[154, 153, 152, 151, 150, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166],
    [170, 169, 168, 167, 171, 172, 173, 174, 175, 176, 177, 178]],
   [[190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179],
    [198, 197, 196, 195, 194, 193, 192, 191]]]

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
    int_rows% "../../../../../data/eight/affine/D_UPPER_AFFINE.arcs" 8 207 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 79 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 79)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
