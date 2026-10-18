module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-! The fixed-point data of the table, checked against the exact data of `Meta`: the
arc boxes and the arctangent intervals of the arcs (in blocks), the scalars, the
state chains and the data of the angle coverage. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 303,
    [int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 200 232 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 232 264 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 264 296 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 296 311 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange table.radius table.arcs ctx.boxes 120 120 = true := by
  decide +kernel

theorem ctx_boxes_2 :
    boxesRange table.radius table.arcs ctx.boxes 240 63 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 120), (240, 63)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, ctx_boxes_2, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    [39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 40, 41, 42, 43, 44, 45,
     46, 47, 48, 49, 50, 51, 52, 53, 54, 55]],
   [[63, 62, 61, 60, 59, 58, 57, 56],
    [76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64]],
   [[88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98,
     99, 100],
    [116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 117, 118,
     119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]],
   [[144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 145, 146, 147, 148, 149, 150,
     151, 152, 153, 154, 155, 156],
    [172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 173, 174,
     175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]],
   [[200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 201],
    [217, 216, 215, 214, 213, 212, 211, 210, 209, 208, 207, 206, 205, 204, 203, 202, 218]],
   [[230, 229, 228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 231, 232, 233, 234, 235, 236,
     237, 238, 239, 240, 241, 242],
    [258, 257, 256, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 259, 260,
     261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274]],
   [[286, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275],
    [302, 301, 300, 299, 298, 297, 296, 295, 294, 293, 292, 291, 290, 289, 288, 287]]]

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
    int_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.arcs" 8 311 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 120 = true := by
  decide +kernel

theorem coverCtx_alphas_2 : alphasRange table.arcs coverCtx.alphas 240 63 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 120), (240, 63)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, coverCtx_alphas_2, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
