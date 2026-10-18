module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-! The fixed-point data of the table, checked against the exact data of `Meta`: the
arc boxes and the arctangent intervals of the arcs (in blocks), the scalars, the
state chains and the data of the angle coverage. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 335,
    [int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 200 232 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 232 264 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 264 296 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 296 328 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 328 343 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange table.radius table.arcs ctx.boxes 120 120 = true := by
  decide +kernel

theorem ctx_boxes_2 :
    boxesRange table.radius table.arcs ctx.boxes 240 95 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 120), (240, 95)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, ctx_boxes_2, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
     34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]],
   [[70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49,
     48, 47, 46, 45],
    [99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78,
     77, 76, 75, 74, 73, 72, 71]],
   [[100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111],
    [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
     130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]],
   [[156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145],
    [189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172,
     171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157]],
   [[190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207,
     208, 209, 210, 211, 212, 213, 214, 215],
    [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233,
     234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245]],
   [[257, 256, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246],
    [290, 289, 288, 287, 286, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273,
     272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258]],
   [[302, 301, 300, 299, 298, 297, 296, 295, 294, 293, 292, 291],
    [334, 333, 332, 331, 330, 329, 328, 327, 326, 325, 324, 323, 322, 321, 320, 319, 318, 317,
     316, 315, 314, 313, 312, 311, 310, 309, 308, 307, 306, 305, 304, 303]]]

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den, ⟨760000000000000000000000, 1723185840707964601769912⟩,
    [⟨0, 0⟩, ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩],
    [-10000000000000000000000000000000, -70000000000000000000000000000000,
     -10000000000000000000000000000000, -10000000000000000000000000000000,
     -10000000000000000000000000000000, -10000000000000000000000000000000,
     -70000000000000000000000000000000],
    [10000000000000000000000000000000, 70000000000000000000000000000000,
     10000000000000000000000000000000, 10000000000000000000000000000000,
     10000000000000000000000000000000, 10000000000000000000000000000000,
     70000000000000000000000000000000],
    int_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.arcs" 8 343 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 120 = true := by
  decide +kernel

theorem coverCtx_alphas_2 : alphasRange table.arcs coverCtx.alphas 240 95 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 120), (240, 95)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, coverCtx_alphas_2, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
