module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the fixed-point context of the affine table `Mismatch026To01Affine`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000000000, 401,
    [int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 200 232 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 232 264 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 264 296 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 296 328 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 328 360 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 360 392 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 392 409 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange table.radius table.arcs ctx.boxes 120 120 = true := by
  decide +kernel

theorem ctx_boxes_2 :
    boxesRange table.radius table.arcs ctx.boxes 240 120 = true := by
  decide +kernel

theorem ctx_boxes_3 :
    boxesRange table.radius table.arcs ctx.boxes 360 41 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 120), (240, 120), (360, 41)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, ctx_boxes_2, ctx_boxes_3, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[0, 1, 2, 3, 4, 5, 6, 7],
    [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
     31, 32]],
   [[58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37,
     36, 35, 34, 33],
    [87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66,
     65, 64, 63, 62, 61, 60, 59]],
   [[99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 100, 101, 102, 103, 104, 105, 106, 107,
     108, 109, 110, 111],
    [144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127,
     126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 145, 146, 147,
     148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165,
     166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]],
   [[189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 190, 191, 192, 193, 194, 195,
     196, 197, 198, 199, 200, 201],
    [234, 233, 232, 231, 230, 229, 228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 218, 217,
     216, 215, 214, 213, 212, 211, 210, 209, 208, 207, 206, 205, 204, 203, 202, 235, 236, 237,
     238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255,
     256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267]],
   [[268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
     286, 287, 288, 289, 290, 291, 292, 293],
    [294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311,
     312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323]],
   [[331, 330, 329, 328, 327, 326, 325, 324],
    [356, 355, 354, 353, 352, 351, 350, 349, 348, 347, 346, 345, 344, 343, 342, 341, 340, 339,
     338, 337, 336, 335, 334, 333, 332]],
   [[368, 367, 366, 365, 364, 363, 362, 361, 360, 359, 358, 357],
    [400, 399, 398, 397, 396, 395, 394, 393, 392, 391, 390, 389, 388, 387, 386, 385, 384, 383,
     382, 381, 380, 379, 378, 377, 376, 375, 374, 373, 372, 371, 370, 369]]]

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den, ⟨760000000000000000000000, 1723185840707964601769912⟩,
    [⟨0, 0⟩, ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩, ⟨0, 0⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩,
     ⟨1570796326794896619000000, 1570796326794896619500000⟩],
    [-26000000000000000000000000000000000000, -70000000000000000000000000000000000000,
     -26000000000000000000000000000000000000, -26000000000000000000000000000000000000,
     -26000000000000000000000000000000000000, -26000000000000000000000000000000000000,
     -70000000000000000000000000000000000000],
    [26000000000000000000000000000000000000, 70000000000000000000000000000000000000,
     26000000000000000000000000000000000000, 26000000000000000000000000000000000000,
     26000000000000000000000000000000000000, 26000000000000000000000000000000000000,
     70000000000000000000000000000000000000],
    int_rows% "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.arcs" 8 409 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 120 = true := by
  decide +kernel

theorem coverCtx_alphas_2 : alphasRange table.arcs coverCtx.alphas 240 120 = true := by
  decide +kernel

theorem coverCtx_alphas_3 : alphasRange table.arcs coverCtx.alphas 360 41 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 120), (240, 120), (360, 41)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, coverCtx_alphas_2, coverCtx_alphas_3, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
