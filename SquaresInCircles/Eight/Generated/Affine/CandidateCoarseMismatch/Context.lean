module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: the fixed-point context of the affine table `CandidateCoarseMismatch`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/-- The margins added to the targets. -/
noncomputable def enhancement (i : Fin 7) : ℚ := (![15,13,18,12,15,23,6] i) / 10^6

theorem enhancement_nonneg : ∀ i, 0 ≤ enhancement i := by decide +kernel

/-- The table with the enhanced targets; the rows are checked against these. -/
noncomputable def enhancedMeta : AffineTableMeta :=
  {table with target := fun i => table.target i + enhancement i}

noncomputable def ctx : TableCtx :=
  ⟨100000000, 462,
    [int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 200 232 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 232 264 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 264 296 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 296 328 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 328 360 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 360 392 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 392 424 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 424 456 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 456 470 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars enhancedMeta = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange enhancedMeta.radius enhancedMeta.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange enhancedMeta.radius enhancedMeta.arcs ctx.boxes 120 120 = true := by
  decide +kernel

theorem ctx_boxes_2 :
    boxesRange enhancedMeta.radius enhancedMeta.arcs ctx.boxes 240 120 = true := by
  decide +kernel

theorem ctx_boxes_3 :
    boxesRange enhancedMeta.radius enhancedMeta.arcs ctx.boxes 360 102 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid enhancedMeta :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 120), (240, 120), (360, 102)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, ctx_boxes_2, ctx_boxes_3, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  [[[11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    [55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34,
     33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
     68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]],
   [[95, 94, 93, 92, 91, 90, 89, 88],
    [120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103,
     102, 101, 100, 99, 98, 97, 96]],
   [[132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 133, 134, 135, 136, 137, 138,
     139, 140, 141, 142, 143, 144],
    [176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159,
     158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 177, 178, 179, 180,
     181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198,
     199, 200, 201, 202, 203, 204, 205, 206, 207, 208]],
   [[220, 219, 218, 217, 216, 215, 214, 213, 212, 211, 210, 209, 221, 222, 223, 224, 225, 226,
     227, 228, 229, 230, 231, 232],
    [264, 263, 262, 261, 260, 259, 258, 257, 256, 255, 254, 253, 252, 251, 250, 249, 248, 247,
     246, 245, 244, 243, 242, 241, 240, 239, 238, 237, 236, 235, 234, 233, 265, 266, 267, 268,
     269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
     287, 288, 289, 290, 291, 292, 293, 294, 295, 296]],
   [[297, 298, 299, 300, 301, 302, 303, 304],
    [305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322,
     323, 324, 325, 326, 327, 328, 329]],
   [[341, 340, 339, 338, 337, 336, 335, 334, 333, 332, 331, 330, 342, 343, 344, 345, 346, 347,
     348, 349, 350, 351, 352, 353],
    [385, 384, 383, 382, 381, 380, 379, 378, 377, 376, 375, 374, 373, 372, 371, 370, 369, 368,
     367, 366, 365, 364, 363, 362, 361, 360, 359, 358, 357, 356, 355, 354, 386, 387, 388, 389,
     390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407,
     408, 409, 410, 411, 412, 413, 414, 415, 416, 417]],
   [[429, 428, 427, 426, 425, 424, 423, 422, 421, 420, 419, 418],
    [461, 460, 459, 458, 457, 456, 455, 454, 453, 452, 451, 450, 449, 448, 447, 446, 445, 444,
     443, 442, 441, 440, 439, 438, 437, 436, 435, 434, 433, 432, 431, 430]]]

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
    int_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.arcs" 8 470 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 120 = true := by
  decide +kernel

theorem coverCtx_alphas_2 : alphasRange table.arcs coverCtx.alphas 240 120 = true := by
  decide +kernel

theorem coverCtx_alphas_3 : alphasRange table.arcs coverCtx.alphas 360 102 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 120), (240, 120), (360, 102)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, coverCtx_alphas_2, coverCtx_alphas_3, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
