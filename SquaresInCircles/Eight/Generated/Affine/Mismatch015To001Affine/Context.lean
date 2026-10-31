module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.Certificates.Readers
public meta import SquaresInCircles.Eight.Certificates.Data

/-!
# Eight squares: the fixed-point context of the affine table `Mismatch015To001Affine`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 456,
    [int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 104 136 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 136 168 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 168 200 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 200 232 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 232 264 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 264 296 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 296 328 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 328 360 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 360 392 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 392 424 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 424 456 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 456 464 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 1 8 ↦
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
    boxesRange table.radius table.arcs ctx.boxes 360 96 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 120), (240, 120), (360, 96)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, ctx_boxes_2, ctx_boxes_3, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  affine_field% "../../../../../data/eight/affine/Mismatch015To001Affine.context.json" "states"

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den,
    affine_field% "../../../../../data/eight/affine/Mismatch015To001Affine.context.json" "gap",
    affine_field% "../../../../../data/eight/affine/Mismatch015To001Affine.context.json" "base",
    affine_field% "../../../../../data/eight/affine/Mismatch015To001Affine.context.json" "dLo",
    affine_field% "../../../../../data/eight/affine/Mismatch015To001Affine.context.json" "dHi",
    int_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.arcs" 8 464 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 120 = true := by
  decide +kernel

theorem coverCtx_alphas_2 : alphasRange table.arcs coverCtx.alphas 240 120 = true := by
  decide +kernel

theorem coverCtx_alphas_3 : alphasRange table.arcs coverCtx.alphas 360 96 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 120), (240, 120), (360, 96)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, coverCtx_alphas_2, coverCtx_alphas_3, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
