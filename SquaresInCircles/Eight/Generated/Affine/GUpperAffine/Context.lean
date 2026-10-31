module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.Certificates.Readers
public meta import SquaresInCircles.Eight.Certificates.Data

/-!
# Eight squares: the fixed-point context of the affine table `GUpperAffine`

The fixed-point data of the table, checked against its exact data (`Meta.lean`): the
arc boxes and the arctangent intervals of the arcs, in blocks, the scalars, the state
chains and the data of the angle coverage.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def ctx : TableCtx :=
  ⟨100000000, 122,
    [int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 8 40 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 40 72 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 72 104 ↦
        ArcBox.ofData,
     int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 104 130 ↦
        ArcBox.ofData],
    int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel

theorem ctx_boxes_0 :
    boxesRange table.radius table.arcs ctx.boxes 0 120 = true := by
  decide +kernel

theorem ctx_boxes_1 :
    boxesRange table.radius table.arcs ctx.boxes 120 2 = true := by
  decide +kernel

theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := [(0, 120), (120, 2)]) (by decide +kernel)
    (by simp only [AllBlocks]; exact
      ⟨ctx_boxes_0, ctx_boxes_1, trivial⟩)

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
  affine_field% "../../../../../data/eight/affine/GUpperAffine.context.json" "states"

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den,
    affine_field% "../../../../../data/eight/affine/GUpperAffine.context.json" "gap",
    affine_field% "../../../../../data/eight/affine/GUpperAffine.context.json" "base",
    affine_field% "../../../../../data/eight/affine/GUpperAffine.context.json" "dLo",
    affine_field% "../../../../../data/eight/affine/GUpperAffine.context.json" "dHi",
    int_rows% "../../../../../data/eight/affine/G_UPPER_AFFINE.arcs" 8 130 ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel

theorem coverCtx_alphas_0 : alphasRange table.arcs coverCtx.alphas 0 120 = true := by
  decide +kernel

theorem coverCtx_alphas_1 : alphasRange table.arcs coverCtx.alphas 120 2 = true := by
  decide +kernel

/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
    [(0, 120), (120, 2)] :=
  by simp only [AllBlocks]; exact
    ⟨coverCtx_alphas_0, coverCtx_alphas_1, trivial⟩

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
