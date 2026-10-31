module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Meta
public import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.Certificates.Readers
public meta import SquaresInCircles.Eight.Certificates.Data

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
  affine_field% "../../../../../data/eight/affine/CandidateCoarseMismatch.context.json" "states"

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den,
    affine_field% "../../../../../data/eight/affine/CandidateCoarseMismatch.context.json" "gap",
    affine_field% "../../../../../data/eight/affine/CandidateCoarseMismatch.context.json" "base",
    affine_field% "../../../../../data/eight/affine/CandidateCoarseMismatch.context.json" "dLo",
    affine_field% "../../../../../data/eight/affine/CandidateCoarseMismatch.context.json" "dHi",
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
