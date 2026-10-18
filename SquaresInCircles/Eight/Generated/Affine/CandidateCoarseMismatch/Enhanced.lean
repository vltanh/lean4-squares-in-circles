module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch

/-! The same rows and coverage for the enhanced targets: the rows were checked
against them, and the coverage walk does not involve the targets. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table, with the enhanced targets. -/
noncomputable def enhancedRows : List AffineTableRow := data.map (·.toTableRow enhancedMeta ctx.den)

theorem enhanced_claims : ∀ r ∈ enhancedRows, r.Claim enhancedMeta := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

noncomputable def enhancedCover : AffineCover := ⟨atanEnds enhancedMeta, chainsOf stateData⟩

theorem enhanced_endpoints : enhancedCover.EndpointsValid enhancedMeta :=
  endpointsValid_atanEnds enhancedMeta _

theorem enhanced_states : enhancedCover.states.NumericValid enhancedMeta := by decide +kernel

theorem enhanced_coverCtx_valid : coverCtx.Valid enhancedCover enhancedMeta ∧
    coverCtx.alphas.length = enhancedMeta.arcs.length :=
  CoverCtx.valid_of (by decide +kernel) (by decide +kernel) coverCtx_alphas

theorem enhanced_angles : enhancedCover.AngleCovers enhancedMeta enhancedRows :=
  coverBlocks_sound enhanced_coverCtx_valid.1 enhanced_coverCtx_valid.2 (by decide +kernel)
    (AllBlocks.imp (fun a n ⟨c, o, h⟩ =>
      ⟨c, o, (coverBlock_congr rfl rfl rfl a n c o chunks).trans h⟩) cover_blocks)

noncomputable def enhanced_charged_bound (C : BoundaryCycle (table.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (enhancedMeta.target i:ℝ)) :=
  AffineCover.chargedBoundOf enhanced_endpoints enhanced_states enhanced_angles enhanced_claims
    C F β word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
