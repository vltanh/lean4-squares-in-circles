module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch

/-! The enhanced margin reuses the same rows and coverage; it does not copy
another prepared certificate corpus. The numeric checks remain uncompiled. -/

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def enhancement (i : Fin 7) : ℚ := (![15,13,18,12,15,23,6] i) / 10^6

def enhancedMeta : AffineTableMeta :=
  {meta with target := fun i => meta.target i + enhancement i}

def enhanceRow (r : AffineTableRow) : AffineTableRow :=
  {r with lowerTarget := r.lowerTarget + enhancement r.edge}

def enhancedRows : List AffineTableRow := rows.map enhanceRow

theorem enhanced_rows_valid : AffineCertificate.RowsValid enhancedMeta enhancedRows := by decide

theorem enhanced_claims : ∀ r ∈ enhancedRows, r.Claim enhancedMeta :=
  AffineCertificate.row_claims enhanced_rows_valid

theorem enhanced_cover_numeric :
    Candidate.GeometricCoreCoverage.NumericValid cover enhancedMeta enhancedRows := by decide

noncomputable def enhanced_charged_bound (C : BoundaryCycle (meta.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (meta.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (meta.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (meta.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈meta.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (enhancedMeta.target i:ℝ)) :=
  Candidate.GeometricCoreCoverage.chargedBound enhanced_cover_numeric enhanced_claims C F β
    word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
