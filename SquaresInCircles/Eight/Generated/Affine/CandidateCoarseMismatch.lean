module

public meta import SquaresInCircles.Eight.AffineDataReader
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Meta
public import SquaresInCircles.Eight.Candidate.GeometricAffineCoverage

/-! The historical input contains 129,031 rows. Whole-domain core
separator exclusions remove 13,800 constructors from the active Lean payload.
Every retained domain keeps the original row semantics and closed coverage.
All decision proofs below are uncompiled and have not been executed. -/

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rows : List AffineTableRow :=
  affine_rows% "../../../../research/eight/CANDIDATE_COARSE_MISMATCH_HAND_DATA.json" rows 129031
    excluding_core_separators 115231

theorem complete_row_count : rows.length = 115231 := by rfl

theorem rows_valid : AffineCertificate.RowsValid meta rows := by decide

theorem all_row_claims : ∀ r ∈ rows, r.Claim meta :=
  AffineCertificate.row_claims rows_valid

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta :=
  AffineCertificate.rows_structural rows_valid

def cover : AffineCover := AffineCertificate.cover meta rows

theorem cover_numeric : Candidate.GeometricAffine.NumericValid cover meta rows := by decide

theorem word_matches : ∀ i, (meta.word i:ℝ)=(Candidate.word i:ℝ) := by
  intro i; fin_cases i <;> norm_num [meta,Candidate.word]

noncomputable def charged_bound (C : BoundaryCycle (meta.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (meta.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (meta.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (meta.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈meta.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (meta.target i:ℝ)) :=
  Candidate.GeometricAffine.chargedBound cover_numeric all_row_claims C F β
    word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
