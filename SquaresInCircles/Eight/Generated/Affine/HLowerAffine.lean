module

public meta import SquaresInCircles.Eight.AffineDataReader
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Meta
public import SquaresInCircles.Eight.Arithmetic.AffineCertificate

/-! One retained data table; shared row semantics and complete closed coverage.
All decision proofs below are uncompiled and have not been executed. -/

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rows : List AffineTableRow :=
  affine_rows% "../../../../research/eight/H_LOWER_AFFINE_HAND_DATA.json" rows 48050

theorem complete_row_count : rows.length = 48050 := by rfl

theorem rows_valid : AffineCertificate.RowsValid meta rows := by decide

theorem all_row_claims : ∀ r ∈ rows, r.Claim meta :=
  AffineCertificate.row_claims rows_valid

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta :=
  AffineCertificate.rows_structural rows_valid

def cover : AffineCover := AffineCertificate.cover meta rows

theorem cover_numeric : cover.NumericValid meta rows := by decide

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
  cover.chargedBound cover_numeric all_row_claims C F β word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
