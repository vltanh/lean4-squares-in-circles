module
public import SquaresInCircles.Six.Analytic.WestCoreBounds.Scalar
public import SquaresInCircles.Six.Analytic.AxialConeSupport

@[expose] public section

/-!
# The two three-edge core profiles are genuine support obstructions

W lies in a proved axial force cone because its actual gap is at least one.
For the large-tilt stress D is also axial; for the low-diagonal stress its
universal vertex support uses one exact rational square-root upper bound.
The central y sign is retained explicitly. No S inequality is used.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCoreBounds
open Normalization

def diagonalUpper (large : Bool) : ℝ :=
  if large then CandidateWestTail.rhoBound*delta large
  else CandidateWestTail.radiusBound*(61327/25000)-(delta large+1)/2

def forceX (large : Bool) (v d : ℝ) : ℝ := beta large*Real.cos v+delta large*Real.cos d
def forceY (large : Bool) (v d : ℝ) : ℝ := -beta large*Real.sin v+delta large*Real.sin d

def centerUpper (large upper : Bool) (v d : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*forceX large v d+face upper*forceY large v d

lemma west_support (large : Bool) {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1 ≤ q ∧ q ≤ Real.pi/2) :
    (beta large+Real.sin q)*a-Real.cos q*b ≤
      CandidateWestTail.rhoBound*(beta large+Real.sin q) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hq.1])
    (by linarith [hq.2,Real.pi_pos])
  have hcq := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 1)
    (show q ≤ Real.pi by linarith [hq.2,Real.pi_pos]) hq.1
  have ht := Seven.cos_upper_four (x := (1:ℝ)) (by norm_num)
  have hcos : Real.cos q ≤ 13/24 := by nlinarith only [hm,ht]
  have hU : 0 ≤ beta large+Real.sin q := by cases large <;> dsimp [beta] <;> linarith
  have hV : |-Real.cos q| ≤ (31/100)*(beta large+Real.sin q) := by
    rw [abs_neg,abs_of_nonneg hcq]
    cases large <;> dsimp [beta] <;> linarith
  have h := axial_cone_support hc hU hV
  have hR := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 hU
  nlinarith only [h,hR]

lemma diagonal_support (large : Bool) {a b : ℝ} (hc : ContainedChart a |b|) :
    delta large*a+b ≤ diagonalUpper large := by
  cases large
  · have h := CandidateWestTail.local_vertex_support hc (delta false) 1
    have hroot : Real.sqrt ((delta false)^2+1) ≤ 61327/25000 := by
      have h := Real.sqrt_le_sqrt
        (show (delta false)^2+1 ≤ ((61327:ℝ)/25000)^2 by norm_num [delta])
      simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 61327/25000)] using h
    have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot (Real.sqrt_nonneg _)
      (by norm_num [CandidateWestTail.radiusBound])
    norm_num [delta] at h
    dsimp [diagonalUpper,delta]
    linarith
  · have h := axial_cone_support hc (U := delta true) (V := 1)
      (by norm_num [delta]) (by norm_num [delta])
    have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1
      (show 0 ≤ delta true by norm_num [delta])
    dsimp [diagonalUpper]
    nlinarith only [h,hm]

/-- Every application obtains a real supporting face, rather than assuming its sign. -/
lemma center_support (large : Bool) {v d cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ Real.pi/2) (hd : 0 ≤ d ∧ d ≤ Real.pi/2)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper) :
    ∃ upper : Bool, forceX large v d*cx+forceY large v d*cy ≤ centerUpper large upper v d := by
  have hcv := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hv.1,Real.pi_pos],hv.2⟩
  have hcd := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hd.1,Real.pi_pos],hd.2⟩
  have hX : 0 ≤ forceX large v d := by
    cases large <;> dsimp [forceX,beta,delta] <;> positivity
  have hx' := mul_le_mul_of_nonneg_left hx hX
  by_cases hY : 0 ≤ forceY large v d
  · refine ⟨true,?_⟩
    have hy' := mul_le_mul_of_nonneg_left hy.2 hY
    dsimp [centerUpper,face,CandidateWestTail.coreUpper] at *
    nlinarith only [hx',hy']
  · refine ⟨false,?_⟩
    have hy' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hY) hy.1
    dsimp [centerUpper,face]
    nlinarith only [hx',hy']

/-- The same actual CW, CD and D-sourced WD inequalities supply either profile. -/
theorem value_nonpositive (large : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ Real.pi/2) (hd : 0 ≤ d ∧ d ≤ Real.pi/2)
    (hq : 1 ≤ v+d ∧ v+d ≤ Real.pi/2)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hWD : 1/2+angularWidth (v+d) ≤ aw*Real.sin (v+d)-bw*Real.cos (v+d)+bd) :
    ∃ upper : Bool, value large upper v d ≤ 0 := by
  have hsum : beta large*(1/2+angularWidth v)+delta large*(1/2+angularWidth d)+
      (1/2+angularWidth (v+d)) ≤
      (beta large+Real.sin (v+d))*aw-Real.cos (v+d)*bw+delta large*ad+bd+
      forceX large v d*cx+forceY large v d*cy := by
    cases large <;> dsimp [beta,delta,forceX,forceY] <;>
      first
      | linear_combination (207/100)*hCW+(56/25)*hCD+hWD
      | linear_combination (17/3)*hCW+(14/3)*hCD+hWD
  have hw := west_support large hW hq
  have hdiag := diagonal_support large hD
  obtain ⟨upper,hcenter⟩ := center_support large hv hd hx hy
  have width_formula {x : ℝ} (h : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [h.1,Real.pi_pos],h.2⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi h.1 (by linarith [h.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]
  rw [width_formula hv,width_formula hd,
    width_formula ⟨by linarith [hq.1],hq.2⟩] at hsum
  refine ⟨upper,?_⟩
  cases large <;> cases upper <;>
    dsimp [value,profile,diagonalUpper,centerUpper,forceX,forceY,beta,delta,face,
      constantTerm,A,B,CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,
      CandidateWestTail.coreUpper] at * <;>
    nlinarith only [hsum,hw,hdiag,hcenter]

end SquaresInCircles.Six.Analytic.WestCoreBounds
