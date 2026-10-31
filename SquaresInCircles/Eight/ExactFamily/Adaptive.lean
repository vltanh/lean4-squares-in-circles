module

public import SquaresInCircles.Eight.ExactFamily.Cuts
public import SquaresInCircles.Eight.ExactFamily.Stationary

/-!
# Eight squares: the adaptive chain at every tilt

For each half-angle tangent `z` of the tilt in `tiltBox = [1/20, 81/1000]`, the adaptive chain
`adaptiveData z` is the chain at the squared radius `qStar` with the tilt `z` and the position
`adaptiveY z` at which the derivative of the defect in the position vanishes. That position is a
zero given by the intermediate value theorem. Circle-coordinate comparisons give opposite
signs at the extreme corners, and decrease in tilt (`familyY_antitone_z`) extends them to the
whole position faces (`adaptive_endpoint_signs`, `adaptive_position_exists`). Strict increase
in position gives uniqueness. Comparison with the known stationary root bounds the endpoint
positions (`adaptive_position_from_sharp`), without generated root brackets.
The mixed derivative is no smaller than `-13`, so the position increases at speed at most
`13/6` (`root_position_motion`). Height
loses at most `0.7` per unit of position and gains at least `1.8` per unit of tilt; it therefore
increases along the adaptive family (`root_height_slope`, `adaptive_height_monotone`).
The position moves at least `2/3` as fast as the tilt (`root_position_lower`); the margin
multiplying the HE contact in reserve 5 gains at least `0.91` per unit of position and loses at
most `0.6` per unit of tilt. This margin also increases (`adaptive_margin_monotone`), and reserve
0 is larger than reserve 5 (`margin_owner_bounds`).
The defect of the adaptive chain is at least `(z - z*)²/8` (`adaptive_curvature`).
`Cuts.lean` supplies the geometric cut estimates; `AdaptiveBounds.lean` applies them using
circle estimates and the root comparison.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated

/-- Circle comparisons give opposite signs at the two extreme corners of the pose box. -/
theorem extreme_corner_signs {q : ℝ} (hq : q ∈ radiusBox) :
    familyY q (-(937/1000),1/20) < 0 ∧ 0 < familyY q (-(179/200),81/1000) := by
  have hlo : (-(937/1000:ℝ),1/20) ∈ poseBox := by norm_num [poseBox,tiltBox]
  have hhi : (-(179/200:ℝ),81/1000) ∈ poseBox := by norm_num [poseBox,tiltBox]
  have hq' : 3.9155 ≤ q ∧ q ≤ 3.9156 := by constructor <;> linarith only [hq.1,hq.2]
  constructor
  · have hd := radical_isChain (local_mem hq hlo)
    rw [familyY_radical hd]
    exact Coordinates.lower_corner_position hd hq' (by norm_num [radicalCoordinates]) rfl
  · have hd := radical_isChain (local_mem hq hhi)
    rw [familyY_radical hd]
    exact Coordinates.upper_corner_position hd hq' (by norm_num [radicalCoordinates]) rfl

/-- Decrease in tilt extends the corner signs along both position faces. -/
theorem adaptive_endpoint_signs {q z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox) :
    familyY q (-(937/1000),z) < 0 ∧ 0 < familyY q (-(179/200),z) := by
  obtain ⟨hlo,hhi⟩ := extreme_corner_signs hq
  have hzlo : (1/20:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  have hzhi : (81/1000:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  exact ⟨((familyY_antitone_z hq (by norm_num)) hzlo hz hz.1).trans_lt hlo,
    hhi.trans_le ((familyY_antitone_z hq (by norm_num)) hz hzhi hz.2)⟩

theorem adaptive_position_exists {z : ℝ} (hz : z ∈ tiltBox) :
    ∃ y ∈ Icc (-(937/1000)) (-(179/200)), familyY qStar (y,z)=0 := by
  obtain ⟨hlo,hhi⟩ := adaptive_endpoint_signs qStar_mem hz
  exact intermediate_value_Icc (by norm_num) (familyY_continuous_y qStar_mem hz) ⟨hlo.le,hhi.le⟩

def adaptiveY (z : ℝ) (hz : z ∈ tiltBox) : ℝ := Classical.choose (adaptive_position_exists hz)
def adaptiveData (z : ℝ) (hz : z ∈ tiltBox) : Coordinates :=
  radicalCoordinates qStar (adaptiveY z hz) z

theorem adaptiveY_mem {z : ℝ} (hz : z ∈ tiltBox) :
    adaptiveY z hz ∈ Icc (-(937/1000)) (-(179/200)) :=
  (Classical.choose_spec (adaptive_position_exists hz)).1

theorem adaptiveY_zero {z : ℝ} (hz : z ∈ tiltBox) :
    familyY qStar (adaptiveY z hz,z)=0 :=
  (Classical.choose_spec (adaptive_position_exists hz)).2

/-- The last-corner height is increasing along the adaptive family. -/
theorem adaptive_height_monotone {z₀ z₁ : ℝ}
    (h₀ : z₀ ∈ tiltBox) (h₁ : z₁ ∈ tiltBox) (hz : z₀ ≤ z₁) :
    (adaptiveData z₀ h₀).h₂ ≤ (adaptiveData z₁ h₁).h₂ := by
  have h := root_height_slope qStar_mem ⟨adaptiveY_mem h₀,h₀⟩ ⟨adaptiveY_mem h₁,h₁⟩
    hz (adaptiveY_zero h₀) (adaptiveY_zero h₁)
  change (17/60)*(z₁-z₀) ≤ (adaptiveData z₁ h₁).h₂-(adaptiveData z₀ h₀).h₂ at h
  linarith only [h,hz]

/-- The reserve margin increases along the adaptive family. -/
theorem adaptive_margin_monotone {z₀ z₁ : ℝ}
    (h₀ : z₀ ∈ tiltBox) (h₁ : z₁ ∈ tiltBox) (hz : z₀ ≤ z₁) :
    familyMargin qStar (adaptiveY z₀ h₀,z₀) ≤ familyMargin qStar (adaptiveY z₁ h₁,z₁) := by
  have h := root_margin_slope qStar_mem ⟨adaptiveY_mem h₀,h₀⟩ ⟨adaptiveY_mem h₁,h₁⟩
    hz (adaptiveY_zero h₀) (adaptiveY_zero h₁)
  change (1/150)*(z₁-z₀) ≤ familyMargin qStar (adaptiveY z₁ h₁,z₁)-
    familyMargin qStar (adaptiveY z₀ h₀,z₀) at h
  linarith only [h,hz]

/-- Compare any position root with the stationary root using the lower root-motion bound. -/
theorem adaptive_position_from_sharp {z : ℝ} (hz : z ∈ tiltBox) :
    (z ≤ sharpPose.2 → adaptiveY z hz ≤ sharpPose.1-(2/3)*(sharpPose.2-z)) ∧
    (sharpPose.2 ≤ z → sharpPose.1+(2/3)*(z-sharpPose.2) ≤ adaptiveY z hz) := by
  have hp : sharpPose ∈ poseBox := minimizingPose_mem qStar
  constructor
  · intro h
    have hs := root_position_lower qStar_mem ⟨adaptiveY_mem hz,hz⟩ hp h
      (adaptiveY_zero hz) sharpPose_stationary.1
    change 6*(sharpPose.2-z) ≤ 9*(sharpPose.1-adaptiveY z hz) at hs
    linarith only [hs]
  · intro h
    have hs := root_position_lower qStar_mem hp ⟨adaptiveY_mem hz,hz⟩ h
      sharpPose_stationary.1 (adaptiveY_zero hz)
    change 6*(z-sharpPose.2) ≤ 9*(adaptiveY z hz-sharpPose.1) at hs
    linarith only [hs]

theorem adaptive_local_mem {z : ℝ} (hz : z ∈ tiltBox) :
    localBox.Mem ![qStar,adaptiveY z hz,z] :=
  local_mem qStar_mem (⟨adaptiveY_mem hz,hz⟩ : (adaptiveY z hz,z) ∈ poseBox)

theorem adaptive_chain {z : ℝ} (hz : z ∈ tiltBox) : (adaptiveData z hz).IsChain :=
  radical_isChain (adaptive_local_mem hz)

theorem adaptive_weightDomain {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).WeightDomain := radical_weightDomain (adaptive_local_mem hz)

theorem adaptive_position_stationary {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).positionDerivative=0 :=
  (familyY_radical (adaptive_chain hz)).symm.trans (adaptiveY_zero hz)

theorem adaptive_curvature {z : ℝ} (hz : z ∈ tiltBox) :
    (z-sharpData.z)^2/8 ≤ (adaptiveData z hz).defect := by
  have h := family_strong_convex (a:=sharpPose) (b:=(adaptiveY z hz,z)) qStar_mem
    (minimizingPose_mem qStar) ⟨adaptiveY_mem hz,hz⟩
  rw [sharpPose_value,sharpPose_stationary.1,sharpPose_stationary.2] at h
  rw [familyValue_radical] at h
  dsimp [adaptiveData,sharpData,radicalCoordinates] at *
  linarith only [sq_nonneg (adaptiveY z hz-sharpPose.1), hz, h]

end SquaresInCircles.Eight.ExactFamily
