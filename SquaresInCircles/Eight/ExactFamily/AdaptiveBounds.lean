module

public import SquaresInCircles.Eight.ExactFamily.Adaptive

/-!
# Eight squares: bounds along the adaptive chain

Height and the reserve margin increase along the position roots. Circle equations bound
the endpoint heights, and coarse coordinates bound the margin on the lower-tilt face.
The shared unnormalized cut decreases with position and has bounded tilt curvature. Its two midpoint tangent parabolas control the entire rectangle.
Force balance and these geometric estimates give all nine owner reserves.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated Coordinates FiveCornerGeometry
private theorem midpoint_slope_bound {q y b : ℝ}
    (h : |rawCutAngle q (halfAngleCos (131/2000)) (halfAngleSin (131/2000)) (-y)| ≤ b) :
    |familyRawCutZ q (y,131/2000)| ≤ 2*b := by
  have hg : |(2/(1+(131/2000:ℝ)^2))| ≤ 2 := by norm_num
  rw [familyRawCutZ,abs_mul]
  exact mul_le_mul hg h (abs_nonneg _) (by norm_num)

/-- Circle equations supply both tangent parabolas, without interval certificates. -/
theorem raw_cut_bound {q : ℝ} (hq : q ∈ radiusBox) {p : Pose} (hp : p ∈ poseBox) :
    0.412 ≤ familyRawCut q p ∧ familyRawCut q p ≤ 0.44 := by
  have hq' : 3.9155 ≤ q ∧ q ≤ 3.9156 := by constructor <;> linarith only [hq.1,hq.2]
  have hl := left_midpoint_cut (d:=radicalCoordinates q (-(937/1000)) (131/2000))
    (radical_isChain (local_mem (p:=( -(937/1000),131/2000)) hq (by norm_num [poseBox,tiltBox]))) hq'
    (by norm_num [radicalCoordinates]) rfl
  have hh := right_midpoint_cut (d:=radicalCoordinates q (-(179/200)) (131/2000))
    (radical_isChain (local_mem (p:=( -(179/200),131/2000)) hq (by norm_num [poseBox,tiltBox]))) hq'
    (by norm_num [radicalCoordinates]) rfl
  refine familyRawCut_bounds_of_midpoint hq hh.1 ?_ hl.1 ?_ hp
  · convert midpoint_slope_bound hh.2 using 1 <;> norm_num [radicalCoordinates]
  · convert midpoint_slope_bound hl.2 using 1 <;> norm_num [radicalCoordinates]

/-- Circle equations bound the endpoint heights; monotonicity extends them to the family. -/
theorem adaptive_hTwo_bound {z : ℝ} (hz : z ∈ tiltBox) :
    -29/20 ≤ (adaptiveData z hz).h₂ ∧ (adaptiveData z hz).h₂ ≤ -7/5 := by
  have hzlo : (1/20:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  have hzhi : (81/1000:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  have hylo := adaptiveY_mem hzlo
  have hyhi := adaptiveY_mem hzhi
  have hplo := (adaptive_position_from_sharp hzlo).1 (by linarith only [sharpPose_bounds.2.1])
  have hphi := (adaptive_position_from_sharp hzhi).2 (by linarith only [sharpPose_bounds.2.2])
  have hq : 3.9155 ≤ qStar ∧ qStar ≤ 3.9156 := by
    constructor <;> linarith only [qStar_mem.1,qStar_mem.2]
  have hw {t : ℝ} (ht : t ∈ tiltBox) :
      -1.9049 ≤ (adaptiveData t ht).x₄ ∧ (adaptiveData t ht).x₄ ≤ -1.8974 := by
    have hy := adaptiveY_mem ht
    obtain ⟨_,_,_,_,_,_,hwl,hwu,_⟩ := radical_coordinate_bounds
      (y:=adaptiveY t ht) qStar_mem ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ ht
    dsimp only [adaptiveData]
    constructor <;> linarith only [hwl,hwu]
  have hlo := lower_tilt_height (adaptive_chain hzlo) hq
    (show -0.937 ≤ (adaptiveData (1/20) hzlo).y ∧ (adaptiveData (1/20) hzlo).y ≤ -0.928 by
      change -0.937 ≤ adaptiveY (1/20) hzlo ∧ adaptiveY (1/20) hzlo ≤ -0.928
      constructor <;> linarith only [hylo.1,hplo,sharpPose_bounds.1.2,sharpPose_bounds.2.1])
    (hw hzlo) rfl
  have hhi := upper_tilt_height (adaptive_chain hzhi) hq
    (show -0.908 ≤ (adaptiveData (81/1000) hzhi).y ∧ (adaptiveData (81/1000) hzhi).y ≤ -0.895 by
      change -0.908 ≤ adaptiveY (81/1000) hzhi ∧ adaptiveY (81/1000) hzhi ≤ -0.895
      constructor <;> linarith only [hyhi.2,hphi,sharpPose_bounds.1.1,sharpPose_bounds.2.2])
    (hw hzhi) rfl
  exact ⟨hlo.1.trans (adaptive_height_monotone hzlo hz hz.1),
    (adaptive_height_monotone hz hzhi hz.2).trans hhi.2⟩

/-- The margin increases from its positive value at the lower tilt endpoint. -/
private theorem adaptive_margin_bound {z : ℝ} (hz : z ∈ tiltBox) :
    1/40 ≤ familyMargin qStar (adaptiveY z hz,z) := by
  have hz₀ : (1/20:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  have hb := familyMargin_lower_tilt qStar_mem (adaptiveY_mem hz₀)
  exact hb.trans (adaptive_margin_monotone hz₀ hz hz.1)

/-- The adaptive chain satisfies the common coordinate bounds used by the contact estimates. -/
private theorem adaptive_weight_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    WeightBounds (adaptiveData z hz) := by
  change WeightBounds (radicalCoordinates qStar (adaptiveY z hz) z)
  have hy := adaptiveY_mem hz
  obtain ⟨hrl,hru,hUl,hUu,hYl,hYu,hwl,hwu,hhl,hhu,_⟩ :=
    radical_coordinate_bounds (q:=qStar) (y:=adaptiveY z hz) (z:=z) qStar_mem
      (by constructor <;> linarith only [hy.1,hy.2]) hz
  have h₂ := adaptive_hTwo_bound hz
  change -29/20 ≤ (radicalCoordinates qStar (adaptiveY z hz) z).h₂ ∧
    (radicalCoordinates qStar (adaptiveY z hz) z).h₂ ≤ -7/5 at h₂
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hz⟩
  · change -0.937 ≤ adaptiveY z hz ∧ adaptiveY z hz ≤ -0.895
    constructor <;> linarith only [hy.1,hy.2]
  · constructor <;> linarith only [hrl,hru]
  · constructor <;> linarith only [hUl,hUu]
  · constructor <;> linarith only [hYl,hYu]
  · constructor <;> linarith only [hwl,hwu]
  · constructor <;> linarith only [hhl,hhu]
  · constructor <;> linarith only [h₂.1,h₂.2]

private theorem adaptive_contact_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    ContactBounds (adaptiveData z hz) :=
  (adaptive_weightDomain hz).contact_bounds (adaptive_position_stationary hz) (adaptive_weight_bounds hz)

theorem adaptive_owner_bounds {z : ℝ} (hz : z ∈ tiltBox) (j : Fin 9) :
    56793/5000000 ≤ (adaptiveData z hz).ownerReserve j := by
  have hw := adaptive_weightDomain hz
  have hy := adaptive_position_stationary hz
  have hb := adaptive_weight_bounds hz
  have hc := adaptive_contact_bounds hz
  have hg := geometric_owner_bounds hw hy hb hc
  have hmargin := adaptive_margin_bound hz
  rw [familyMargin_coordinates] at hmargin
  have hm := margin_owner_bounds hw hy hb hc hmargin
  have hρ : (56793/5000000:ℝ) ≤ 1/80 := by norm_num
  have hcut := raw_cut_bound qStar_mem (⟨adaptiveY_mem hz,hz⟩ : (adaptiveY z hz,z) ∈ poseBox)
  rw [familyRawCut_coordinates] at hcut
  have hn := cut_owner_bounds hw hb hc hcut
  have hρ' : (56793/5000000:ℝ) ≤ 3/250 := by norm_num
  fin_cases j
  · exact hρ.trans hm.1
  · exact hρ.trans hg.1
  · exact hρ.trans hg.2.1
  · exact hρ.trans hg.2.2.1
  · exact hρ.trans hg.2.2.2.1
  · exact hρ.trans hm.2
  · exact hρ.trans hg.2.2.2.2
  · exact hρ'.trans hn.1
  · exact hρ'.trans hn.2

/-- Force balance gives `5/6`, which is stronger than the terminal's contact-weight bound. -/
theorem adaptive_edge_weight_bound {z : ℝ} (hz : z ∈ tiltBox) (j : Fin 7) :
    (adaptiveData z hz).lam j ≤ 4209/5000 := by
  have h := (adaptive_contact_bounds hz).upper j
  linarith only [h]

end SquaresInCircles.Eight.ExactFamily
