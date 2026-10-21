module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperSurface

/-!
# A whole-domain negative direction for the upper contact surface

The second derivative along `(x+t,B-t)` is less than `-.7` on
every physical contact with `0≤x≤.108`.  All estimates are obtained
from the shifted circle and the complete closed intervals.  In
particular, the mixed derivative is not discarded.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperCurvature
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned FrameHighLowUpperSurface

theorem low_bounds {B : ℝ} (hB : B∈Icc 0 b0) :
    (13/50:ℝ)<slope B ∧ slope B<8/25 ∧ 0<slopeD B ∧ slopeD B<59/100 := by
  have hBlow : B∈Icc 0 b1 := ⟨hB.1,hB.2.trans b0_low.2⟩
  have he := low_extended hBlow
  have hr := extended_slope_monotone he (low_extended b0_low) hB.2
  have hA := extended_A_antitone he (low_extended b0_low) hB.2
  have hp := extended_shift_pos he
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/25)
    (show (47/25:ℝ)≤A B+1/2 by linarith [b0_shift_bounds.1]) 3
  refine ⟨(slope_bounds hBlow).1,by linarith [b0_slope_bounds.2],slopeD_positive he,?_⟩
  dsimp [slopeD]
  apply (div_lt_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem marker_bounds {z : ℝ} (hz : z∈Icc c0 1) :
    (480179/500000:ℝ)≤Gd z ∧ Gd z<41/40 ∧ 0<Gdd z ∧ Gdd z<357/500 := by
  have hsource : z∈sourceDomain := ⟨hz.1,by linarith [hz.2,a2_bounds.1]⟩
  have he := source_extended hsource
  have hOne : (1:ℝ)∈extendedDomain := by constructor <;> norm_num [extendedDomain]
  have hmono := Gd_monotone he hOne hz.2
  have hA := extended_A_antitone he hOne hz.2
  have hzero := FrameHighLowAxialGeometry.upper_chart
    (show (0:ℝ)∈FrameHighLowAxialGeometry.upperDomain by constructor <;> norm_num)
  have hmarker := FrameHighLowAxialGeometry.upper_marker_bounds
    (show (0:ℝ)∈FrameHighLowAxialGeometry.upperDomain by constructor <;> norm_num)
  simp only [FrameHighLowAxialGeometry.Z_zero] at hzero hmarker
  have hp := extended_shift_pos he
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤129/100)
    (show (129/100:ℝ)≤A z+1/2 by linarith [hzero.2.2.1]) 3
  refine ⟨source_Gd_lower hsource,by linarith [hmarker.2.1],?_,?_⟩
  · exact mul_pos (by norm_num [FrameHighArc.v]) (slopeD_positive he)
  · rw [Gdd,slopeD,← mul_div_assoc]
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [FrameHighArc.v,Q0] at *
    nlinarith

theorem contact_P {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0) :
    (879/1000:ℝ)<P x B ∧ P x B<969/1000 := by
  have ht := trig_bounds hx
  have hBlow : B∈Icc 0 b1 := ⟨hB.1,hB.2.trans b0_low.2⟩
  have hA := extended_A_antitone (low_extended hBlow) (low_extended b0_low) hB.2
  have hAu := (A_low_bounds hBlow).2
  have hlow := mul_le_mul
    (show (177/200:ℝ)≤A B-1/2 by linarith [b0_shift_bounds.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤497/500) (by linarith [b0_shift_bounds.1] : 0≤A B-1/2)
  have hnonneg := mul_nonneg (show 0≤1/2-B by linarith [hB.2,b0_bounds.2]) ht.1
  have hupperA := mul_le_mul_of_nonneg_left ht.2.2.2
    (show 0≤A B-1/2 by linarith [b0_shift_bounds.1])
  have hupperB := mul_le_mul
    (show 1/2-B≤1/2 by linarith [hB.1]) ht.2.1 ht.1 (by norm_num : (0:ℝ)≤1/2)
  dsimp [P]
  constructor <;> nlinarith [a0_precise.2]

theorem contact_D {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0) :
    (959/1000:ℝ)<D x B ∧ D x B≤1 := by
  have ht := trig_bounds hx
  have hr := low_bounds hB
  have hprod := mul_le_mul hr.2.1.le ht.2.1 ht.1 (by norm_num : (0:ℝ)≤8/25)
  have hnonneg := mul_nonneg (by linarith [hr.1] : 0≤slope B) ht.1
  dsimp [D,FrameHighLowContactSurface.D]
  constructor <;> nlinarith

theorem contact_E {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0) :
    (129/500:ℝ)<E x B := by
  have ht := trig_bounds hx
  have hr := low_bounds hB
  have hprod := mul_le_mul hr.1.le ht.2.2.1.le
    (by norm_num : (0:ℝ)≤497/500) (by linarith [hr.1] : 0≤slope B)
  dsimp [E]
  nlinarith

theorem line_curvature {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0)
    (hz : c0≤height x B) : lineDD x B<-(7/10:ℝ) := by
  have hBlow : B∈Icc 0 b1 := ⟨hB.1,hB.2.trans b0_low.2⟩
  have hcoord := (physical_contact_bounds hx hBlow hz).2
  have hmarker := marker_bounds hcoord
  have hp := contact_P hx hB
  have hd := contact_D hx hB
  have he := contact_E hx hB
  have ht := trig_bounds hx
  have hr := low_bounds hB
  have hdiff : -(13/100:ℝ)≤D x B-P x B ∧ D x B-P x B≤13/100 := by
    constructor <;> linarith
  have hsquare : (D x B-P x B)^2≤(13/100:ℝ)^2 := by
    nlinarith [mul_nonneg (show 0≤13/100-(D x B-P x B) by linarith [hdiff.2])
      (show 0≤13/100+(D x B-P x B) by linarith [hdiff.1])]
  have hquadratic := mul_le_mul hmarker.2.2.2.le hsquare (sq_nonneg _)
    (by norm_num : (0:ℝ)≤357/500)
  have hrproduct := mul_le_mul hr.2.2.2.le ht.2.1 ht.1 (by norm_num : (0:ℝ)≤59/100)
  have hbracket : 1/2-height x B+slopeD B*Real.sin x-2*E x B≤-(17/20:ℝ) := by
    linarith [hcoord.1,c0_bounds.1]
  have hg0 : 0≤Gd (height x B) := by linarith [hmarker.1]
  have hwork := mul_le_mul_of_nonneg_left hbracket hg0
  have hwork0 := mul_le_mul_of_nonpos_right hmarker.1 (by norm_num : -(17/20:ℝ)≤0)
  have hlast : 0≤FrameLowArc.u*slopeD B :=
    mul_nonneg (by norm_num [FrameLowArc.u]) hr.2.2.1.le
  dsimp [lineDD]
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperCurvature
