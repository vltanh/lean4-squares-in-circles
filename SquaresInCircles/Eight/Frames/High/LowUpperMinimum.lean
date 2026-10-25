module

public import SquaresInCircles.Eight.Frames.High.LowContactSelection
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives

/-!
# Eight squares: the compact upper contact minimum lies on a proved boundary

Every interior contact admits the explicit line with second
derivative below `-.7`.  Compactness therefore reduces the whole
region to its four actual boundary pieces.  The diagonal boundary
uses the unique original circle contact, including its endpoints.
-/

section
/-!
## A whole-domain negative direction for the upper contact surface

The second derivative along `(x+t,B-t)` is less than `-.7` on
every physical contact with `0≤x≤.108`.  All estimates are obtained
from the shifted circle and the complete closed intervals.  In
particular, the mixed derivative is not discarded.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperCurvature
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
  have hnonneg := mul_nonneg (by linarith [hr.1] : 0≤ slope B) ht.1
  dsimp [D,FrameHighLowContactSurface.D]
  constructor <;> nlinarith

theorem contact_E {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0) :
    (129/500:ℝ)<E x B := by
  have ht := trig_bounds hx
  have hr := low_bounds hB
  have hprod := mul_le_mul hr.1.le ht.2.2.1.le
    (by norm_num : (0:ℝ)≤497/500) (by linarith [hr.1] : 0≤ slope B)
  dsimp [E]
  nlinarith

theorem line_curvature {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0)
    (hz : c0≤height x B) : lineDD x B< -(7/10:ℝ) := by
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

end SquaresInCircles.Eight.FrameHighLowUpperCurvature
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperMinimum
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned FrameHighLowUpperSurface

theorem zero_angle_lower {B : ℝ} (hB : B∈Icc 0 b0) : (8833/10000:ℝ)<F 0 B := by
  simpa [F,height_at_zero] using negative_aligned
    (show B∈Icc 0 b1 from ⟨hB.1,hB.2.trans b0_low.2⟩)

theorem zero_target_lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x 0 := by
  have hh := FrameHighLowAxialScalars.upper_lower
    (show x∈FrameHighLowAxialGeometry.upperDomain from ⟨hx.1,by linarith [hx.2]⟩)
  simpa [F,FrameHighLowContactSurface.height_zero,L_zero,FrameHighLowAxialCalculus.upperF]
    using hh

theorem final_angle_lower {B : ℝ} (hB : B∈Icc 0 b0)
    (hz : c0≤height (27/250) B) : (8833/10000:ℝ)<F (27/250) B := by
  have hx : (27/250:ℝ)∈domain := by constructor <;> norm_num [domain]
  have hBlow : B∈Icc 0 b1 := ⟨hB.1,hB.2.trans b0_low.2⟩
  have hc := (physical_contact_bounds hx hBlow hz).2
  have hh := negative_target_tail
    (show height (27/250) B∈sourceDomain from ⟨hc.1,by linarith [hc.2,a2_bounds.1]⟩)
    hBlow (le_refl (27/250:ℝ))
  dsimp [upperCost,sign] at hh
  rw [(first_width (FrameHighLowAxialGeometry.quadrant (domain_axial hx))).2] at hh
  simp only [F]
  linarith

theorem diagonal_lower {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0)
    (hz : height x B=c0) : (8833/10000:ℝ)<F x B := by
  have hd := domain_diagonal hx
  have hBlow : B∈FrameHighLowContactSurface.lowDomain :=
    ⟨by linarith [hB.1],hB.2.trans b0_low.2⟩
  have hdiag := FrameHighLowContactSelection.diagonal_domain hd
  have hzd : height x (FrameHighLowDiagonalCurve.z x)=c0 :=
    FrameHighLowContactSurface.height_diagonal hd
  have heq : B=FrameHighLowDiagonalCurve.z x :=
    (FrameHighLowContactSelection.height_strict_antitone (domain_axial hx)).injOn
      hBlow hdiag (hz.trans hzd.symm)
  have hh := FrameHighLowDiagonalScalar.lower hd
  rw [F,heq,hzd,G_c0]
  simp only [FrameHighLowDiagonalScalar.J] at hh
  linarith

theorem contact_lower {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b1)
    (hz : c0≤height x B) : (8833/10000:ℝ)<F x B := by
  have hb0 := (physical_contact_bounds hx hB hz).1
  obtain ⟨p,hp,hp0,hmin⟩ := contact_region_minimum
    (contact := fun p : ℝ×ℝ => height p.1 p.2-c0)
    (height_continuous.sub continuous_const) F_continuous
    (p₀ := (x,B)) ⟨hx,hb0,sub_nonneg.mpr hz⟩
  have hpz : c0≤height p.1 p.2 := by linarith [hp.2.2]
  have hbound : (8833/10000:ℝ)<F p.1 p.2 := by
    by_cases hx0 : p.1=0
    · simpa only [hx0] using zero_angle_lower hp.2.1
    by_cases hxf : p.1=27/250
    · rw [hxf] at hpz ⊢
      exact final_angle_lower hp.2.1 hpz
    by_cases hB0 : p.2=0
    · simpa only [hB0] using zero_target_lower hp.1
    by_cases hdiag : height p.1 p.2=c0
    · exact diagonal_lower hp.1 hp.2.1 hdiag
    have hxI : p.1∈Ioo (0:ℝ) (27/250) :=
      ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hx0),lt_of_le_of_ne hp.1.2 hxf⟩
    have hBI : p.2∈Ioo (0:ℝ) b0 := by
      refine ⟨lt_of_le_of_ne hp.2.1.1 (Ne.symm hB0),?_⟩
      by_contra! hbad
      have heq : p.2=b0 := le_antisymm hp.2.1.2 hbad
      have hu := height_upper hp.1
        (show p.2∈Icc 0 b1 from ⟨hp.2.1.1,hp.2.1.2.trans b0_low.2⟩)
      have hb : (1:ℝ)-b0=c0 := by simp only [b0]; ring
      exact hdiag (le_antisymm (by rw [heq] at hu ⊢; linarith) hpz)
    have hline : Continuous (fun t : ℝ => height (p.1+t) (p.2-t)) := by
      unfold height FrameHighLowContactSurface.height A
      fun_prop
    obtain ⟨O,hOdef⟩ : ∃ O : Set ℝ, O=(fun t => p.1+t)⁻¹' Ioo (0:ℝ) (27/250) ∩
        ((fun t => p.2-t)⁻¹' Ioo (0:ℝ) b0 ∩ {t | c0<height (p.1+t) (p.2-t)}) := ⟨_,rfl⟩
    have hmem (t : ℝ) : t∈O ↔ p.1+t∈Ioo (0:ℝ) (27/250) ∧
        p.2-t∈Ioo (0:ℝ) b0 ∧ c0<height (p.1+t) (p.2-t) := by
      rw [hOdef]
      simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
    have hO : IsOpen O := by
      rw [hOdef]
      exact (isOpen_Ioo.preimage (by fun_prop)).inter
        ((isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_lt continuous_const hline))
    have hzero : (0:ℝ)∈O := by
      rw [hmem,add_zero,sub_zero]
      exact ⟨hxI,hBI,lt_of_le_of_ne hpz (Ne.symm hdiag)⟩
    have hdata (t : ℝ) (ht : t∈O) :
        p.1+t∈domain ∧ p.2-t∈Icc 0 b0 ∧ c0≤height (p.1+t) (p.2-t) := by
      rw [hmem] at ht
      exact ⟨Ioo_subset_Icc_self ht.1,Ioo_subset_Icc_self ht.2.1,ht.2.2.le⟩
    have hext (t : ℝ) (ht : t∈O) :
        p.2-t∈extendedDomain ∧ height (p.1+t) (p.2-t)∈extendedDomain := by
      have hd := hdata t ht
      have hlow : p.2-t∈Icc 0 b1 := ⟨hd.2.1.1,hd.2.1.2.trans b0_low.2⟩
      have hc := (physical_contact_bounds hd.1 hlow hd.2.2).2
      exact ⟨low_extended hlow,source_extended
        ⟨hc.1,by linarith [hc.2,a2_bounds.1]⟩⟩
    exfalso
    apply not_minimum_on_strictly_concave_curve
      (s := {q : ℝ×ℝ | q.1∈domain ∧ q.2∈Icc 0 b0 ∧ 0≤height q.1 q.2-c0})
      (cost := fun q : ℝ×ℝ => F q.1 q.2)
      (fun q hq => hmin q hq.1 hq.2.1 hq.2.2)
      (curve := fun t : ℝ => (p.1+t,p.2-t))
      (value := fun t => F (p.1+t) (p.2-t))
      (dvalue := fun t => lineD (p.1+t) (p.2-t))
      (ddvalue := fun t => lineDD (p.1+t) (p.2-t))
      hO hzero (show (0:ℝ)<7/10 by norm_num)
    · simp
    · intro t ht
      have hd := hdata t ht
      exact ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2⟩
    · intros
      rfl
    · intro t ht
      exact F_line_deriv (hext t ht).1 (hext t ht).2
    · intro t ht
      exact lineD_line_deriv (hext t ht).1 (hext t ht).2
    · intro t ht
      have hd := hdata t ht
      exact (FrameHighLowUpperCurvature.line_curvature hd.1 hd.2.1 hd.2.2).le
  exact hbound.trans_le hp0

end SquaresInCircles.Eight.FrameHighLowUpperMinimum
end
end
end
