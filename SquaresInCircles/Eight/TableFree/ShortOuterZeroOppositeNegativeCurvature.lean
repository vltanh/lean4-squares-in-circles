module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositeNegativeGeometry

/-!
# The four concave negative contact surfaces

Uncompiled transcription of Section 2.1, equations (7)--(8). The last
row uses the two simultaneous whole-domain projection estimates and
averages them. The preceding row uses its one convex quadratic on the
whole sine interval. No angle subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain UW_circle U_positive)

def ratioQuotient (b B : ℝ) : ℝ := (U B)^3/(U b)^3
abbrev lowerRatio : ℝ := (1399/1000)^3/(943/500)^3

def curvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioQuotient (minus B x) B*(minusK B x)^2-
    l r (minus B x)*Real.sin x-v r

lemma ratioQuotient_identity {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) : ratioD b=ratioQuotient b B*ratioD B := by
  have hu := U_positive (outer_domain hb)
  have hU := U_positive (outer_domain hB)
  change Q0/(U b)^3=((U B)^3/(U b)^3)*(Q0/(U B)^3)
  field_simp [hu.ne',hU.ne']

lemma curvature_identity (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    minusTargetCurvature r B x=ratioD B*curvature r B x := by
  rw [minusTargetCurvature,ratioQuotient_identity hd.2.2 hd.1]
  dsimp [curvature]
  ring

lemma ratioQuotient_bounds {b B : ℝ} (hb : b∈Icc low outerDiagonal)
    (hB : B∈Icc low outerDiagonal) :
    0<ratioQuotient b B ∧ lowerRatio≤ratioQuotient b B ∧ ratioQuotient b B<123/50 := by
  have hu := band_root hb
  have hU := band_root hB
  have hup : 0<U b := by linarith [hu.1]
  have hUp : 0<U B := by linarith [hU.1]
  have hulo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
  have hUlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hU.1.le 3
  have huhi := pow_le_pow_left₀ hup.le hu.2.le 3
  have hUhi := pow_le_pow_left₀ hUp.le hU.2.le 3
  refine ⟨div_pos (pow_pos hUp 3) (pow_pos hup 3),?_,?_⟩
  · apply (le_div_iff₀ (pow_pos hup 3)).2
    dsimp [lowerRatio]
    have hp := mul_le_mul_of_nonneg_left huhi
      (by norm_num : (0:ℝ)≤(1399/1000)^3/(943/500)^3)
    norm_num at hp
    linarith
  · apply (div_lt_iff₀ (pow_pos hup 3)).2
    have href : (943/500:ℝ)^3<(123/50)*(1399/1000)^3 := by norm_num
    nlinarith

lemma projection_lower {B x : ℝ} (hd : MinusDomain B x) :
    (Real.cos x)^2≤(minusK B x)^2 := by
  have tr := positive_trig hd.2.1
  have hR := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hp := mul_nonneg hR.le tr.2.2.1
  have hk : Real.cos x≤ minusK B x := by
    dsimp [minusK,SecondWord.OppositeZero.minusK]
    linarith
  exact pow_le_pow_left₀ (by linarith [tr.1]) hk 2

lemma projection_upper {B x : ℝ} (hd : MinusDomain B x) :
    (minusK B x)^2≤1+2*Real.sin x := by
  have tr := positive_trig hd.2.1
  have hr := SecondWord.outer_ratio_bounds hd.1
  have hs := mul_le_mul_of_nonneg_right hr.2.1 tr.2.2.1
  have hk : minusK B x≤Real.cos x+Real.sin x := by
    dsimp [minusK,SecondWord.OppositeZero.minusK]
    linarith
  have hk0 := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.2.2
  have hsq := pow_le_pow_left₀ hk0.le hk 2
  have hcs := mul_le_mul_of_nonneg_right tr.2.1 tr.2.2.1
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma projection_cauchy {B x : ℝ} (hd : MinusDomain B x) :
    (U B*Real.cos x+W B*Real.sin x)^2≤Q0 := by
  have hc := UW_circle (outer_domain hd.1)
  have ht := Real.sin_sq_add_cos_sq x
  have hs := sq_nonneg (U B*Real.sin x-W B*Real.cos x)
  nlinarith [hc,ht,
    show (U B*Real.cos x+W B*Real.sin x)^2+
      (U B*Real.sin x-W B*Real.cos x)^2=Q0 by
        linear_combination hc+((U B)^2+(W B)^2)*ht]

lemma weighted_projection {B x : ℝ} (hd : MinusDomain B x) :
    ratioQuotient (minus B x) B*(minusK B x)^2=
      U B*(U B*Real.cos x+W B*Real.sin x)^2/(U (minus B x))^3 := by
  have hu := U_positive (outer_domain hd.2.2)
  have hU := U_positive (outer_domain hd.1)
  have hr : ratio B=W B/U B := rfl
  simp only [ratioQuotient,minusK,SecondWord.OppositeZero.minusK]
  rw [hr]
  field_simp

lemma projection_product_bounds {B x : ℝ} (hd : MinusDomain B x) :
    lowerRatio*(Real.cos x)^2≤ratioQuotient (minus B x) B*(minusK B x)^2 ∧
    ratioQuotient (minus B x) B*(minusK B x)^2≤(123/50)*(1+2*Real.sin x) ∧
    ratioQuotient (minus B x) B*(minusK B x)^2<
      Q0*(943/500)/(1399/1000)^3 := by
  have hb := band_coordinates hd
  have hr := ratioQuotient_bounds hb.2 hb.1
  have hu := band_root hb.2
  have hU := band_root hb.1
  refine ⟨mul_le_mul hr.2.1 (projection_lower hd) (sq_nonneg _)
    hr.1.le,?_,?_⟩
  · exact mul_le_mul hr.2.2.le (projection_upper hd) (sq_nonneg _) (by norm_num)
  · rw [weighted_projection hd]
    have hC := projection_cauchy hd
    have hprod := mul_le_mul_of_nonneg_left hC (by linarith [hU.1] : 0≤U B)
    have hprodU := mul_lt_mul_of_pos_right hU.2 (by norm_num [Q0] : 0<Q0)
    have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
    apply (div_lt_iff₀ (pow_pos (by linarith [hu.1] : 0<U (minus B x)) 3)).2
    have hden := mul_le_mul_of_nonneg_left hu3
      (by norm_num [Q0] : (0:ℝ)≤Q0*(943/500)/(1399/1000)^3)
    have hc : Q0*(943/500)/(1399/1000)^3*(1399/1000)^3=Q0*(943/500) := by
      field_simp
    linarith only [hden,hc,hprod,hprodU]

abbrev coefficientA : ℝ := (51554/100000)*lowerRatio
abbrev coefficientB : ℝ := (19335/100000)*(123/50)
abbrev coefficientC : ℝ := (19335/100000)*Q0*(943/500)/(1399/1000)^3

def rowFourQuadratic (s : ℝ) : ℝ :=
  coefficientA*s^2-(68355/100000)*s+19335/100000-coefficientA

lemma rowFourQuadratic_negative {s : ℝ} (hs : s∈Icc (0:ℝ) (129/200)) :
    rowFourQuadratic s<0 := by
  have hA : 0<coefficientA := by norm_num [coefficientA,lowerRatio]
  have hproduct := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have hlinear : rowFourQuadratic s≤
      rowFourQuadratic 0+(s/(129/200))*(rowFourQuadratic (129/200)-rowFourQuadratic 0) := by
    dsimp [rowFourQuadratic]
    nlinarith
  have hl : rowFourQuadratic 0<0 := by norm_num [rowFourQuadratic,coefficientA,lowerRatio]
  have hu : rowFourQuadratic (129/200)<0 := by norm_num [rowFourQuadratic,coefficientA,lowerRatio]
  have hweight : s/(129/200)∈Icc (0:ℝ) 1 := by constructor <;> linarith [hs.1,hs.2]
  have hleft := mul_nonpos_of_nonneg_of_nonpos (show 0≤1-s/(129/200) by linarith [hweight.2]) hl.le
  have hright := mul_nonpos_of_nonneg_of_nonpos hweight.1 hu.le
  by_cases hz : s=0
  · simpa [hz] using hl
  · have hstrict := mul_neg_of_pos_of_neg (show 0<s/(129/200) by
      have hp : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hz); positivity) hu
    linarith

lemma curvature_negative (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : curvature r B x<0 := by
  have tr := positive_trig hd.2.1
  have hL := slope_bounds r hd.2.2
  have hp := projection_product_bounds hd
  have hR := ratioQuotient_bounds (band_coordinates hd).2 (band_coordinates hd).1
  have hK := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.2.2
  have hs : Real.sin x∈Icc (0:ℝ) (129/200) := ⟨tr.2.2.1,by linarith [tr.2.2.2.1]⟩
  rcases hr with rfl | rfl | rfl | rfl
  · have hnon := mul_nonneg (by linarith [hL.1] : 0≤l 0 (minus B x)) hs.1
    norm_num [curvature,p,v]
    linarith
  · have hstrict := mul_pos hR.1 (sq_pos_of_pos hK)
    have hnon := mul_nonneg (by linarith [hL.1] : 0≤l 1 (minus B x)) hs.1
    norm_num [curvature,p,v]
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_left hp.1 (by norm_num : (0:ℝ)≤51554/100000)
    have hlabel := mul_le_mul_of_nonneg_right hL.1 hs.1
    have hquad := rowFourQuadratic_negative hs
    have hid := Real.sin_sq_add_cos_sq x
    dsimp [curvature,rowFourQuadratic,coefficientA] at *
    norm_num [p,v] at *
    nlinarith
  · have hprod1 := mul_le_mul_of_nonneg_left hp.2.1 (by norm_num : (0:ℝ)≤19335/100000)
    have hprod2 := mul_lt_mul_of_pos_left hp.2.2 (by norm_num : (0:ℝ)<19335/100000)
    have hlabel : (76744/100000:ℝ)≤l 5 (minus B x) := by
      have hratio := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.2.2)
      norm_num [l,p,q]
      linarith
    have hlabelS := mul_le_mul_of_nonneg_right hlabel hs.1
    have href : (coefficientB+coefficientC)/2-(51554/100000:ℝ)< -(2/125:ℝ) ∧
        coefficientB<(76744/100000:ℝ) := by
      constructor <;> norm_num [coefficientB,coefficientC,Q0]
    have hneg := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr href.2.le) hs.1
    dsimp [curvature,coefficientB,coefficientC] at *
    norm_num [p,v] at *
    nlinarith

/-- All four target-concave rows, with both original coordinates coupled. -/
theorem target_curvature_negative (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : minusTargetCurvature r B x<0 := by
  rw [curvature_identity r hd]
  exact mul_neg_of_pos_of_neg (ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1))
    (curvature_negative r hr hd)

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Negative
