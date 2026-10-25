module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameDiagonalEarly

/-!
# Eight squares: the increasing target derivative on the source diagonal

Its derivative is positive on the whole rotated-circle branch (`targetSlopeD_positive`); the
negative-`Z` portion uses four bounds (`negative_Z_factor`). The comparison at `.3`
(`late_slope`) therefore excludes every later source-diagonal minimum by left descent
(`original_late_slope`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord.SameZero.PJ.Diagonal (z₀)

def targetSlopeD (r : Row) (x : ℝ) : ℝ :=
  (q r-p r)*Z x/horizontal x+
    ((q r-p r)*Real.sin x+P r)*Q0*factor x/(horizontal x)^2

lemma targetSlope_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (targetSlope r) (targetSlopeD r x) x := by
  have hU := SecondWord.SameZero.PJ.Diagonal.horizontal_hasDerivAt hx
  have hV : HasDerivAt vertical (horizontal x*factor x) x := by
    convert (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt hx).add_const (1/2) using 1
    · funext y
      simp only [SecondWord.SameZero.PJ.Diagonal.height]
      ring
    · rfl
  have hu : 0<horizontal x := by linarith [(SecondWord.SameZero.PJ.Diagonal.whole_bounds hx).1]
  have hd := (((Real.hasDerivAt_cos x).const_mul (q r-p r)).add
    (((((Real.hasDerivAt_sin x).const_mul (q r-p r)).add_const (P r)).mul hV).div
      hU hu.ne')).sub_const (t r)
  have hc := SecondWord.SameZero.PJ.Diagonal.circle hx
  have hrotation : vertical x*Real.cos x-horizontal x*Real.sin x=Z x := by
    dsimp [vertical,horizontal,SecondWord.SameZero.PJ.Diagonal.vertical,
      SecondWord.SameZero.PJ.Diagonal.horizontal]
    linear_combination (SecondWord.SameZero.PJ.Diagonal.Z x)*(Real.sin_sq_add_cos_sq x)
  convert hd using 1
  · rfl
  · dsimp [targetSlopeD]
    field_simp
    linear_combination (-(q r-p r)*horizontal x)*hrotation-
      (((q r-p r)*Real.sin x+P r)*factor x)*hc

lemma negative_Z_factor {x : ℝ} (hx : x∈Icc start (7/10)) (hz : Z x<0) :
    (665/1250:ℝ)<factor x := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx)
  have hs : (499/1250:ℝ)<Real.sin x := by
    dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀] at hz
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hc : Real.cos x<(917/1000:ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq x,tr.1]
  have hy : (1963/1000:ℝ)<Y x := by
    have hn := hr.2.2.2.2
    norm_num [Q0] at hn
    nlinarith [hr.1,hr.2.2.1,hz]
  have hratio : Real.cos x/Y x<(117/250:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<Y x)).2
    nlinarith
  dsimp [factor,SecondWord.SameZero.PJ.Diagonal.factor]
  linarith

lemma targetSlopeD_positive (r : Row) (hr : Coupled r) {x : ℝ}
    (hx : x∈Icc start (7/10)) : 0<targetSlopeD r x := by
  have hL : 0<q r-p r := by
    have hp := (coupled_signs r hr).1
    linarith [(coefficient_signs r).1]
  have hP := (coefficient_signs r).2.2
  have hcoord := SecondWord.SameZero.PJ.Diagonal.whole_bounds hx
  have hbase := SecondWord.SameZero.PJ.Diagonal.coordinates_positive hx
  have hu : 0<horizontal x := by linarith [hcoord.1]
  have hf : 0<factor x := by linarith [hbase.2.2]
  have hxi := SecondWord.SameZero.PJ.Diagonal.angle_mem hx
  have hsin : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start] at hx; linarith [hx.1])
    (by linarith [hxi.2,Real.pi_gt_three])
  have hF : 0<(q r-p r)*Real.sin x+P r := by
    have := mul_pos hL hsin
    linarith
  by_cases hz : 0≤Z x
  · have h1 := div_nonneg (mul_nonneg hL.le hz) hu.le
    have h2 := div_pos
      (mul_pos (mul_pos hF (show (0:ℝ)<Q0 by norm_num [Q0])) hf) (sq_pos_of_pos hu)
    dsimp [targetSlopeD]
    linarith
  · have hz' : Z x<0 := lt_of_not_ge hz
    have hfL := negative_Z_factor hx hz'
    have hs : (499/1250:ℝ)<Real.sin x := by
      dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀] at hz'
      linarith [ShortMixedZero.fine_diagonal_bounds.1]
    have hZ := (SecondWord.SameZero.PJ.Diagonal.radical_data hx).1
    have h1 := mul_le_mul_of_nonneg_right hZ.le hu.le
    have h2 := mul_le_mul_of_nonpos_left hcoord.2.1.le (by norm_num : (-123/500:ℝ)≤0)
    have hnegative : -(123/500)*(383/200)≤Z x*horizontal x := by linarith
    have hnegativeL := mul_le_mul_of_nonneg_left hnegative hL.le
    have hsinL := mul_le_mul_of_nonneg_left hs.le hL.le
    have hpositive := mul_le_mul
      (show (q r-p r)*(499/1250)≤(q r-p r)*Real.sin x+P r by linarith)
      hfL.le (by norm_num : (0:ℝ)≤665/1250) hF.le
    have hpositiveQ := mul_le_mul_of_nonneg_left hpositive (by norm_num [Q0] : (0:ℝ)≤Q0)
    have href : 0 < -(123/500)*(383/200)+(499/1250)*Q0*(665/1250) := by norm_num [Q0]
    have hreserve := mul_pos hL href
    have hnum : 0<(q r-p r)*Z x*horizontal x+
        ((q r-p r)*Real.sin x+P r)*Q0*factor x := by
      norm_num [Q0] at hpositiveQ hreserve ⊢
      linarith
    have he : targetSlopeD r x=
        ((q r-p r)*Z x*horizontal x+((q r-p r)*Real.sin x+P r)*Q0*factor x)/
          (horizontal x)^2 := by
      dsimp [targetSlopeD]
      field_simp
    rw [he]
    exact div_pos hnum (sq_pos_of_pos hu)

lemma targetSlope_monotone (r : Row) (hr : Coupled r) :
    MonotoneOn (targetSlope r) (Icc start (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hx => (targetSlope_hasDerivAt r hx).continuousAt.continuousWithinAt)
    (fun _ hx => targetSlope_hasDerivAt r (Ioo_subset_Icc_self hx))
    (fun _ hx => (targetSlopeD_positive r hr (Ioo_subset_Icc_self hx)).le)

lemma late_slope (r : Row) (hr : Coupled r) {x : ℝ} (hx : x∈Icc (3/10:ℝ) (7/10)) :
    0<targetSlope r x := by
  have hh := targetSlope_monotone r hr
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start])
    ⟨by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start]; linarith [hx.1],hx.2⟩ hx.1
  linarith [(three_tenths.2.2 r hr)]

lemma actual_targetSlope (r : Row) {B x : ℝ} (hd : Domain B x)
    (hb : contact B x=outerDiagonal) :
    Same.targetFirst r B x=targetSlope r x := by
  obtain ⟨hx,hB⟩ := SecondWord.SameZero.PJ.Diagonal.original_coordinates hd hb
  have hU := (SecondWord.SameZero.PJ.Diagonal.actual_coordinates hx).1
  have hV := (SecondWord.SameZero.PJ.Diagonal.actual_coordinates hx).2
  rw [hB] at hU hV
  dsimp [Same.targetFirst,l,projection,SecondWord.SameZero.k]
  rw [hb,SecondWord.ratio_diagonal]
  change (q r-p r*1)*(Real.cos x+(SecondWord.W B/SecondWord.U B)*Real.sin x)+
    P r*(SecondWord.W B/SecondWord.U B)-t r=targetSlope r x
  rw [hU,hV]
  dsimp [targetSlope]
  ring

lemma original_early_lower (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hb : contact B x=outerDiagonal) (hx : x≤3/10) :
    (11226/12500:ℝ)<Same.cost r B x := by
  obtain ⟨e,he⟩ := Event.exists_event
  obtain ⟨hG,hB⟩ := SecondWord.SameZero.PJ.Diagonal.original_coordinates hd hb
  have hl := early_lower r hr he ⟨Event.before_contact he hd,hx⟩
  have hB' : height x=B := hB
  simp only [cost] at hl
  rw [hB'] at hl
  simp only [Same.cost]
  rw [hb,ShortOuterOne.SameContact.arc_diagonal]
  linarith

lemma original_late_slope (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hb : contact B x=outerDiagonal) (hx : 3/10≤x) :
    0<Same.targetFirst r B x := by
  rw [actual_targetSlope r hd hb]
  exact late_slope r hr ⟨hx,hd.2.1.2⟩

end SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
