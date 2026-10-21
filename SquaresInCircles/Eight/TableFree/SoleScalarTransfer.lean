module

public import SquaresInCircles.Eight.TableFree.SoleScalarTaylor

/-!
# Strict trigonometric sole-E endpoint inequalities

Uncompiled source. The five radical rows lose at most 2500 Taylor
remainders, and the outside term loses at most 100. The rational
radius is below two, so the total error is below the explicit 10^-8
allowance in the polynomial certificates. The resulting inequalities
also hold at every smaller actual radius and its actual axis coordinate.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleScalarTransfer
open SoleECoefficients SoleScalarData SoleScalarTaylor HighOrderTaylor
open BoundedRadicalPerturbation
open SoleScalarPolynomials (ScalarCase band radiusUpper axisUpper margin)

theorem outside_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    taylorOutside s t-100*remainder≤
      outsideData s (radiusUpper:ℝ) (axisUpper:ℝ) t
        (Real.sin t) (Real.cos t) (Real.sin (t/2)) := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,heta,heta1⟩
  rcases input_bounds (angle ht) with ⟨hs,hco,hs',hco'⟩
  rcases input_errors (angle ht) with ⟨hse,hce,hhe⟩
  have he0 : 0≤remainder := by norm_num [remainder]
  have hnu := nu_bounds s ht hs hco
  have hN := product_difference
    (show |nuData s t (Real.sin t) (Real.cos t)|≤2 by
      rwa [abs_of_nonneg hnu.1])
    (show |C16 t-1|≤1 by apply abs_le.mpr; constructor <;> linarith [hco'.1,hco'.2])
    (nu_error s ht)
    (show |(Real.cos t-1)-(C16 t-1)|≤remainder by simpa using hce)
  have hN' := abs_le.mp hN
  have hkg : k (band s) t*(1+2*g (band s) t)≤2 := by
    have hm := mul_le_mul_of_nonneg_left
      (show 1+2*g (band s) t≤17/10 by linarith) hk.le
    nlinarith
  have hG := linear_difference
    (show |2*k (band s) t|≤3 by rw [abs_of_nonneg (by positivity)]; linarith)
    (show |k (band s) t*(1+2*g (band s) t)|≤2 by
      rw [abs_of_nonneg (by positivity)]; exact hkg) hce hse
  have hG' := abs_le.mp hG
  have hE := linear_difference (by norm_num : |(2:ℝ)|≤2)
    (show |1+2*eta (band s) t|≤2 by
      rw [abs_of_nonneg (by linarith)]; linarith) hce hse
  have hE' := abs_le.mp hE
  have hD := linear_difference (by norm_num : |(1/2:ℝ)|≤1/2)
    (by norm_num [axisUpper] : |(1/2:ℝ)-(axisUpper:ℝ)|≤1) hce hse
  have hD' := abs_le.mp hD
  have hr := tilted_error (angle ht) (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  simp only [one_mul] at hr
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  have hDr := constant_product_difference (by norm_num : |(3/2:ℝ)|≤3/2) hr
  have hDr' := abs_le.mp hDr
  have hH := linear_difference (by norm_num : |(1:ℝ)|≤1)
    (by norm_num [radiusUpper] : |(-2:ℝ)*(radiusUpper:ℝ)|≤4) hse hhe
  have hH' := abs_le.mp hH
  dsimp [taylorOutside,outsideData]
  split_ifs <;> nlinarith [hN'.1,hN'.2,hG'.1,hG'.2,hE'.1,hE'.2,
    hD'.1,hD'.2,hDr'.1,hDr'.2,hH'.1,hH'.2]

theorem conservative_positive (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0<valueAt s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  have hp := SoleScalarRadicals.taylor_reserve s ht
  have hd := outside_error s ht
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2
    (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<(margin:ℝ) := by norm_num [remainder,margin]
  unfold valueAt
  nlinarith

theorem rowSum_nonneg (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0≤rowSum s t (Real.sin t) (Real.cos t) := by
  have hs := (input_bounds (angle ht)).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds s ht hs i).1 (Real.sqrt_nonneg _)

theorem outside_antitone_parameters (s : ScalarCase) {R R' M M' t : ℝ}
    (ht : t∈domain (band s)) (hR : R≤R') (hM : M≤M') :
    outsideData s R' M' t (Real.sin t) (Real.cos t) (Real.sin (t/2))≤
      outsideData s R M t (Real.sin t) (Real.cos t) (Real.sin (t/2)) := by
  have hd := angle ht
  have hs := (input_bounds hd).1.1
  have hh : t/2∈Set.Icc 0 frameCap :=
    ⟨by linarith [hd.1],by linarith [hd.1,hd.2]⟩
  have hsh := (input_bounds hh).1.1
  have hRp := mul_nonneg (sub_nonneg.mpr hR) hsh
  have hMp := mul_nonneg (sub_nonneg.mpr hM) hs
  dsimp [outsideData]
  split_ifs <;> nlinarith

theorem valueAt_positive (s : ScalarCase) {R M t : ℝ}
    (ht : t∈domain (band s))
    (hR : R≤(radiusUpper:ℝ)) (hM : M≤(axisUpper:ℝ)) :
    0<valueAt s R M t := by
  have hp := conservative_positive s ht
  have ho := outside_antitone_parameters s ht hR hM
  have hs := mul_le_mul_of_nonneg_right hR (rowSum_nonneg s ht)
  unfold valueAt at *
  linarith

/-- The estimates use the actual common radius and its actual axis
coordinate. Only the scalar support comparison uses the rational ceiling. -/
theorem actual_radius_positive (s : ScalarCase) {q t : ℝ}
    (ht : t∈domain (band s)) (hq : q≤qTrial) :
    0<valueAt s (Real.sqrt q) (axisCoordinate q) t := by
  apply valueAt_positive s ht
  · exact (Real.sqrt_le_sqrt hq).trans SoleScalarPolynomials.radius_upper.le
  · have hm := Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))
    have hu := SoleScalarPolynomials.axis_upper
    dsimp [axisCoordinate] at *
    linarith

theorem value_positive (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0<value s t := actual_radius_positive s ht le_rfl

end SquaresInCircles.Eight.TableFree.SoleScalarTransfer
