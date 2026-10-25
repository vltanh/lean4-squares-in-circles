module

public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTRadicals
public import SquaresInCircles.Eight.Owners.Sole.ScalarTaylor

/-!
# Eight squares: actual trigonometric negative-T endpoint inequalities

The S15/C16 errors are carried through all four
trigonometric inputs on each complete intrinsic interval. The rational
numerator reserve pays their total loss. The support radius is then
decreased to the unchanged original common q.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTTaylor
open ExceptionalNegativeTScalarModel ExceptionalNegativeTScalarData
open HighOrderTaylor BoundedRadicalPerturbation
open ExceptionalNegativeTPolynomials (radiusUpper)

theorem coordinate_errors (s : Case) {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (i : Fin 4) :
    |first s t (Real.sin t) (Real.cos t) i-first s t (S15 t) (C16 t) i|≤3*remainder ∧
    |second s t (Real.sin t) (Real.cos t) i-second s t (S15 t) (C16 t) i|≤3*remainder := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp := SoleScalarTaylor.tilted_error (ExceptionalECoefficients.angle ht)
    (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10)) ⟨he,by linarith⟩
  have hn := SoleScalarTaylor.tilted_error (ExceptionalECoefficients.angle ht)
    (show ExceptionalECoefficients.k (band s.row) t∈Set.Icc 0 (11/10) from
      ⟨hk.le,by linarith⟩) ⟨he,by linarith⟩
  simp only [one_mul] at hp
  have h0 : 0≤remainder := by norm_num [remainder]
  fin_cases i <;> cases h : s.atG <;> refine ⟨?_,?_⟩ <;> simp [first,second,h] <;> linarith

theorem weight_error (s : Case) {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (i : Fin 5) :
    |weight s t (Real.sin t) i-weight s t (S15 t) i|≤3*remainder := by
  have hs := (SoleScalarTaylor.input_errors (ExceptionalECoefficients.angle ht)).1
  have hk := (ExceptionalECoefficients.ranges ht).1
  have hkabs : |ExceptionalECoefficients.k (band s.row) t|≤1 := by
    rw [abs_of_nonneg (by linarith [hk.1])]
    exact hk.2
  have hm := constant_product_difference hkabs hs
  have h0 : 0≤remainder := by norm_num [remainder]
  dsimp [weight]
  split_ifs
  · simp only [sub_self,abs_zero]; linarith
  · linarith
  · linarith

theorem square_error (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 5) :
    |square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i-
      square s t (S15 t) (C16 t) (S15 (angle s.row t)) i|≤100*remainder := by
  have hf := family_domain ht
  rcases SoleScalarTaylor.input_bounds (angles ht).1 with ⟨hs,hc,hs',hc'⟩
  rcases SoleScalarTaylor.input_bounds (angles ht).2.2.1 with ⟨hd,hcd,hd',hcd'⟩
  have he := SoleScalarTaylor.input_errors (angles ht).2.2.1
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp [square]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds s hf hs hc j
    have hb' := coordinates_bounds s hf hs' hc' j
    have herror := coordinate_errors s hf j
    have ha : |first s t (Real.sin t) (Real.cos t) j|≤2 := by rw [abs_of_nonneg hb.1]; exact hb.2.1
    have ha' : |first s t (S15 t) (C16 t) j|≤2 := by rw [abs_of_nonneg hb'.1]; exact hb'.2.1
    have hbb : |second s t (Real.sin t) (Real.cos t) j|≤2 := by
      rw [abs_of_nonneg hb.2.2.1]; exact hb.2.2.2
    have hbb' : |second s t (S15 t) (C16 t) j|≤2 := by rw [abs_of_nonneg hb'.2.2.1]; exact hb'.2.2.2
    unfold squared
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb'
        (by rw [abs_of_nonneg hd'.1]; exact hd'.2) herror.1 herror.2 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb' herror.1 herror.2
  · simp only [sub_self, abs_zero]; linarith

theorem row_error (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 5) :
    |weight s t (Real.sin t) i*Real.sqrt (square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i)-
      weight s t (S15 t) i*Real.sqrt (square s t (S15 t) (C16 t) (S15 (angle s.row t)) i)|≤500*remainder := by
  have hf := family_domain ht
  rcases SoleScalarTaylor.input_bounds (angles ht).1 with ⟨hs,hc,hs',hc'⟩
  have hd := (SoleScalarTaylor.input_bounds (angles ht).2.2.1).1
  have hp := ExceptionalNegativeTPolynomials.square_bounds s i (local_parameter ht)
  rw [(polynomial_rows s t i).1] at hp
  exact weighted_root_difference (square_nonneg s hf hs hc hd i)
    (by linarith [hp.1]) (by linarith [hp.2])
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds s hf hs i) (weight_bounds s hf hs' i) (square_error s ht i) (weight_error s hf i)

theorem rowSum_error (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    rowSum s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t))≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weight s t (Real.sin t) i*Real.sqrt (square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i)≤
        weight s t (S15 t) i*Real.sqrt (square s t (S15 t) (C16 t) (S15 (angle s.row t)) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold taylorSum rowSum
  push_cast at hsum
  linarith

theorem outside_error (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    taylorOutside s t-100*remainder≤
      outside s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) (Real.cos (angle s.row t)) := by
  have hf := family_domain ht
  have hn := nu_bounds hf (index s.row)
  rcases ExceptionalEScalarData.coefficient_bounds hf with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have herr := SoleScalarTaylor.input_errors (angles ht).1
  have hshort := SoleScalarTaylor.input_errors (angles ht).2.2.1
  have hlinear := linear_difference (by norm_num : |(2:ℝ)|≤2)
    (show |1+2*ExceptionalECoefficients.eta (band s.row) t|≤2 by
      rw [abs_of_nonneg (by linarith)]; linarith) herr.2.1 herr.1
  have hkabs : |ExceptionalECoefficients.k (band s.row) t|≤1 := by
    rw [abs_of_nonneg hk.le]
    exact hk1
  have hscaled := constant_product_difference hkabs hlinear
  have hnabs : |nu s.row t (index s.row)|≤2 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hcharge := constant_product_difference hnabs hshort.2.1
  have hmain0 := (abs_le.mp hlinear).1
  have hmain1 := (abs_le.mp hscaled).1
  have hcharge0 := (abs_le.mp hcharge).1
  dsimp [taylorOutside,outside]
  have h0 : 0≤remainder := by norm_num [remainder]
  split_ifs <;> linarith

theorem conservative_reserve (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    (7/50000:ℝ)<value s (radiusUpper:ℝ) t := by
  have hp := ExceptionalNegativeTRadicals.taylor_reserve s ht
  have hd := outside_error s ht
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2 (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<119/800000-7/50000 := by norm_num [remainder]
  unfold value
  nlinarith

theorem rowSum_nonneg (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    0≤rowSum s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) := by
  have hs := (SoleScalarTaylor.input_bounds (angles ht).1).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds s (family_domain ht) hs i).1 (Real.sqrt_nonneg _)

theorem actual_radius_reserve (s : Case) {R t : ℝ}
    (ht : t∈domain s.row) (_hR : 0≤R) (hQU : R^2≤qTrial) :
    (7/50000:ℝ)<value s R t := by
  have hroot := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hroot0 := Real.sqrt_nonneg qTrial
  have hupper := SoleScalarPolynomials.radius_upper
  have hh : R≤Real.sqrt qTrial := by nlinarith
  have hRupper : R≤(radiusUpper:ℝ) :=
    hh.trans (by simpa [radiusUpper,SoleScalarPolynomials.radiusUpper] using hupper.le)
  have hm := mul_le_mul_of_nonneg_right hRupper (rowSum_nonneg s ht)
  have hp := conservative_reserve s ht
  dsimp [value] at *
  linarith

theorem endpoint_positive (s : Case) {R t : ℝ}
    (ht : t∈domain s.row) (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<baseline s R t+correction s.row t+ExceptionalECoefficients.c (band s.row) t*
      slope s.row t*removed s.row t+charge s R t (angle s.row t) (index s.row) := by
  have hh := actual_radius_reserve s ht hR hQU
  rw [value_identity] at hh
  linarith

end SquaresInCircles.Eight.ExceptionalNegativeTTaylor
