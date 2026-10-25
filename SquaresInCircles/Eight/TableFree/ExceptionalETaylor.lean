module

public import SquaresInCircles.Eight.TableFree.ExceptionalERadicals

/-!
# Actual trigonometric exceptional endpoint inequalities

Uncompiled source. The fixed S15/C16 remainder controls the outside
term and all five weighted radicals on each complete interval. The
10^-8 polynomial allowance pays that error. The resulting positive
endpoint expressions hold at every original common radius up to qTrial.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalETaylor
open ExceptionalECoefficients ExceptionalEScalarData HighOrderTaylor BoundedRadicalPerturbation
open ExceptionalEPolynomials (ScalarCase band negativeIndex radiusUpper margin)

theorem coordinate_errors (s : ScalarCase) {t : ℝ}
    (ht : t∈domain (band s)) (i : Fin 4) :
    |firstData (band s) t (Real.sin t) (Real.cos t) i-firstData (band s) t (S15 t) (C16 t) i|≤
      3*remainder := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp := SoleScalarTaylor.tilted_error (angle ht)
    (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10)) ⟨he,by linarith⟩
  simp only [one_mul] at hp
  fin_cases i <;> simp [firstData] <;> linarith [show 0≤remainder by norm_num [remainder]]

theorem weight_error {t : ℝ} (ht : t∈Set.Icc 0 frameCap) (i : Fin 5) :
    |weightData (Real.sin t) i-weightData (S15 t) i|≤3*remainder := by
  have hs := (SoleScalarTaylor.input_errors ht).1
  have h0 : 0≤remainder := by norm_num [remainder]
  dsimp [weightData]
  split_ifs
  · simp only [sub_self,abs_zero]; linarith
  · linarith

theorem square_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) (i : Fin 5) :
    |squareData s t (Real.sin t) (Real.cos t) i-squareData s t (S15 t) (C16 t) i|≤
      100*remainder := by
  rcases SoleScalarTaylor.input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have he := SoleScalarTaylor.input_errors (angle ht)
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp [squareData]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds ht hs hc j
    have hb' := coordinates_bounds ht hs' hc' j
    have hd := coordinate_errors s ht j
    have ha : |firstData (band s) t (Real.sin t) (Real.cos t) j|≤2 := by
      rw [abs_of_nonneg hb.1]; exact hb.2.1
    have ha' : |firstData (band s) t (S15 t) (C16 t) j|≤2 := by
      rw [abs_of_nonneg hb'.1]; exact hb'.2.1
    have hbb : |secondData (band s) t j|≤2 := by rw [abs_of_nonneg hb.2.2.1]; exact hb.2.2.2
    have hd0 : |secondData (band s) t j-secondData (band s) t j|≤3*remainder := by
      rw [sub_self, abs_zero]; linarith
    change |squaredData s t (Real.sin t) (Real.cos t) j-
      squaredData s t (S15 t) (C16 t) j|≤100*remainder
    unfold squaredData
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb
        (by rw [abs_of_nonneg hs'.1]; exact hs'.2) hd hd0 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb hd hd0
  · simp only [sub_self, abs_zero]; linarith

theorem row_error (s : ScalarCase) {t : ℝ} (ht : t∈ExceptionalEPolynomials.domain s) (i : Fin 5) :
    |weightData (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)-
      weightData (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)|≤500*remainder := by
  have hf := ExceptionalEPolynomials.family_domain ht
  rcases SoleScalarTaylor.input_bounds (angle hf) with ⟨hs,hc,hs',hc'⟩
  have hp := ExceptionalEPolynomials.square_bounds s i (ExceptionalEPolynomials.local_parameter ht)
  rw [(polynomial_rows s t i).1] at hp
  exact weighted_root_difference (square_nonneg s hf hs hc i) hp.1.le hp.2.le
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds hs i) (weight_bounds hs' i) (square_error s hf i) (weight_error (angle hf) i)

theorem rowSum_error (s : ScalarCase) {t : ℝ} (ht : t∈ExceptionalEPolynomials.domain s) :
    rowSum s t (Real.sin t) (Real.cos t)≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weightData (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)≤
        weightData (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold taylorSum rowSum
  push_cast at hsum
  linarith

theorem outside_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    taylorOutside s t-100*remainder≤outsideData s t (Real.sin t) (Real.cos t) := by
  have hn := nu_bounds ht (negativeIndex s)
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have herr := SoleScalarTaylor.input_errors (angle ht)
  have hh := linear_difference
    (show |2+nuData (band s) t (negativeIndex s)|≤4 by
      rw [abs_of_nonneg (by linarith [hn.1])]; linarith [hn.2])
    (show |1+2*eta (band s) t|≤2 by rw [abs_of_nonneg (by linarith)]; linarith)
    herr.2.1 herr.1
  have hlower := (abs_le.mp hh).1
  dsimp [taylorOutside,outsideData]
  nlinarith [show 0≤remainder by norm_num [remainder]]

theorem conservative_positive (s : ScalarCase) {t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) : 0<valueAt s (radiusUpper:ℝ) t := by
  have hp := ExceptionalERadicals.taylor_reserve s ht
  have hd := outside_error s (ExceptionalEPolynomials.family_domain ht)
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2 (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<(margin:ℝ) := by norm_num [remainder,margin]
  unfold valueAt
  nlinarith

theorem rowSum_nonneg (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0≤rowSum s t (Real.sin t) (Real.cos t) := by
  have hs := (SoleScalarTaylor.input_bounds (angle ht)).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds hs i).1 (Real.sqrt_nonneg _)

theorem valueAt_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (hR : R≤(radiusUpper:ℝ)) : 0<valueAt s R t := by
  have hp := conservative_positive s ht
  have hm := mul_le_mul_of_nonneg_right hR (rowSum_nonneg s (ExceptionalEPolynomials.family_domain ht))
  dsimp [valueAt] at *
  linarith

/-- The original common radius is retained; qTrial only bounds the
scalar support coefficient. -/
theorem actual_radius_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<valueAt s R t := by
  apply valueAt_positive s ht
  have hroot := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hroot0 := Real.sqrt_nonneg qTrial
  have hupper := SoleScalarPolynomials.radius_upper
  have hh : R≤Real.sqrt qTrial := by nlinarith
  exact hh.trans (by simpa [radiusUpper,SoleScalarPolynomials.radiusUpper] using hupper.le)

theorem endpoint_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<ExceptionalContactSupport.atE R (k (band s) t) (ell (band s) t)
      (c (band s) t) (eta (band s) t) t+charge R (band s) t (negativeIndex s) := by
  rw [← value_eq_endpoint_charge]
  exact actual_radius_positive s ht hR hQU

end SquaresInCircles.Eight.TableFree.ExceptionalETaylor
