module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsEndpointBounds

/-!
# Eight squares: polynomial upper bounds on the four squared norms

The B coefficient is increased only after `q ≥ p sin δ` is proved for the pair
(`B_sine_charge`). The sine is then bounded by the lower alternating polynomial. All other norms
keep their coefficients (`norm_square_upper`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem norm_zero_square (p q : ℝ) : (pairNorm p q 0)^2=p^2+q^2 := by
  rw [pairNorm_zero]
  exact Real.sq_sqrt (by positivity)

theorem norm_negative_square {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    (pairNorm p q (-t))^2=p^2+q^2-2*p*q*Real.sin t := by
  have hh := pairNorm_sq hp hq
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  rw [hh,pairEnergy,pairProduct,Real.sin_neg]
  ring

theorem norm_negative_polynomial {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    (pairNorm p q (-t))^2≤p^2+q^2-2*p*q*aeval t PositiveTD.Certificate.S11 := by
  have hs := (PositiveTD.Certificate.taylor_bounds ht).2.1
  have hh := mul_le_mul_of_nonneg_left hs (show 0≤2*p*q by positivity)
  rw [norm_negative_square hp hq ht]
  linarith

theorem norm_zero_coefficient_upper {p q M : ℝ} (hq : 0≤q) (hM : q≤M) :
    (pairNorm p q 0)^2≤p^2+M^2 := by
  rw [norm_zero_square]
  have := pow_le_pow_left₀ hq hM 2
  linarith

theorem norm_negative_coefficient_upper {p q M t : ℝ}
    (hp : 0<p) (hq : 0<q) (hM : q≤M)
    (ht : t∈Icc 0 frameCap) (hcharge : p*Real.sin t≤q) :
    (pairNorm p q (-t))^2≤p^2+M^2-2*p*M*aeval t PositiveTD.Certificate.S11 := by
  have hdiff := mul_nonneg (sub_nonneg.mpr hM)
    (show 0≤M+q-2*p*Real.sin t by linarith)
  have hsin := mul_le_mul_of_nonneg_left (PositiveTD.Certificate.taylor_bounds ht).2.1
    (show 0≤2*p*M by have hMp := hq.le.trans hM; positivity)
  rw [norm_negative_square hp hq ht]
  nlinarith only [hdiff,hsin]

theorem B_sine_charge (r : Region) (ep : Endpoint) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    Explicit.l r x y*Real.sin (Explicit.delta r x y)≤
      mAt ep (Explicit.c r x y) (Explicit.theta r x y) := by
  have hb := Explicit.base_bounds r hd
  have hm := mAt_data r ep hd
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  have hs := (transport_trig hδ).2.2.2.1
  have hp := mul_lt_mul_of_pos_left hs hb.l_positive
  linarith [hm.2.2,hb.l_positive]

theorem norm_square_upper (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    (normAt r ep i j x y)^2≤evaluate x y (Certificate.P r ep i j) := by
  have hb := Explicit.base_bounds r hd
  have hk0 : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hm := mAt_data r ep hd
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  fin_cases j
  · change (pairNorm (Explicit.k r x y) 1
        (if (0:ℕ)=i.val then -Explicit.delta r x y else 0))^2≤
      evaluate x y ((1+Certificate.k r^2)-if (0:ℕ)=i.val then
        scalar 2*Certificate.k r*lift (Certificate.delta r) PositiveTD.Certificate.S11 else 0)
    split_ifs with hi
    · have hh := norm_negative_polynomial hk0 (by norm_num : (0:ℝ)<1) hδ
      simp only [map_sub,map_add,map_mul,map_pow,map_one,evaluate_scalar,evaluate_lift,
        Certificate.evaluate_k,Certificate.evaluate_delta]
      push_cast
      linarith
    · rw [norm_zero_square]
      simp only [map_sub,map_add,map_pow,map_one,map_zero,Certificate.evaluate_k]
      linarith
  · change (pairNorm (Explicit.k r x y) (Explicit.l r x y)
        (if (1:ℕ)=i.val then -Explicit.delta r x y else 0))^2≤
      evaluate x y ((Certificate.k r^2+Certificate.l r^2)-if (1:ℕ)=i.val then
        scalar 2*(Certificate.k r*Certificate.l r)*
          lift (Certificate.delta r) PositiveTD.Certificate.S11 else 0)
    split_ifs with hi
    · have hh := norm_negative_polynomial hk0 hb.l_positive hδ
      simp only [map_sub,map_add,map_mul,map_pow,evaluate_scalar,evaluate_lift,
        Certificate.evaluate_k,Certificate.evaluate_l,Certificate.evaluate_delta]
      push_cast
      linarith
    · rw [norm_zero_square]
      simp only [map_sub,map_add,map_pow,map_zero,Certificate.evaluate_k,Certificate.evaluate_l]
      linarith
  · change (pairNorm (Explicit.l r x y) (mAt ep (Explicit.c r x y) (Explicit.theta r x y))
        (if (2:ℕ)=i.val then -Explicit.delta r x y else 0))^2≤
      evaluate x y ((Certificate.l r^2+Certificate.M r ep^2)-if (2:ℕ)=i.val then
        scalar 2*(Certificate.l r*Certificate.M r ep)*
          lift (Certificate.delta r) PositiveTD.Certificate.S11 else 0)
    split_ifs with hi
    · have hh := norm_negative_coefficient_upper hb.l_positive hm.1 hm.2.1 hδ
        (B_sine_charge r ep hd)
      simp only [map_sub,map_add,map_mul,map_pow,evaluate_scalar,evaluate_lift,
        Certificate.evaluate_l,Certificate.evaluate_delta]
      simp only [polyM] at hh
      push_cast
      linarith
    · have hh := norm_zero_coefficient_upper (p:=Explicit.l r x y) hm.1.le hm.2.1
      simp only [map_sub,map_add,map_pow,map_zero,Certificate.evaluate_l]
      simp only [polyM] at hh
      linarith
  · have hi : ¬(3:ℕ)=i.val := by omega
    change (pairNorm (Explicit.c r x y) 1
        (if (3:ℕ)=i.val then -Explicit.delta r x y else 0))^2≤
      evaluate x y ((1+Certificate.c r^2)-if (3:ℕ)=i.val then
        scalar 2*0*lift (Certificate.delta r) PositiveTD.Certificate.S11 else 0)
    simp only [hi,↓reduceIte]
    rw [norm_zero_square]
    simp only [map_sub,map_add,map_pow,map_one,map_zero,Certificate.evaluate_c]
    linarith

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic
