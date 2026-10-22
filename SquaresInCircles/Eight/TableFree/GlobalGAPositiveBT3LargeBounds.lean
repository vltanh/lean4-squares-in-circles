module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3ScalarData

/-!
# Polynomial bounds for the six actual BT3 T endpoints

Uncompiled radical transfer from Section 7. Only the zero-angle D
norm contains the rotating coefficient, so its Taylor upper bound is
inserted monotonically into that squared norm. H, G, and B retain the
fixed original coefficients in their possible negative-angle norm.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals

theorem largeCoefficient_upper (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    largeCoefficient r x y i≤evaluate x y (![1,LargeCertificate.l r,LargeCertificate.qB r] i) := by
  have hh := NonnegativeTotals.Analytic.qB_envelope r .atA hd
  fin_cases i
  · simp [largeCoefficient]
  · simp [largeCoefficient,LargeCertificate.l]
  · cases r <;> simpa [largeCoefficient,LargeCertificate.qB,
      NonnegativeTotals.Certificate.qB,NonnegativeTotals.Certificate.M,
      NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt,
      PositiveTD.tilted,LargeCertificate.m] using hh

theorem largeCoefficient_nonnegative (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0≤largeCoefficient r x y i := by
  have hb := Explicit.base_bounds r hd
  fin_cases i
  · norm_num [largeCoefficient]
  · exact hb.l_positive.le
  · exact hb.l_positive.le.trans (le_max_left _ _)

theorem nonradical_lower (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : evaluate x y (LargeCertificate.A r i)≤nonradical r i x y := by
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds hδ
  have hC : aeval (Explicit.delta r x y) PositiveTD.Certificate.C10-1≤0 := by
    linarith [ht.2.2.2.2.1,Real.cos_le_one (Explicit.delta r x y)]
  have h1 := mul_le_mul_of_nonpos_right (largeCoefficient_upper r i hd) hC
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (largeCoefficient_nonnegative r i hd)
  have hbase := NonnegativeTotals.Analytic.nonradicalBase_lower r .atT hd
  simp only [LargeCertificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
    LargeCertificate.delta,Certificate.evaluate_delta]
  dsimp [nonradical]
  linarith

theorem rotation_upper (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<tilted (Explicit.c r x y) (Explicit.theta r x y) ∧
    tilted (Explicit.c r x y) (Explicit.theta r x y)≤evaluate x y (LargeCertificate.rotation r) := by
  have hh := NonnegativeTotals.Analytic.mAt_data r .atT hd
  simpa [LargeCertificate.rotation,LargeCertificate.m,LargeCertificate.theta,
    NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt,
    NonnegativeTotals.Analytic.polyM,Certificate.M,tilted_eq] using ⟨hh.1,hh.2.1⟩

theorem norm_square_upper (r : Region) (i : Fin 3) (j : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain r x y) : (normAt r i j x y)^2≤evaluate x y (LargeCertificate.P r i j) := by
  have hb := Explicit.base_bounds r hd
  have hk0 : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  fin_cases j
  · by_cases hi : (0:ℕ)=i.val
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hk0 (by norm_num : (0:ℝ)<1) hδ
      simpa [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.k,
        LargeCertificate.l,LargeCertificate.m,LargeCertificate.delta,hi] using hh
    · simp [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.k,
        hi,NonnegativeTotals.Analytic.norm_zero_square,add_comm]
  · by_cases hi : (1:ℕ)=i.val
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hk0 hb.l_positive hδ
      simpa [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.k,
        LargeCertificate.l,LargeCertificate.m,LargeCertificate.delta,hi] using hh
    · simp [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.k,
        LargeCertificate.l,hi,NonnegativeTotals.Analytic.norm_zero_square]
  · by_cases hi : (2:ℕ)=i.val
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hb.l_positive hb.c_positive hδ
      simpa [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.k,
        LargeCertificate.l,LargeCertificate.m,LargeCertificate.delta,hi] using hh
    · simp [normAt,LargeCertificate.P,LargeCertificate.baseNorm,LargeCertificate.l,
        LargeCertificate.m,hi,NonnegativeTotals.Analytic.norm_zero_square]
  · have hi : ¬(3:ℕ)=i.val := by omega
    have hh := NonnegativeTotals.Analytic.norm_zero_coefficient_upper
      (p:=1) (rotation_upper r hd).1.le (rotation_upper r hd).2
    simpa [normAt,LargeCertificate.P,LargeCertificate.baseNorm,hi] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
