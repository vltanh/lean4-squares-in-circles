module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsCharges
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsEndpointData

/-!
# Eight squares: every polynomial endpoint bounds its original nonradical expression

The actual maximum
coefficient is kept until its stated upper envelope is inserted into
a nonpositive cosine term. The T endpoint uses the negative sine
coefficient in exactly the lower-bound direction written in the proof.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev polyM (r : Region) (ep : Endpoint) (x y : ℝ) : ℝ := evaluate x y (Certificate.M r ep)

theorem mAt_data (r : Region) (ep : Endpoint) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0< mAt ep (Explicit.c r x y) (Explicit.theta r x y) ∧
    mAt ep (Explicit.c r x y) (Explicit.theta r x y)≤polyM r ep x y ∧
    (2/3)*Explicit.l r x y< mAt ep (Explicit.c r x y) (Explicit.theta r x y) := by
  have hθ := (Explicit.domains hd).1
  have hz := zAt_domain ep hθ
  have hratio := Explicit.tilted_ratio r hd hz
  have hb := Explicit.base_bounds r hd
  have hm0 : 0<Explicit.tilted r x y (zAt ep (Explicit.theta r x y)) := by
    nlinarith [hratio.1,hb.l_positive]
  have hle : mAt ep (Explicit.c r x y) (Explicit.theta r x y)≤polyM r ep x y := by
    cases ep
    · simp [mAt,zAt,polyM,Certificate.M,PositiveTD.tilted]
    · have hh := mul_le_mul_of_nonneg_left (Explicit.tilt_taylor hθ).2 hb.c_positive.le
      simpa [mAt,zAt,polyM,Certificate.M,PositiveTD.tilted,PositiveTD.eta,Explicit.tilt] using hh
  exact ⟨hm0,hle,hratio.1⟩

theorem qB_envelope (r : Region) (ep : Endpoint) {x y : ℝ} (hd : Explicit.Domain r x y) :
    max (Explicit.l r x y) (mAt ep (Explicit.c r x y) (Explicit.theta r x y))≤
      evaluate x y (Certificate.qB r ep) := by
  have hm := mAt_data r ep hd
  cases r
  · have henv := Explicit.triangle_q_envelope hd
    cases ep
    · simp only [Certificate.qB,Certificate.evaluate_qStar,mAt,zAt,
        PositiveTD.tilted,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one]
      exact max_le henv.1 henv.2.1.le
    · simp only [Certificate.qB,Certificate.evaluate_qStar]
      exact max_le henv.1 henv.2.2.le
  · have hθ := (Explicit.domains hd).1
    have htilt := Explicit.rectangle_tilted_bounds hd (zAt_domain ep hθ)
    have hlc := (Explicit.rectangle_ranges hd).2.2.2.2.1
    have hlm : Explicit.l .rectangle x y≤ mAt ep (Explicit.c .rectangle x y) (Explicit.theta .rectangle x y) :=
      hlc.le.trans htilt.1
    simp only [Certificate.qB,max_eq_right hlm]
    exact hm.2.1

theorem largeCoefficient_nonnegative (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0≤largeCoefficient r ep x y i := by
  have hb := Explicit.base_bounds r hd
  have hm := mAt_data r ep hd
  fin_cases i
  · norm_num [largeCoefficient]
  · exact hb.l_positive.le
  · exact hb.l_positive.le.trans (le_max_left _ _)

theorem largeCoefficient_upper (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    largeCoefficient r ep x y i≤evaluate x y (![1,Certificate.l r,Certificate.qB r ep] i) := by
  fin_cases i
  · simp [largeCoefficient]
  · simp [largeCoefficient]
  · exact qB_envelope r ep hd

theorem nonradicalBase_lower (r : Region) (ep : Endpoint)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.ABase r ep)≤nonradicalBase r ep x y := by
  have hb := Explicit.base_bounds r hd
  have hθ := (Explicit.domains hd).1
  have hE := Charges.E_charge r hd
  cases ep
  · have hA := mul_le_mul_of_nonneg_left (Charges.theta_charge r hd) hb.l_positive.le
    simp only [Certificate.ABase,map_add,map_mul,evaluate_scalar,
      Certificate.evaluate_k,Certificate.evaluate_l,Certificate.evaluate_c]
    dsimp only [nonradicalBase]
    push_cast
    linarith
  · have ht := PositiveTD.Certificate.taylor_bounds hθ
    have hs := (transport_trig hθ).2.2.1
    have hcoeff : (3/2)*(293/1000:ℝ)+1/2-(Certificate.sigmabar:ℝ)≤0 := by
      norm_num [Certificate.sigmabar]
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 hcoeff
    have hσ := mul_le_mul_of_nonneg_right Charges.sigma_upper hs
    have hinner : 1+2*aeval (Explicit.theta r x y) PositiveTD.Certificate.C10+
        ((3/2)*(293/1000:ℝ)+1/2-(Certificate.sigmabar:ℝ))*
          aeval (Explicit.theta r x y) PositiveTD.Certificate.S9≤
        1+2*Real.cos (Explicit.theta r x y)+
          ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.theta r x y) := by
      dsimp [PositiveTD.eta]
      linarith [ht.2.2.2.2.1]
    have hprod := mul_le_mul_of_nonneg_left hinner hb.c_positive.le
    simp only [Certificate.ABase,map_add,map_mul,map_one,evaluate_scalar,evaluate_lift,
      Certificate.evaluate_k,Certificate.evaluate_l,Certificate.evaluate_c,
      Certificate.evaluate_theta]
    push_cast
    dsimp only [nonradicalBase]
    linarith only [hE,hprod]

theorem nonradical_lower (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.A r ep i)≤nonradical r ep i x y := by
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds hδ
  have hC : aeval (Explicit.delta r x y) PositiveTD.Certificate.C10-1≤0 := by
    linarith [ht.2.2.2.2.1,Real.cos_le_one (Explicit.delta r x y)]
  have h1 := mul_le_mul_of_nonpos_right (largeCoefficient_upper r ep i hd) hC
  have h2 := mul_le_mul_of_nonneg_left
    (sub_le_sub_right ht.2.2.2.2.1 1) (largeCoefficient_nonnegative r ep i hd)
  have hbase := nonradicalBase_lower r ep hd
  simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
    Certificate.evaluate_delta]
  dsimp [nonradical]
  linarith

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic
