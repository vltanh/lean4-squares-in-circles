module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LargeCertificates

/-!
# Positivity of all six BT3 numerators on their whole native domains

Uncompiled assembly of the exact edge, derivative, and chord
certificates in Section 7. The opposite G/D cubic corrections remain
inside the four positive masses throughout this argument.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals

theorem mass_positive (r : Region) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<evaluate x y (mass r i j) := by
  have hh := Certificate.positive_on_domain (mass_certificate r i j).1
    (mass_certificate r i j).2 hd
  have hr : (0:ℝ)<(massReserve r:ℝ) := by cases r <;> norm_num [massReserve]
  exact hr.trans hh

theorem triangle_quotient_derivative (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain .triangle x y) :
    evaluate x y (derivativeY (triangleQuotient i))<0 := by
  have hh := Certificate.upper_on_domain (triangle_derivative_certificate i).1
    (triangle_derivative_certificate i).2 hd
  have hr : (triangleDerivativeReserve i:ℝ)<0 := by
    fin_cases i <;> norm_num [triangleDerivativeReserve]
  exact hh.trans hr

theorem triangle_quotient_antitone (i : Fin 3) {x : ℝ}
    (hx : x∈Icc 0 (8/15:ℝ)) :
    AntitoneOn (fun y => evaluate x y (triangleQuotient i)) (Icc 0 (8/15-x)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y _ => (hasDerivAt_Y (triangleQuotient i) x y).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_Y (triangleQuotient i) x y)
  intro y hy
  exact (triangle_quotient_derivative i
    (show Explicit.Domain .triangle x y from ⟨hx.1,hy.1.le,by linarith [hy.2]⟩)).le

theorem triangle_far_HG (i : Fin 2) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    0<aeval x (triangleFar i.castSucc) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) (triangle_far_certificate i).1
    (triangle_far_certificate i).2 hx
  have hr : (0:ℝ)<(triangleFarReserve i:ℝ) := by
    fin_cases i <;> norm_num [triangleFarReserve]
  exact hr.trans hh

theorem triangle_far_B {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    0<aeval x (triangleFar 2) := by
  have hdata := triangle_far_B_certificate
  have hm : AntitoneOn (fun t : ℝ => aeval t (triangleFar 2)) (Icc 0 (8/15)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun t _ => (CenteredMonomialBounds.aeval_hasDerivAt (triangleFar 2) t).continuousAt.continuousWithinAt)
      (fun t _ => CenteredMonomialBounds.aeval_hasDerivAt (triangleFar 2) t)
    intro t ht
    have hh := (WholeIntervalPolynomial.interval_bounds
      (by norm_num : (0:ℚ)<d) hdata.1 (Ioo_subset_Icc_self ht)).2
    have hr : (WholeIntervalPolynomial.upperOn 39 0 d
        (triangleFar 2).derivative:ℝ)<-(583/1000:ℝ) := by
      exact_mod_cast hdata.2.1
    linarith
  have hh := hm hx (show (8/15:ℝ)∈Icc 0 (8/15) by norm_num) hx.2
  have he : (113/500:ℝ)<aeval (8/15:ℝ) (triangleFar 2) := by
    have hc : (113/500:ℝ)<((triangleFar 2).eval d:ℝ) := by
      exact_mod_cast hdata.2.2
    simpa only [←Certificate.eval_rat,d] using hc
  linarith

theorem triangle_far_positive (i : Fin 3) {x : ℝ}
    (hx : x∈Icc 0 (8/15:ℝ)) : 0<aeval x (triangleFar i) := by
  fin_cases i
  · exact triangle_far_HG 0 hx
  · exact triangle_far_HG 1 hx
  · exact triangle_far_B hx

theorem triangle_quotient_positive (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain .triangle x y) : 0<evaluate x y (triangleQuotient i) := by
  have hx : x∈Icc 0 (8/15:ℝ) := ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩
  have hy : y∈Icc 0 (8/15-x) := ⟨hd.2.1,by linarith [hd.2.2]⟩
  have hh := triangle_quotient_antitone i hx hy
    (show 8/15-x∈Icc 0 (8/15-x) from ⟨by linarith [hx.2],le_rfl⟩) hy.2
  have he : aeval x (triangleFar i)=evaluate x (8/15-x) (triangleQuotient i) := by
    simp [triangleFar,evaluate_restrict,d]
  rw [←he] at hh
  exact (triangle_far_positive i hx).trans_le hh

theorem triangle_base_positive (i : Fin 3) {x : ℝ}
    (hx : x∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval x (triangleBase i) := by
  fin_cases i
  · have hc := triangle_initial_certificate
    have hq := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) hc.2.1 hc.2.2 hx
    have h0 : (893/500000:ℝ)<((triangleBase 0).eval 0:ℝ) := by exact_mod_cast hc.1
    have hh := Certificate.initial_lower hx.1 h0 hq (by norm_num : (0:ℝ)≤8/125)
    linarith
  · obtain ⟨hid,h0,h1,hqId,hqBound⟩ := triangle_chord_certificate
    have hq := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) hqId hqBound hx
    have h0' : (893/500000:ℝ)<((triangleBase 1).eval 0:ℝ) := by exact_mod_cast h0
    have h1' : (893/500000:ℝ)<((triangleBase 1).eval d:ℝ) := by exact_mod_cast h1
    exact Certificate.chord_lower hid hx h0' h1' (by linarith)
  · have hh := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) triangle_B_certificate.1 triangle_B_certificate.2 hx
    linarith

theorem triangle_positive (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain .triangle x y) :
    (1/1000:ℝ)<evaluate x y (numerator .triangle i) := by
  have hbase := triangle_base_positive i
    (show x∈Icc 0 (8/15:ℝ) from ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩)
  have hprod := mul_nonneg hd.2.1 (triangle_quotient_positive i hd).le
  have he := divY_identity (numerator .triangle i) x y
  rw [←evaluate_baseY] at he
  change evaluate x y (numerator .triangle i)=
    aeval x (triangleBase i)+y*evaluate x y (triangleQuotient i) at he
  linarith

theorem rectangle_quotient_positive (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain .rectangle x y) : 0<evaluate x y (rectangleQuotient i) := by
  have hc := rectangle_quotient_certificate i
  have hh := Certificate.positive_on_domain hc.1 hc.2 hd
  have hp : (0:ℝ)<(rectangleQuotientReserve i:ℝ) := by
    fin_cases i <;> norm_num [rectangleQuotientReserve]
  exact hp.trans hh

theorem rectangle_initial_positive (i : Fin 2) {y : ℝ}
    (hy : y∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval y (rectangleBase i.succ) := by
  have hc := rectangle_initial_certificate i
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) hc.2.1 hc.2.2 hy
  have hs : (0:ℝ)≤(rectangleSlopeReserve i:ℝ) := by
    fin_cases i <;> norm_num [rectangleSlopeReserve]
  have h0 : (rectangleInitialReserve i:ℝ)<((rectangleBase i.succ).eval 0:ℝ) := by
    exact_mod_cast hc.1
  have hh := Certificate.initial_lower hy.1 h0 hq hs
  have hv : (1/1000:ℝ)<(rectangleInitialReserve i:ℝ) := by
    fin_cases i <;> norm_num [rectangleInitialReserve]
  exact hv.trans hh

theorem rectangle_base_positive (i : Fin 3) {y : ℝ}
    (hy : y∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval y (rectangleBase i) := by
  fin_cases i
  · have hh := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) rectangle_H_certificate.1 rectangle_H_certificate.2 hy
    linarith
  · exact rectangle_initial_positive 0 hy
  · exact rectangle_initial_positive 1 hy

theorem rectangle_positive (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain .rectangle x y) :
    (1/1000:ℝ)<evaluate x y (numerator .rectangle i) := by
  have hbase := rectangle_base_positive i hd.2
  have hprod := mul_nonneg hd.1.1 (rectangle_quotient_positive i hd).le
  have he := divX_identity (numerator .rectangle i) x y
  rw [←evaluate_baseX] at he
  change evaluate x y (numerator .rectangle i)=
    aeval y (rectangleBase i)+x*evaluate x y (rectangleQuotient i) at he
  linarith

theorem numerator_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : (1/1000:ℝ)<evaluate x y (numerator r i) := by
  cases r
  · exact triangle_positive i hd
  · exact rectangle_positive i hd

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
