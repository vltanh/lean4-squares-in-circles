module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsCertificates

/-!
# Eight squares: strict positivity on both complete nonnegative-total domains

Triangle quotients
are decreased to the far edge, while rectangle quotients are positive
on the whole rectangle. All base-edge cases use their stated initial,
chord, or direct coefficient bounds. In particular the negative TG
chord reserve is paid on the entire interval, including both endpoints.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem eval_rat (p : ℚ[X]) (x : ℚ) : aeval (x:ℝ) p=((p.eval x:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

theorem divX_eval (p : ℚ[X]) (x : ℝ) :
    aeval x p=((p.eval 0:ℚ):ℝ)+x*aeval x p.divX := by
  have hh := congrArg (fun q : ℚ[X] => aeval x q) (Polynomial.X_mul_divX_add p)
  simp only [map_add,map_mul,aeval_X,aeval_C,eq_ratCast] at hh
  rw [←Polynomial.coeff_zero_eq_eval_zero]
  linarith

private theorem r79_icc_d {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    x∈Icc ((0:ℚ):ℝ) ((d:ℚ):ℝ) := by
  simp only [d]; push_cast; exact hx

theorem initial_lower {p : ℚ[X]} {x a b : ℝ}
    (hx : 0≤x) (ha : a<((p.eval 0:ℚ):ℝ))
    (hb : b<aeval x p.divX) (hb0 : 0≤b) : a<aeval x p := by
  have hprod := mul_nonneg hx (hb0.trans hb.le)
  rw [divX_eval]
  linarith

theorem chord_lower {p : ℚ[X]} {x : ℝ}
    (hid : p=chordPolynomial p) (hx : x∈Icc 0 (8/15:ℝ))
    (h0 : (893/500000:ℝ)<((p.eval 0:ℚ):ℝ))
    (h1 : (893/500000:ℝ)<((p.eval d:ℚ):ℝ))
    (hq : -(657/100000:ℝ)<aeval x (chordQuotient p)) :
    (1/1000:ℝ)<aeval x p := by
  set p0 : ℝ := ((p.eval 0:ℚ):ℝ) with hp0
  set p1 : ℝ := ((p.eval d:ℚ):ℝ) with hp1
  let m : ℝ := min p0 p1
  have hm : (893/500000:ℝ) < m := lt_min h0 h1
  have hleft := mul_nonneg
    (show 0≤p0-m by exact sub_nonneg.mpr (min_le_left _ _))
    (show 0≤8/15-x by linarith [hx.2])
  have hright := mul_nonneg
    (show 0≤p1-m by exact sub_nonneg.mpr (min_le_right _ _)) hx.1
  have hchord : (893/500000:ℝ)<p0+(p1-p0)*(15/8)*x := by
    nlinarith only [hm,hleft,hright]
  have hproduct : 0≤x*(8/15-x) := mul_nonneg hx.1 (by linarith [hx.2])
  have hbounded : x*(8/15-x)≤(8/15:ℝ)^2/4 := by
    nlinarith only [sq_nonneg (x-4/15)]
  have hscaled := mul_le_mul_of_nonneg_left hq.le hproduct
  have he := congrArg (fun q : ℚ[X] => aeval x q) hid
  simp only [chordPolynomial,map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hdiv : (((p.eval d-p.eval 0)/d:ℚ):ℝ)=(p1-p0)*(15/8) := by
    rw [hp0,hp1]; push_cast [d]; ring
  rw [hdiv] at he
  have hd : ((d:ℚ):ℝ)=8/15 := by norm_num [d]
  rw [hd] at he
  rw [he]
  nlinarith only [hchord,hscaled,hbounded]

theorem mass_positive (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<evaluate x y (mass r ep i j) := by
  have hh := positive_on_domain (mass_certificate r ep i j).1
    (mass_certificate r ep i j).2 hd
  have hr : (0:ℝ)<(massReserve r:ℝ) := by cases r <;> norm_num [massReserve]
  exact hr.trans hh

theorem triangle_quotient_derivative (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain .triangle x y) :
    evaluate x y (derivativeY (triangleQuotient ep i))<0 := by
  have hh := upper_on_domain (triangle_derivative_certificate ep i).1
    (triangle_derivative_certificate ep i).2 hd
  have hr : (triangleDerivativeReserve ep i:ℝ)<0 := by
    cases ep <;> fin_cases i <;> norm_num [triangleDerivativeReserve]
  exact hh.trans hr

theorem triangle_quotient_antitone (ep : Endpoint) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    AntitoneOn (fun y => evaluate x y (triangleQuotient ep i)) (Icc 0 (8/15-x)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y _ => (hasDerivAt_Y (triangleQuotient ep i) x y).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_Y (triangleQuotient ep i) x y)
  intro y hy
  exact (triangle_quotient_derivative ep i
    (show Explicit.Domain .triangle x y from ⟨hx.1,hy.1.le,by linarith [hy.2]⟩)).le

theorem triangle_far_HG (ep : Endpoint) (i : Fin 2)
    {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) : 0<aeval x (triangleFar ep i.castSucc) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) (triangle_far_certificate ep i).1
    (triangle_far_certificate ep i).2 (r79_icc_d hx)
  have hr : (0:ℝ)<(triangleFarReserve ep i:ℝ) := by
    cases ep <;> fin_cases i <;> norm_num [triangleFarReserve]
  exact hr.trans hh

theorem triangle_far_B (ep : Endpoint) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    0<aeval x (triangleFar ep 2) := by
  have hdata := triangle_far_B_certificate ep
  have hm : AntitoneOn (fun t : ℝ => aeval t (triangleFar ep 2)) (Icc (0:ℝ) (8/15)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun t _ => (CenteredMonomialBounds.aeval_hasDerivAt (triangleFar ep 2) t).continuousAt.continuousWithinAt)
      (fun t _ => CenteredMonomialBounds.aeval_hasDerivAt (triangleFar ep 2) t)
    intro t ht
    have hh := (WholeIntervalPolynomial.interval_bounds
      (by norm_num : (0:ℚ)<d) hdata.1 (r79_icc_d (Ioo_subset_Icc_self ht))).2
    have hr : (WholeIntervalPolynomial.upperOn (degree .triangle ep 2) 0 d
        (triangleFar ep 2).derivative:ℝ)<(triangleFarDerivative ep:ℝ) := by
      exact_mod_cast hdata.2.1
    have hnegative : (triangleFarDerivative ep:ℝ)<0 := by
      cases ep <;> norm_num [triangleFarDerivative]
    linarith
  have hh := hm hx (show (8/15:ℝ)∈Icc 0 (8/15) by norm_num) hx.2
  have he : (triangleFarEndpoint ep:ℝ)<aeval (8/15:ℝ) (triangleFar ep 2) := by
    have hc : (triangleFarEndpoint ep:ℝ)<(((triangleFar ep 2).eval d:ℚ):ℝ) := by
      exact_mod_cast hdata.2.2
    have h8 : ((d:ℚ):ℝ)=8/15 := by norm_num [d]
    rwa [←eval_rat,h8] at hc
  have hp : (0:ℝ)<(triangleFarEndpoint ep:ℝ) := by
    cases ep <;> norm_num [triangleFarEndpoint]
  exact (hp.trans he).trans_le hh

theorem triangle_far_positive (ep : Endpoint) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) : 0<aeval x (triangleFar ep i) := by
  fin_cases i
  · exact triangle_far_HG ep 0 hx
  · exact triangle_far_HG ep 1 hx
  · exact triangle_far_B ep hx

theorem triangle_quotient_positive (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain .triangle x y) :
    0<evaluate x y (triangleQuotient ep i) := by
  have hx : x∈Icc 0 (8/15:ℝ) := ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩
  have hy : y∈Icc 0 (8/15-x) := ⟨hd.2.1,by linarith [hd.2.2]⟩
  have hh := triangle_quotient_antitone ep i hx hy
    (show 8/15-x∈Icc 0 (8/15-x) from ⟨by linarith [hx.2],le_rfl⟩) hy.2
  have he : aeval x (triangleFar ep i)=evaluate x (8/15-x) (triangleQuotient ep i) := by
    simp [triangleFar,evaluate_restrict,d]
  dsimp only at hh
  rw [←he] at hh
  exact (triangle_far_positive ep i hx).trans_le hh

theorem triangle_initial_positive (ep : Endpoint) {x : ℝ}
    (hx : x∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval x (triangleBase ep 0) := by
  have hc := triangle_initial_certificate ep
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) hc.2.1 hc.2.2 (r79_icc_d hx)
  have h0 : (triangleInitialValue ep:ℝ)<(((triangleBase ep 0).eval 0:ℚ):ℝ) := by
    exact_mod_cast hc.1
  have hs : (0:ℝ)≤(triangleInitialSlope ep:ℝ) := by cases ep <;> norm_num [triangleInitialSlope]
  have hh := initial_lower hx.1 h0 hq hs
  have hv : (1/1000:ℝ)<(triangleInitialValue ep:ℝ) := by
    cases ep <;> norm_num [triangleInitialValue]
  exact hv.trans hh

theorem triangle_chord_positive (ep : Endpoint) (i : Fin 3)
    (hi : i=2 ∨ (ep=.atT ∧ i=1)) {x : ℝ}
    (hx : x∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval x (triangleBase ep i) := by
  obtain ⟨hid,h0,h1,hqId,hqBound⟩ := triangle_chord_certificate ep i hi
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) hqId hqBound (r79_icc_d hx)
  have hr : (893/500000:ℝ)≤(chordEndpointReserve ep i:ℝ) ∧
      -(657/100000:ℝ)≤(chordQuotientReserve ep i:ℝ) := by
    rcases hi with rfl | ⟨rfl,rfl⟩
    · cases ep <;> norm_num [chordEndpointReserve,chordQuotientReserve]
    · norm_num [chordEndpointReserve,chordQuotientReserve]
  have h0' : (chordEndpointReserve ep i:ℝ)<(((triangleBase ep i).eval 0:ℚ):ℝ) := by
    exact_mod_cast h0
  have h1' : (chordEndpointReserve ep i:ℝ)<(((triangleBase ep i).eval d:ℚ):ℝ) := by
    exact_mod_cast h1
  exact chord_lower hid hx (hr.1.trans_lt h0') (hr.1.trans_lt h1') (hr.2.trans_lt hq)

theorem triangle_base_positive (ep : Endpoint) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval x (triangleBase ep i) := by
  cases ep <;> fin_cases i
  · exact triangle_initial_positive .atA hx
  · have hh := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) triangle_AG_certificate.1 triangle_AG_certificate.2 (r79_icc_d hx)
    have hc : ((21/12500:ℚ):ℝ)=21/12500 := by norm_num
    rw [hc] at hh
    exact lt_trans (by norm_num) hh
  · exact triangle_chord_positive .atA 2 (Or.inl rfl) hx
  · exact triangle_initial_positive .atT hx
  · exact triangle_chord_positive .atT 1 (Or.inr ⟨rfl,rfl⟩) hx
  · exact triangle_chord_positive .atT 2 (Or.inl rfl) hx

theorem triangle_positive (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain .triangle x y) :
    (1/1000:ℝ)<evaluate x y (numerator .triangle ep i) := by
  have hbase := triangle_base_positive ep i
    (show x∈Icc 0 (8/15:ℝ) from ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩)
  have hq := triangle_quotient_positive ep i hd
  have hprod := mul_nonneg hd.2.1 hq.le
  have he := divY_identity (numerator .triangle ep i) x y
  rw [←evaluate_baseY] at he
  change evaluate x y (numerator .triangle ep i)=
    aeval x (triangleBase ep i)+y*evaluate x y (triangleQuotient ep i) at he
  linarith

theorem rectangle_quotient_positive (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain .rectangle x y) :
    0<evaluate x y (rectangleQuotient ep i) := by
  have hc := rectangle_quotient_certificate ep i
  have hh := positive_on_domain hc.1 hc.2 hd
  have hp : (0:ℝ)<(rectangleQuotientReserve ep i:ℝ) := by
    cases ep <;> fin_cases i <;> norm_num [rectangleQuotientReserve]
  exact hp.trans hh

theorem rectangle_initial_positive (ep : Endpoint) (i : Fin 3)
    (hi : ¬(ep=.atA ∧ i=0)) {y : ℝ} (hy : y∈Icc 0 (8/15:ℝ)) :
    (1/1000:ℝ)<aeval y (rectangleBase ep i) := by
  have hc := rectangle_initial_certificate ep i hi
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<d) hc.2.1 hc.2.2 (r79_icc_d hy)
  have hs : (0:ℝ)≤(rectangleSlopeReserve ep i:ℝ) := by
    cases ep <;> fin_cases i <;> norm_num [rectangleSlopeReserve]
  have h0 : (17/10000:ℝ)<(((rectangleBase ep i).eval 0:ℚ):ℝ) := by
    rw [show (17/10000:ℝ)=((17/10000:ℚ):ℝ) by norm_num]
    exact Rat.cast_lt.mpr hc.1
  have hh := initial_lower hy.1 h0 hq hs
  linarith

theorem rectangle_base_positive (ep : Endpoint) (i : Fin 3)
    {y : ℝ} (hy : y∈Icc 0 (8/15:ℝ)) : (1/1000:ℝ)<aeval y (rectangleBase ep i) := by
  by_cases hi : ep=.atA ∧ i=0
  · rcases hi with ⟨rfl,rfl⟩
    have hh := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<d) rectangle_AH_certificate.1 rectangle_AH_certificate.2 (r79_icc_d hy)
    have hc : ((1/800:ℚ):ℝ)=1/800 := by norm_num
    rw [hc] at hh
    linarith
  · exact rectangle_initial_positive ep i hi hy

theorem rectangle_positive (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain .rectangle x y) :
    (1/1000:ℝ)<evaluate x y (numerator .rectangle ep i) := by
  have hbase := rectangle_base_positive ep i hd.2
  have hq := rectangle_quotient_positive ep i hd
  have hprod := mul_nonneg hd.1.1 hq.le
  have he := divX_identity (numerator .rectangle ep i) x y
  rw [←evaluate_baseX] at he
  change evaluate x y (numerator .rectangle ep i)=
    aeval y (rectangleBase ep i)+x*evaluate x y (rectangleQuotient ep i) at he
  linarith

theorem numerator_positive (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    (1/1000:ℝ)<evaluate x y (numerator r ep i) := by
  cases r
  · exact triangle_positive ep i hd
  · exact rectangle_positive ep i hd

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Certificate
