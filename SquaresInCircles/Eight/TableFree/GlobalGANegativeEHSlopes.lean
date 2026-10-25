module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHHComparison

/-!
# Two whole-interval slope reserves for negative EH

Uncompiled equations (10)--(11) of the small-error companion and
(24)--(26) of the remaining-error companion. The first quartic uses
the prescribed centered quadratic completion. The second uses its
displayed coefficients at the intrinsic ratio endpoint `3/5`.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEH.Slopes
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open NegativeAPositiveTD.PositiveSlope OrdinaryNegativeSlope
open PowerTailBounds DirectedPowerBounds

def smallPoly : ℚ[X] := (C (1/2)+C (179/200)*X)^2*
  (1+X^2+C (499/2500)*X)-C (9789/2500)*X^2
def smallCentered : ℚ[X] := shift (3/4) smallPoly
def smallQuadratic : ℚ := smallCentered.coeff 2-PowerTailBounds.norm smallCentered 3 2 (1/4)

theorem small_certificate :
    smallCentered=C (smallCentered.coeff 0)+C (smallCentered.coeff 1)*X+
      C (smallCentered.coeff 2)*X^2+tail smallCentered 3 2 ∧
    (3691/2500:ℚ)<smallQuadratic ∧
    (1459/10000:ℚ)<smallCentered.coeff 0-
      (smallCentered.coeff 1)^2/(4*smallQuadratic) := by
  have hE : smallCentered=C (468212609/3200000000)+C (76556693/1600000000)*X+
      C (956406681/400000000)*X^2+C (345795959/100000000)*X^3+C (32041/40000)*X^4 := by
    apply Polynomial.funext
    intro x
    simp only [smallCentered,shift,smallPoly,eval_comp,eval_add,eval_mul,eval_pow,eval_sub,
      eval_C,eval_X,eval_one]
    ring
  have h0 : smallCentered.coeff 0=468212609/3200000000 := by rw [hE]; simp
  have h1 : smallCentered.coeff 1=76556693/1600000000 := by rw [hE]; simp
  have h2 : smallCentered.coeff 2=956406681/400000000 := by rw [hE]; simp
  have h3 : smallCentered.coeff 3=345795959/100000000 := by rw [hE]; simp
  have h4 : smallCentered.coeff 4=32041/40000 := by rw [hE]; simp
  have htail : tail smallCentered 3 2=C (smallCentered.coeff 3)*X^3+
      C (smallCentered.coeff 4)*X^4 := by
    simp [tail,Fin.sum_univ_two]
  have hQ : smallQuadratic=590585097/400000000 := by
    simp only [smallQuadratic,PowerTailBounds.norm,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
      zero_add,Nat.reduceAdd,h2,h3,h4]
    norm_num
  refine ⟨?_,?_,?_⟩
  · rw [htail,h0,h1,h2,h3,h4,← add_assoc]
    exact hE
  · rw [hQ]; norm_num
  · rw [hQ,h0,h1]; norm_num

theorem small_polynomial_positive {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    0<(1/2+(179/200)*r)^2*(1+r^2+(499/2500)*r)-qCap*r^2 := by
  have hx : |r-(3/4:ℝ)|≤((1/4:ℚ):ℝ) := by
    rw [abs_le]; push_cast; exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := PowerTailBounds.quadratic_lower small_certificate.1 (by norm_num : (0:ℚ)≤1/4) hx
  have hA : (0:ℝ)<(smallQuadratic:ℝ) := by
    have hn : (0:ℚ)<smallQuadratic := by linarith [small_certificate.2.1]
    exact_mod_cast hn
  have hc : (0:ℝ)<(smallCentered.coeff 0:ℝ)-
      (smallCentered.coeff 1:ℝ)^2/(4*(smallQuadratic:ℝ)) := by
    have hn : (0:ℚ)<smallCentered.coeff 0-
        (smallCentered.coeff 1)^2/(4*smallQuadratic) := by
      linarith [small_certificate.2.2]
    exact_mod_cast hn
  have hq (x : ℝ) : 0<(smallCentered.coeff 0:ℝ)+
      (smallCentered.coeff 1:ℝ)*x+(smallQuadratic:ℝ)*x^2 := by
    have hs := mul_nonneg hA.le (sq_nonneg (x+(smallCentered.coeff 1:ℝ)/(2*(smallQuadratic:ℝ))))
    have he : (smallQuadratic:ℝ)*(x+(smallCentered.coeff 1:ℝ)/(2*(smallQuadratic:ℝ)))^2+
        (smallCentered.coeff 0:ℝ)-(smallCentered.coeff 1:ℝ)^2/(4*(smallQuadratic:ℝ))=
        (smallCentered.coeff 0:ℝ)+(smallCentered.coeff 1:ℝ)*x+(smallQuadratic:ℝ)*x^2 := by
      field_simp [hA.ne']
      ring
    linarith
  have he : aeval (r-(3/4:ℝ)) smallCentered=
      (1/2+(179/200)*r)^2*(1+r^2+(499/2500)*r)-qCap*r^2 := by
    norm_num [smallCentered,shift_eval,smallPoly,qCap]
  rw [he] at hh
  have hAeq : (smallQuadratic:ℝ)=(smallCentered.coeff 2:ℝ)-
      (PowerTailBounds.norm smallCentered 3 2 (1/4):ℝ) := by simp [smallQuadratic]
  rw [← hAeq] at hh
  exact (hq _).trans_le hh

theorem small_endpoint_trig :
    (179/200:ℝ)<Real.cos v-Real.sin v ∧
      (499/5000:ℝ)<Real.sin v := by
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤v by norm_num [v])
  have hl := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤v by norm_num [v])
  have hu := Arithmetic.sin_le_sin9 (show (0:ℝ)≤v by norm_num [v])
  norm_num [v,Arithmetic.cos10,Arithmetic.cos8,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7] at hc hl hu ⊢
  exact ⟨by linarith,by linarith⟩

theorem small_normalized {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -(1/2:ℝ)<r*(Real.cos v-Real.sin v)-R*r*Real.cos v/pairNorm r 1 v := by
  have hr0 : 0<r := by linarith [hr.1]
  have hv : |v|≤frameCap := by norm_num [v,frameCap]
  have hn := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1) hv
  have hn2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1) hv
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hn2
  obtain ⟨hc,hs⟩ := small_endpoint_trig
  have hlow : 1+r^2+(499/2500)*r≤(pairNorm r 1 v)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs.le hr0.le]
  have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg (1/2+(179/200)*r))
  have hpoly := small_polynomial_positive hr
  have hR2 : (R*r)^2=qCap*r^2 := by rw [mul_pow,radius_sq]
  have hcross : R*r<(1/2+(179/200)*r)*pairNorm r 1 v := by
    have hright : 0≤(1/2+(179/200)*r)*pairNorm r 1 v := by positivity
    have hsq : (R*r)^2<((1/2+(179/200)*r)*pairNorm r 1 v)^2 := by
      rw [hR2,mul_pow]
      linarith [hmul,hpoly]
    exact lt_of_pow_lt_pow_left₀ 2 hright hsq
  have hnum := mul_le_mul_of_nonneg_left (Real.cos_le_one v)
    (show 0≤R*r by exact mul_nonneg (Real.sqrt_nonneg _) hr0.le)
  have hquot : R*r*Real.cos v/pairNorm r 1 v<1/2+(179/200)*r := by
    apply (div_lt_iff₀ hn).2
    nlinarith only [hcross,hnum]
  have hlinear := mul_lt_mul_of_pos_left hc hr0
  linarith

theorem small_positive {a b t : ℝ} (ha : 0<a) (hab : a≤b) (hba : b≤2*a)
    (ht : t∈Icc 0 v) : -(1/2)*b<Ud a b t := by
  have hb := ha.trans_le hab
  have hr : a/b∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hb).2 (by linarith),(div_le_one hb).2 hab⟩
  have he : -(1/2)*b<Ud a b v := by
    rw [Ud_normalized hb]
    nlinarith only [mul_lt_mul_of_pos_left (small_normalized hr) hb]
  exact he.trans_le (Ud_antitone ha hab hba
    ⟨ht.1,by dsimp [v,frameCap] at *; linarith [ht.2]⟩
    (by norm_num [v,frameCap]) ht.2)

def farPoly : ℚ[X] := C (9789/2500*(82533/100000)^2)*X^2-
  (C (103/100)*X+C (11293/20000))^2*(1+X^2-C (7058/6250)*X)

theorem far_polynomial_positive {r : ℝ} (hr : r∈Icc (3/5:ℝ) 1) :
    0<qCap*r^2*(82533/100000)^2-
      ((103/100)*r+11293/20000)^2*(1+r^2-2*r*(7058/12500)) := by
  let x : ℝ := r-3/5
  have hx : x∈Icc (0:ℝ) (2/5) := ⟨by dsimp [x]; linarith [hr.1],by dsimp [x]; linarith [hr.2]⟩
  have hx2 : x^2≤(2/5:ℝ)^2 := by nlinarith [hx.1,hx.2]
  have hx3 : x^3≤(2/5:ℝ)^2*x := by nlinarith [mul_le_mul_of_nonneg_right hx2 hx.1]
  have hx4 : x^4≤(2/5:ℝ)^3*x := by
    have ha := mul_le_mul_of_nonneg_right hx3 hx.1
    have hb := mul_le_mul_of_nonneg_left hx.2 hx.1
    nlinarith
  have he : qCap*r^2*(82533/100000)^2-
      ((103/100)*r+11293/20000)^2*(1+r^2-2*r*(7058/12500))=
      3560337820289/625000000000000+(89945678458213/62500000000000)*x+
      (9306058820721/25000000000000)*x^2-(313910731/125000000)*x^3-
      (10609/10000)*x^4 := by dsimp [x,qCap]; ring
  rw [he]
  nlinarith [sq_nonneg x]

theorem far_endpoint_trig :
    (7058/12500:ℝ)<Real.sin (3/5:ℝ) ∧
      Real.sin (3/5:ℝ)<11293/20000 ∧
      (82533/100000:ℝ)<Real.cos (3/5:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤3/5 by norm_num)
  have hu := Arithmetic.sin_le_sin9 (show (0:ℝ)≤3/5 by norm_num)
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤3/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at hs hu hc
  exact ⟨by linarith,by linarith,by linarith⟩

theorem far_normalized {r : ℝ} (hr : r∈Icc (3/5:ℝ) 1) :
    (103/100)*r< -Real.sin (3/5:ℝ)+
      R*r*Real.cos (3/5:ℝ)/VaryingBFunctions.root r (Real.sin (3/5:ℝ)) := by
  have hr0 : 0<r := by linarith [hr.1]
  have ht : (3/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hn := VaryingBFunctions.root_pos r (VaryingBFunctions.sin_mem ht)
  have hn2 := VaryingBFunctions.root_sq r (VaryingBFunctions.sin_mem ht)
  obtain ⟨hs,hu,hc⟩ := far_endpoint_trig
  have hNupper : (VaryingBFunctions.root r (Real.sin (3/5:ℝ)))^2≤
      1+r^2-2*r*(7058/12500) := by
    nlinarith [mul_le_mul_of_nonneg_left hs.le hr0.le]
  have hmul := mul_le_mul_of_nonneg_left hNupper
    (sq_nonneg ((103/100)*r+11293/20000))
  have hpoly := far_polynomial_positive hr
  have hR2 : (R*r*(82533/100000))^2=qCap*r^2*(82533/100000)^2 := by
    rw [mul_pow,mul_pow,radius_sq]
  have hcross : ((103/100)*r+11293/20000)*
      VaryingBFunctions.root r (Real.sin (3/5:ℝ))<R*r*(82533/100000) := by
    have hright : 0≤R*r*(82533/100000) := by
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hr0.le) (by norm_num)
    nlinarith
  have hnum := mul_le_mul_of_nonneg_left hc.le
    (show 0≤R*r by exact mul_nonneg (Real.sqrt_nonneg _) hr0.le)
  have hdiv : (103/100)*r+11293/20000<
      R*r*Real.cos (3/5:ℝ)/VaryingBFunctions.root r (Real.sin (3/5:ℝ)) := by
    apply (lt_div_iff₀ hn).2
    nlinarith only [hcross,hnum]
  linarith

theorem far_negative {a b t : ℝ} (ha : 0<a) (hab : a≤b)
    (hba : (3/5)*b≤a) (ht : t∈Icc 0 (3/5:ℝ)) :
    (103/100)*a<Vd R a b t := by
  have hb := ha.trans_le hab
  have hr : a/b∈Icc (3/5:ℝ) 1 :=
    ⟨(le_div_iff₀ hb).2 hba,(div_le_one hb).2 hab⟩
  have he : (103/100)*a<Vd R a b (3/5:ℝ) := by
    rw [Vd_normalized hb]
    have hh := mul_lt_mul_of_pos_left (far_normalized hr) hb
    have he : b*((103/100)*(a/b))=(103/100)*a := by field_simp [hb.ne']
    rw [he] at hh
    exact hh
  exact he.trans_le (Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le ha hab
    (by linarith) ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
    (by norm_num [frameCap]) ht.2)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEH.Slopes
