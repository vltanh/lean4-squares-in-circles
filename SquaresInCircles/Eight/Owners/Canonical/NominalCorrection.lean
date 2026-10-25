module

public import SquaresInCircles.Eight.Owners.Canonical.NegativeCorrection
public import SquaresInCircles.Eight.Owners.Canonical.NominalFlux

/-!
# Eight squares: the nominal two-error remainder on both complete tilt tails

The original nominal weights retain the
first-order gains of both nonnegative errors.  Above sine 3/50 the
whole correction is nonnegative.  Below that cut its possible loss is
at most 3/2 times the squared total error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNominal
open CanonicalNegativeStress CanonicalNegativeCorrection

theorem ordinary_short_lower {b k t : ℝ}
    (hb : b∈Icc 0 (1:ℝ)) (hk : k∈Icc 0 (6/5:ℝ))
    (ht : t∈Icc 0 (3/200:ℝ)) :
    k*t-(51/100)*t^2≤b*(Real.cos t-1)+k*Real.sin t := by
  have hh := ordinary_turn_lower ht.1 hb hk
  have ht3 : t^3≤(3/200)*t^2 := by
    have hp := mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t)
    nlinarith
  nlinarith [sq_nonneg t]

theorem secant_short_lower {b γ e : ℝ}
    (hb : b∈Icc 0 (1:ℝ)) (hγ : γ∈Icc 0 (3/2:ℝ))
    (he : e∈Icc 0 (3/200:ℝ)) :
    b*(13/12)*e-(77/100)*e^2≤
      b*(1/Real.cos e-1)+b*(13/12)*Real.tan e-
        (γ/2)*((1/Real.cos e)^2-1) := by
  obtain ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,htan⟩ := short_secant_bounds he
  have hsec := mul_nonneg hb.1 hd
  have htan' := mul_le_mul_of_nonneg_left htan
    (mul_nonneg hb.1 (by norm_num : (0:ℝ)≤13/12))
  have hlast := mul_le_mul hγ.2 hv2u hv2 (by norm_num : (0:ℝ)≤3/2)
  have hb3 := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg he.1 3)
  have he3 : e^3≤(3/200)*e^2 := by
    have hp := mul_le_mul_of_nonneg_right he.2 (sq_nonneg e)
    nlinarith
  nlinarith [sq_nonneg e]

theorem correction_lower {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    (Real.sin α/2)*t+(1/25)*e-(7/10)*(t+e)^2-
      (51/100)*t^2-(77/100)*e^2≤correction (atTilt α) α t e := by
  have hs := (short_trig hα).1
  have hb := beta_bounds hs
  have hb' : (atTilt α).beta∈Icc 0 (1:ℝ) := ⟨le_trans (by norm_num) hb.1,hb.2⟩
  have hk : KB (atTilt α)∈Icc (0:ℝ) (6/5) := KB_bounds hs
  have hγ : (atTilt α).beta^2/(2*(atTilt α).mu 2)∈Icc (0:ℝ) (3/2) := gamma_bounds hs
  have hflux := (flux_bounds hα).1
  have hamp := amplitude_bounds hα
  have hA := mixed_turn_lower (omega:=1) (k:=KA (atTilt α)) (α:=α) (L:=7/5)
    (show 0≤t+e by linarith) hflux
    (by simpa only [one_mul] using hamp.1)
    (by simpa only [one_mul] using hamp.2)
  have hB := ordinary_short_lower hb' hk (show t∈Icc 0 (3/200:ℝ) from ⟨ht,by linarith⟩)
  have hD := secant_short_lower hb' hγ (show e∈Icc 0 (3/200:ℝ) from ⟨he,by linarith⟩)
  have hDcoef : ((atTilt α).beta^2/(2*(atTilt α).mu 2))/2=
      (atTilt α).beta^2/(4*(atTilt α).mu 2) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hDcoef] at hD
  have hsmall := mul_le_mul_of_nonneg_right (small_error_reserve hα) ht
  have hsecant := mul_le_mul_of_nonneg_right (secant_error_reserve hα) he
  rw [show α-(t+e)=α-t-e by ring] at hA
  have homega : (atTilt α).omega=1 := rfl
  dsimp only [flux] at hsmall hsecant
  rw [homega] at hsmall hsecant
  dsimp only [correction]
  rw [homega]
  linarith

theorem correction_nonneg {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ)) (hs : 3/50≤Real.sin α)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    0≤correction (atTilt α) α t e := by
  have hb := correction_lower hα ht he hr
  have hs' := mul_le_mul_of_nonneg_right hs ht
  have hte := mul_nonneg ht he
  have htt : t^2≤(t+e)*t := by nlinarith
  have hee : e^2≤(t+e)*e := by nlinarith
  have hrt := mul_le_mul_of_nonneg_right hr ht
  have hre := mul_le_mul_of_nonneg_right hr he
  nlinarith

theorem correction_rough_lower {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    -(3/2)*(t+e)^2≤correction (atTilt α) α t e := by
  have hb := correction_lower hα ht he hr
  have hsin := mul_nonneg (div_nonneg (short_trig hα).1.1 (by norm_num : (0:ℝ)≤2)) ht
  have hte := mul_nonneg ht he
  nlinarith [sq_nonneg t,sq_nonneg e,sq_nonneg (t+e)]

end SquaresInCircles.Eight.CanonicalNominal
