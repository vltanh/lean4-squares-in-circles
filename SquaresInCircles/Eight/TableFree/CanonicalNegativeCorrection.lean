module

public import SquaresInCircles.Eight.TableFree.CanonicalNegativeStress

/-!
# A direct quantitative correction for the two canonical negative errors

Uncompiled reconstruction.  The exact five-circle scalar has only two
errors after canonicalization.  Sine/cosine addition and elementary
Taylor bounds preserve their first-order flux reserves.  The estimates
below therefore need neither an owner table nor a five-variable Hessian.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CanonicalNegativeCorrection
open CanonicalNegativeStress

theorem mixed_turn_lower {omega k α r L : ℝ}
    (hr : 0≤r) (hflux : 0≤k*Real.cos α-omega*Real.sin α)
    (hamp : 0≤omega*Real.cos α+k*Real.sin α)
    (hL : omega*Real.cos α+k*Real.sin α≤L) :
    -(k*Real.cos α-omega*Real.sin α)*r-L*r^2/2≤
      omega*(Real.cos (α-r)-Real.cos α)+k*(Real.sin (α-r)-Real.sin α) := by
  have hid : omega*(Real.cos (α-r)-Real.cos α)+k*(Real.sin (α-r)-Real.sin α)=
      (omega*Real.cos α+k*Real.sin α)*(Real.cos r-1)-
        (k*Real.cos α-omega*Real.sin α)*Real.sin r := by
    rw [Real.cos_sub,Real.sin_sub]
    ring
  rw [hid]
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le hr) hflux
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := r)) hamp
  have hquad := mul_le_mul_of_nonneg_right hL (sq_nonneg r)
  linarith

theorem ordinary_turn_lower {beta k t B K : ℝ}
    (ht : 0≤t) (hbeta : beta∈Icc 0 B) (hk : k∈Icc 0 K) :
    k*t-B*t^2/2-K*t^3/6≤beta*(Real.cos t-1)+k*Real.sin t := by
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := t)) hbeta.1
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube ht) hk.1
  have hB := mul_le_mul_of_nonneg_right hbeta.2 (sq_nonneg t)
  have hK := mul_le_mul_of_nonneg_right hk.2 (pow_nonneg ht 3)
  linarith

theorem short_secant_bounds {e : ℝ} (he : e∈Icc 0 (3/200:ℝ)) :
    0<Real.cos e ∧ 1≤1/Real.cos e ∧ 1/Real.cos e≤501/500 ∧
      0≤1/Real.cos e-1 ∧ 1/Real.cos e-1≤(501/1000)*e^2 ∧
      0≤(1/Real.cos e)^2-1 ∧ (1/Real.cos e)^2-1≤(101/100)*e^2 ∧
      e-e^3/6≤Real.tan e := by
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hcl := Real.one_sub_sq_div_two_le_cos (x := e)
  have hcos : (999/1000:ℝ)<Real.cos e := by
    nlinarith
  have hc : 0<Real.cos e := by linarith
  have hc1 := Real.cos_le_one e
  have hv : 1≤1/Real.cos e := by apply (le_div_iff₀ hc).2; simpa
  have hvu : 1/Real.cos e≤501/500 := by apply (div_le_iff₀ hc).2; linarith
  have hd : 0≤1/Real.cos e-1 := by linarith
  have hdiff : 1/Real.cos e-1=(1-Real.cos e)/Real.cos e := by
    field_simp [hc.ne']
  have hdu : 1/Real.cos e-1≤(501/1000)*e^2 := by
    rw [hdiff]
    apply (div_le_iff₀ hc).2
    have hp := mul_le_mul_of_nonneg_right hcos.le (sq_nonneg e)
    nlinarith [sq_nonneg e]
  have hv2 : 0≤(1/Real.cos e)^2-1 := by nlinarith
  have hv2u : (1/Real.cos e)^2-1≤(101/100)*e^2 := by
    have hp := mul_le_mul hdu (show 1/Real.cos e+1≤1001/500 by linarith)
      (show 0≤1/Real.cos e+1 by linarith) (by positivity : 0≤(501/1000)*e^2)
    nlinarith [sq_nonneg e]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Real.pi_gt_three])
  have htangent : Real.sin e≤Real.tan e := by
    rw [Real.tan_eq_sin_div_cos]
    apply (le_div_iff₀ hc).2
    simpa using mul_le_mul_of_nonneg_left hc1 hs0
  exact ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,(Real.sin_ge_sub_cube he.1).trans htangent⟩

theorem secant_turn_lower {beta gamma e : ℝ}
    (hbeta : beta∈Icc 0 (39/50:ℝ)) (hgamma : gamma∈Icc 0 (6/5:ℝ))
    (he : e∈Icc 0 (3/200:ℝ)) :
    beta*(13/12)*e-(61/100)*e^2≤
      beta*(1/Real.cos e-1)+beta*(13/12)*Real.tan e-
        (gamma/2)*((1/Real.cos e)^2-1) := by
  obtain ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,htan⟩ := short_secant_bounds he
  have hsec := mul_nonneg hbeta.1 hd
  have htan' := mul_le_mul_of_nonneg_left htan
    (mul_nonneg hbeta.1 (by norm_num : (0:ℝ)≤13/12))
  have hlast := mul_le_mul hgamma.2 hv2u hv2 (by norm_num : (0:ℝ)≤6/5)
  have hbeta3 := mul_le_mul_of_nonneg_right hbeta.2 (pow_nonneg he.1 3)
  have he3 : e^3≤(3/200)*e^2 := by
    have hp := mul_le_mul_of_nonneg_right he.2 (sq_nonneg e)
    nlinarith
  nlinarith [sq_nonneg e]

theorem ordinary_short_lower {beta k t : ℝ}
    (hbeta : beta∈Icc 0 (39/50:ℝ)) (hk : k∈Icc 0 (431/500:ℝ))
    (ht : t∈Icc 0 (3/200:ℝ)) :
    k*t-(79/200)*t^2≤beta*(Real.cos t-1)+k*Real.sin t := by
  have hh := ordinary_turn_lower ht.1 hbeta hk
  have ht3 : t^3≤(3/200)*t^2 := by
    have hp := mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t)
    nlinarith
  nlinarith [sq_nonneg t]

/-- The stationary primitive bounds are the only inputs to this
quantitative scalar lemma.  Its conclusion is proved from the exact
two-error formula, not assumed as a terminal contract. -/
theorem correction_lower {w : CanonicalNegativeStress.Parameters} {α t e : ℝ}
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (homega : w.omega∈Icc 0 (4/5:ℝ))
    (hKA : KA w∈Icc 0 (471/500:ℝ))
    (hbeta : w.beta∈Icc 0 (39/50:ℝ))
    (hKB : KB w∈Icc 0 (431/500:ℝ))
    (hgamma : w.beta^2/(2*w.mu 2)∈Icc 0 (6/5:ℝ))
    (hflux : 0≤flux w α)
    (hsmall : 3367/250000≤KB w-flux w α)
    (hsecant : 23/1000≤w.beta*(13/12)-flux w α) :
    (t+e)/5000≤correction w α t e := by
  have hα0 : 0≤α := by linarith [hα.1]
  have hc0 : 0≤Real.cos α := by
    have ha2 := pow_le_pow_left₀ hα0 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hα0
    (by linarith [hα.2,Real.pi_gt_three])
  have hamp0 : 0≤w.omega*Real.cos α+KA w*Real.sin α :=
    add_nonneg (mul_nonneg homega.1 hc0) (mul_nonneg hKA.1 hs0)
  have hamp : w.omega*Real.cos α+KA w*Real.sin α≤951/1000 := by
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one α) homega.1
    have h2 := mul_le_mul hKA.2 ((Real.sin_le hα0).trans hα.2) hs0
      (by norm_num : (0:ℝ)≤471/500)
    linarith [homega.2]
  have hA := mixed_turn_lower (show 0≤t+e by linarith) hflux hamp0 hamp
  have ht' : t∈Icc 0 (3/200:ℝ) := ⟨ht,by linarith⟩
  have he' : e∈Icc 0 (3/200:ℝ) := ⟨he,by linarith⟩
  have hB := ordinary_short_lower hbeta hKB ht'
  have hD := secant_turn_lower hbeta hgamma he'
  have hDcoef : (w.beta^2/(2*w.mu 2))/2=w.beta^2/(4*w.mu 2) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hDcoef] at hD
  have hsmall' := mul_le_mul_of_nonneg_right hsmall ht
  have hsecant' := mul_le_mul_of_nonneg_right hsecant he
  have htt : t^2≤(t+e)*t := by nlinarith [mul_nonneg ht he]
  have hee : e^2≤(t+e)*e := by nlinarith [mul_nonneg ht he]
  have hrt := mul_le_mul_of_nonneg_right hr ht
  have hre := mul_le_mul_of_nonneg_right hr he
  rw [show α-(t+e)=α-t-e by ring] at hA
  dsimp [correction,flux] at *
  linarith

end SquaresInCircles.Eight.TableFree.CanonicalNegativeCorrection
