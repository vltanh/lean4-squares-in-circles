module

public import SquaresInCircles.Eight.Owners.Sole.FixedSplit

/-!
# Eight squares: uniform fixed-coordinate concavity at a positive E contact

The exact contact removes the varying EH multiplier.
The same harmonic therefore covers the outside-strip rational families
and the sharp supporting dual. Its curvature reserve holds throughout
the complete split interval, with E's actual nonnegative tangent kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalContactCurvature
open SoleFixedSplit

theorem comparison_harmonic {k t x : ℝ} (hk : k∈Icc (431/500:ℝ) 1)
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x≤-4/25 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ht
  have hkc := mul_le_mul_of_nonneg_right hk.1 (show 0≤Real.cos t by linarith)
  have hks := mul_le_mul_of_nonneg_right hk.2 hs0
  have hcl := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<431/500)
  rw [show (-4/25:ℝ) = -(4/25) by norm_num]
  apply harmonic_endpoint_upper ht hx (by norm_num)
  · simp only [SoleFixedSplit.harmonic,Real.cos_zero,Real.sin_zero,sub_zero,mul_one,mul_zero,
      add_zero]
    nlinarith [hk.1]
  · simp only [SoleFixedSplit.harmonic,sub_self,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      add_zero]
    nlinarith

theorem curvature {MH k eta sigma a b t x : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤-4/25 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith [hk.1]
  have hn : 0≤k*(Real.cos x+eta*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg heta.1 hs0])
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hcoef : sigma-1/2+(13/200)*eta≤957/1000 := by linarith [heta.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hs0)
  have hcoefE := mul_le_mul_of_nonneg_right ha hse0
  have hminor := mul_nonneg hb (show 0≤Real.cos (t-x) by linarith)
  have hmajor : -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤
      SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x := by
    dsimp [SoleFixedSplit.harmonic]
    nlinarith
  exact hmajor.trans (comparison_harmonic hk ht hx)

theorem concave {K MH k eta sigma a b t : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (high K MH k eta sigma a b t) := by
  apply concave_of_deriv2
    (f' := harmonicDeriv (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t)
    (f'' := fun x => -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t x)
  · intro x hx
    exact (SoleFixedSplit.harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (curvature hMH hk heta hsigma ha hb ht hx).trans (by norm_num)

/-- A nonnegative sharp endpoint and a strictly positive G endpoint
exclude every split with an actual positive G error, including x=t. -/
theorem positive_of_positive_right {f : ℝ → ℝ} {t x : ℝ}
    (hf : ConcaveOn ℝ (Icc 0 t) f) (hx : x∈Ioc 0 t)
    (h0 : 0≤f 0) (ht : 0<f t) : 0<f x := by
  have ht0 : 0<t := hx.1.trans_le hx.2
  have ha : 0≤(t-x)/t := div_nonneg (sub_nonneg.mpr hx.2) ht0.le
  have hb : 0<x/t := div_pos hx.1 ht0
  have hab : (t-x)/t+x/t=1 := by field_simp; ring
  have hpoint : ((t-x)/t) • (0:ℝ)+(x/t) • t=x := by
    simp only [smul_eq_mul,mul_zero,zero_add]
    exact div_mul_cancel₀ x ht0.ne'
  have hh := hf.2 (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht0.le⟩)
    (show t∈Icc 0 t from ⟨ht0.le,le_rfl⟩) ha hb.le hab
  rw [hpoint] at hh
  have hl := mul_nonneg ha h0
  have hr := mul_pos hb ht
  simp only [smul_eq_mul] at hh
  linarith

end SquaresInCircles.Eight.ExceptionalContactCurvature
