module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEParameters

/-!
# The D velocity for the lower charged flat-core-E stress

Uncompiled transcription of Section 2 of the negative-flat-E note.
The original positive-A velocity identities are unchanged. Their negative
angle comparisons retain the smaller charge 473/500 on the same complete
signed intervals and the same intrinsic endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
open Secondary PositiveAngularEnvelope PairNormCalculus

def dVelocity (s : ℝ) : ℝ := R*normD1 1 lowC s
def dCancellation (s : ℝ) : ℝ := dVelocity s-Real.sin (frameCap-s)
def dCancellationD (s : ℝ) : ℝ :=
  R*normD2 1 lowC s+Real.cos (frameCap-s)
def dCancellationDD (s : ℝ) : ℝ :=
  R*normD3 1 lowC s+Real.sin (frameCap-s)

theorem dNorm_sq {s : ℝ} (hs : |s|≤frameCap) :
    (pairNorm 1 lowC s)^2=106/25+(18/5)*Real.sin s := by
  rw [pairNorm_sq (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hs]
  simp only [pairEnergy,pairProduct,lowC]
  ring

theorem dNorm_zero_upper : pairNorm 1 lowC 0<(103/50:ℝ) := by
  have h := dNorm_sq (s:=0) (by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at h
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h]; norm_num)

theorem dNorm_cap_upper : pairNorm 1 lowC frameCap<(1281/500:ℝ) := by
  have h := dNorm_sq (s:=frameCap) (by norm_num [frameCap])
  have ht := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  nlinarith [Real.sqrt_nonneg ((1:ℝ)^2+lowC^2+2*1*lowC*Real.sin frameCap)]

theorem dVelocity_zero_lower : charge+Real.sin frameCap<dVelocity 0 := by
  have hN := pairNorm_pos (p:=1) (q:=lowC) (t:=0)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  have hs := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  have hm := mul_le_mul
    (show charge+Real.sin frameCap≤charge+6443/10000 by linarith)
    dNorm_zero_upper.le hN.le (by norm_num [charge])
  have he : dVelocity 0=lowC*R/pairNorm 1 lowC 0 := by
    dsimp only [dVelocity,normD1,pairProduct]
    rw [Real.cos_zero]
    ring
  rw [he,lt_div_iff₀ hN]
  dsimp only [charge,lowC] at hm ⊢
  linarith [radius_bounds.1]

theorem dVelocity_cap_lower : charge<dVelocity frameCap := by
  have hN := pairNorm_pos (p:=1) (q:=lowC) (t:=frameCap)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  obtain ⟨hc,_,_,_,_⟩ := transport_trig (x:=frameCap) (by norm_num [frameCap])
  have hm := mul_le_mul radius_bounds.1.le hc.le
    (by norm_num : (0:ℝ)≤7648/10000) (Real.sqrt_nonneg qCap)
  have hn := mul_lt_mul_of_pos_left dNorm_cap_upper (by norm_num : (0:ℝ)<charge)
  have he : dVelocity frameCap=lowC*R*Real.cos frameCap/pairNorm 1 lowC frameCap := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he,lt_div_iff₀ hN]
  dsimp only [charge,lowC] at hn ⊢
  linarith

/-- Positive squaring on the whole negative half, retaining the signed
sine in the exact norm identity. -/
theorem dVelocity_negative_lower {s : ℝ} (hs : s∈Icc (-frameCap) 0) :
    dVelocity 0≤dVelocity s := by
  have hsi : |s|≤frameCap := abs_le.mpr
    ⟨hs.1,hs.2.trans (by norm_num [frameCap])⟩
  have hN := pairNorm_pos (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hsi
  have hN0 := pairNorm_pos (p:=1) (q:=lowC) (t:=0)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  have hsq := dNorm_sq hsi
  have hsq0 := dNorm_sq (s:=0) (by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at hsq0
  have hn : -s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have ht := transport_trig hn
  have hsin : -(6443/10000:ℝ)<Real.sin s ∧ Real.sin s≤0 := by
    have he := Real.sin_neg s
    constructor <;> linarith [ht.2.2.1,ht.2.2.2.1]
  have hp : 0≤ -Real.sin s*((106/25)*Real.sin s+18/5) :=
    mul_nonneg (by linarith [hsin.2]) (by linarith [hsin.1])
  have hc := transport_cos_pos hsi
  have hcomp : pairNorm 1 lowC s≤pairNorm 1 lowC 0*Real.cos s := by
    have he : (pairNorm 1 lowC 0*Real.cos s)^2-(pairNorm 1 lowC s)^2=
        -Real.sin s*((106/25)*Real.sin s+18/5) := by
      rw [mul_pow,hsq0,hsq]
      linear_combination (106/25)*Real.sin_sq_add_cos_sq s
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_pos hN0 hc).le (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hcomp
    (show 0≤lowC*R by positivity)
  have he (x : ℝ) : dVelocity x=lowC*R*Real.cos x/pairNorm 1 lowC x := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he 0,he s,Real.cos_zero,mul_one,div_le_div_iff₀ hN0 hN]
  linarith

/-- The positive polynomial is exactly equation (28) of the hand proof. -/
theorem dVelocity_curvature_reserve {s : ℝ} (hs : s∈Icc 0 frameCap) :
    frameCap-s< -R*normD3 1 lowC s := by
  have hsi : |s|≤frameCap := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hN := pairNorm_pos (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hsi
  have hsq := dNorm_sq hsi
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsin := Real.sin_ge_sub_cube hs.1
  have hsinup := Real.sin_le hs.1
  obtain ⟨hc,_,hsin0,_,_⟩ := transport_trig hs
  have hs2 : s^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 2
  have hs3 : s^3≤(7/10:ℝ)^3 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 3
  have hC0 : 0≤1-s^2/2 := by linarith
  have hP0 : 0≤5161/625+(954/125)*s-(159/125)*s^3 := by linarith [hs.1]
  have hP : 5161/625+(954/125)*s-(159/125)*s^3≤
      5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2 := by
    linarith [sq_nonneg (Real.sin s)]
  have hCP := mul_le_mul hcos hP hP0 (by linarith : 0≤Real.cos s)
  have hR : (1773/500:ℝ)≤lowC*R := by
    dsimp [lowC]
    linarith [radius_bounds.1]
  have hRmul := mul_le_mul_of_nonneg_right hR
    (mul_nonneg (by linarith : 0≤Real.cos s)
      (show 0≤5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2 by positivity))
  have hCPmul := mul_le_mul_of_nonneg_left hCP (by norm_num : (0:ℝ)≤1773/500)
  have hnum : (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)≤
      lowC*R*Real.cos s*(5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2) := by
    calc (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)
        =(1773/500)*((1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)) := by ring
      _ ≤ _ := hCPmul
      _ ≤ _ := hRmul
      _ = _ := by ring
  have hNu : pairNorm 1 lowC s<103/50+(7/8)*s :=
    lt_of_pow_lt_pow_left₀ 2 (by linarith [hs.1])
      (by rw [hsq]; linarith [sq_nonneg s,hs.1])
  have hrad : 106/25+(18/5)*Real.sin s≤106/25+(18/5)*s := by linarith
  have hrad0 : 0≤106/25+(18/5)*Real.sin s := by positivity
  have hp2 := pow_le_pow_left₀ hrad0 hrad 2
  have hpow := mul_le_mul hNu.le hp2 (sq_nonneg _)
    (show 0≤103/50+(7/8)*s by linarith [hs.1])
  have hN5 : (pairNorm 1 lowC s)^5=
      pairNorm 1 lowC s*(106/25+(18/5)*Real.sin s)^2 := by
    rw [show (pairNorm 1 lowC s)^5=pairNorm 1 lowC s*((pairNorm 1 lowC s)^2)^2 by ring,hsq]
  have hden : (pairNorm 1 lowC s)^5≤(103/50+(7/8)*s)*(106/25+(18/5)*s)^2 := by
    rw [hN5]
    exact hpow
  have hdenmul := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hs.2)
  have hid : (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)-
      (103/50+(7/8)*s)*(106/25+(18/5)*s)^2*(frameCap-s)=
      1049297/312500+(566517/62500)*s+(16619147/625000)*s^2+
      (1714347/62500)*s^3+(567/50)*s^4+(281907/125000)*s^5 := by
    dsimp [frameCap]
    ring
  have hp : 0<(1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)-
      (103/50+(7/8)*s)*(106/25+(18/5)*s)^2*(frameCap-s) := by
    rw [hid]
    have h3 := pow_nonneg hs.1 3
    have h4 := pow_nonneg hs.1 4
    have h5 := pow_nonneg hs.1 5
    linarith [hs.1,sq_nonneg s]
  have he : -R*normD3 1 lowC s=
      (lowC*R*Real.cos s*(5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2))/
        (pairNorm 1 lowC s)^5 := by
    simp only [normD3,pairEnergy,pairProduct,lowC]
    ring
  rw [he,lt_div_iff₀ (pow_pos hN 5)]
  dsimp only [frameCap] at hdenmul hp ⊢
  linarith

theorem dCancellation_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellation (dCancellationD s) s := by
  have hn := (normD1_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC])
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_sin (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  refine (hn.sub ht).congr_deriv ?_
  rw [dCancellationD]
  ring

theorem dCancellationD_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellationD (dCancellationDD s) s := by
  have hn := (normD2_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC])
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_cos (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  refine (hn.add ht).congr_deriv ?_
  rw [dCancellationDD]
  ring

theorem dCancellation_concave : ConcaveOn ℝ (Icc 0 frameCap) dCancellation := by
  apply concave_of_deriv2
    (fun s hs => dCancellation_hasDerivAt hs)
    (fun s hs => dCancellationD_hasDerivAt hs)
  intro s hs
  have h := dVelocity_curvature_reserve hs
  have ht := Real.sin_le (sub_nonneg.mpr hs.2)
  dsimp [dCancellationDD]
  linarith

theorem dCancellation_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    charge<dCancellation s := by
  apply concave_gt_of_endpoints dCancellation_concave hs
  · dsimp [dCancellation]
    simp only [sub_zero]
    linarith [dVelocity_zero_lower]
  · simpa [dCancellation] using dVelocity_cap_lower

/-- The original signed cancellation is retained: `s+w` is the other
D angle and is bounded by the same frame cap. -/
theorem dVelocity_sine_lower {s w : ℝ}
    (hs : s∈Icc (-frameCap) frameCap) (hw : w∈Icc 0 frameCap)
    (hsw : s+w≤frameCap) : charge<dVelocity s-Real.sin w := by
  by_cases hs0 : s≤0
  · have hv := dVelocity_negative_lower ⟨hs.1,hs0⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hw.2
    linarith [dVelocity_zero_lower]
  · have hs0' : 0≤ s := (lt_of_not_ge hs0).le
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap] at hs; linarith [hs0',Real.pi_gt_three])
      (show w≤frameCap-s by linarith)
    have hh := dCancellation_lower ⟨hs0',hs.2⟩
    dsimp [dCancellation] at hh
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
