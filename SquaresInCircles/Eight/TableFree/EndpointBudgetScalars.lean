module

public import SquaresInCircles.Eight.TableFree.EndpointRotationPenalty
public import SquaresInCircles.Eight.TableFree.EndpointBudgetPolynomial

/-!
# Strict scalar bounds for every original H--D span

Uncompiled source draft.  A single polynomial comparison covers the
complete short positive span.  The other intrinsic ranges use fixed
positive stress weights and two elementary trigonometric endpoints.
Every bound has the common strict reserve `1/8000`, larger than the
`1/10000` tolerance in the signed-middle wrong-sign argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EndpointBudgetScalars
open PositiveAngularEnvelope PairNormCalculus
open EndpointRotationPenalty

def S0 : ℝ := 2*Real.sqrt (qCap-1)-3
def k0 : ℝ := Real.sqrt (qCap-1/4)-1
def K : ℝ := 847/800
def epsilon : ℝ := 1/8000
def baseline (l : ℝ) : ℝ := 2*R*pairNorm l 1 0-3*l-1
def positiveGain (s : ℝ) : ℝ := k0*Real.sin s+(1-Real.cos s)/2
def negativeGain (d s : ℝ) : ℝ := -K*Real.sin s+d*(1-Real.cos s)
def profileX (s : ℝ) : ℝ := (3-positiveGain s)/2
def profileY (s : ℝ) : ℝ := Real.sqrt (qCap-(profileX s)^2)
def weight (s : ℝ) : ℝ := profileX s/profileY s

theorem radical_bounds :
    (914575/1000000 : ℝ)<k0 ∧ k0<914576/1000000 ∧
      S0<(415026/1000000 : ℝ) ∧ S0<(52/125 : ℝ) := by
  have hk := Real.sq_sqrt (show 0≤qCap-1/4 by norm_num [qCap])
  have hk0 := Real.sqrt_nonneg (qCap-1/4)
  have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs0 := Real.sqrt_nonneg (qCap-1)
  dsimp [k0,S0,qCap] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem zero_norm_sq (l : ℝ) : (pairNorm l 1 0)^2=1+l^2 := by
  rw [pairNorm_zero,Real.sq_sqrt (by positivity : 0≤l^2+(1:ℝ)^2)]
  ring

theorem radius_norm_sq (l : ℝ) : (R*pairNorm l 1 0)^2=qCap*(1+l^2) := by
  rw [mul_pow,R_sq,zero_norm_sq]

theorem fixed_norm_bounds :
    R*pairNorm (7/6) 1 0<3041/1000 ∧
      R*pairNorm (7/4) 1 0<9971/2500 ∧
      R*pairNorm (4/5) 1 0<507/200 := by
  have h₁ := radius_norm_sq (7/6)
  have h₂ := radius_norm_sq (7/4)
  have h₃ := radius_norm_sq (4/5)
  have hn (l : ℝ) : 0≤R*pairNorm l 1 0 :=
    mul_nonneg R_nonneg (Real.sqrt_nonneg _)
  norm_num [qCap] at h₁ h₂ h₃
  exact ⟨by nlinarith [hn (7/6)],by nlinarith [hn (7/4)],by nlinarith [hn (4/5)]⟩

theorem positive_gain_bounds {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    0≤positiveGain s ∧ positiveGain s≤13/25 := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hsin0 := (transport_trig hs').2.2.1
  have hcos1 := Real.cos_le_one s
  have hsin := Real.sin_le hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(1/2 : ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hk := radical_bounds
  have hk0 : 0≤k0 := by linarith [hk.1]
  have hmul := mul_le_mul_of_nonneg_left hsin hk0
  have hmul' := mul_le_mul_of_nonneg_right
    (show k0≤183/200 by linarith [hk.2.1]) hs.1
  have hnonneg := mul_nonneg hk0 hsin0
  dsimp [positiveGain]
  constructor <;> nlinarith

theorem profile_bounds {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    profileX s∈Icc (31/25 : ℝ) (3/2) ∧
      1<profileY s ∧ profileY s<31/20 ∧
      (profileX s)^2+(profileY s)^2=qCap := by
  obtain ⟨hg0,hg1⟩ := positive_gain_bounds hs
  have hX : profileX s∈Icc (31/25 : ℝ) (3/2) := by
    dsimp [profileX]
    constructor <;> linarith
  have hX0 : 0≤profileX s := by linarith [hX.1]
  have hXu := pow_le_pow_left₀ hX0 hX.2 2
  have hXl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤31/25) hX.1 2
  have hrad : 0≤qCap-(profileX s)^2 := by dsimp [qCap]; linarith
  have hY2 : (profileY s)^2=qCap-(profileX s)^2 := Real.sq_sqrt hrad
  have hY0 : 0≤profileY s := Real.sqrt_nonneg _
  refine ⟨hX,?_,?_,by linarith⟩ <;> dsimp [qCap] at * <;> nlinarith

theorem weight_bounds {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    weight s∈Icc (4/5 : ℝ) 2 := by
  obtain ⟨hX,hYl,hYu,_⟩ := profile_bounds hs
  have hY : 0<profileY s := by linarith
  dsimp [weight]
  constructor
  · apply (le_div_iff₀ hY).2
    linarith [hX.1]
  · apply (div_le_iff₀ hY).2
    linarith [hX.2]

theorem polynomial_primary_lower {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    (31/25 : ℝ)≤Polynomial.aeval s EndpointBudgetPolynomial.primary := by
  have hs2 : s^2≤(1/2 : ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hS := mul_nonneg (pow_nonneg hs.1 3) (show 0≤20-s^2 by linarith)
  have hC := mul_nonneg (pow_nonneg hs.1 4) (show 0≤30-s^2 by linarith)
  rw [EndpointBudgetPolynomial.primary_eval]
  norm_num [EndpointBudgetPolynomial.kbar]
  nlinarith

theorem profile_polynomial_comparison {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    Polynomial.aeval s EndpointBudgetPolynomial.primary≤profileX s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hs0 := (transport_trig hs').2.2.1
  have hsin := sin_upper_five hs.1
  have hcos := cos_lower_six hs.1
  have hk : k0≤(EndpointBudgetPolynomial.kbar:ℝ) := by
    norm_num [EndpointBudgetPolynomial.kbar]
    exact radical_bounds.2.1.le
  have hm := mul_le_mul hk hsin hs0
    (by norm_num [EndpointBudgetPolynomial.kbar] : (0:ℝ)≤(EndpointBudgetPolynomial.kbar:ℝ))
  rw [EndpointBudgetPolynomial.primary_eval]
  dsimp [profileX,positiveGain]
  nlinarith

/-- The full short positive-span comparison, proved by a single
polynomial on the complete interval rather than local angle bounds. -/
theorem positive_short_profile {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    2*profileY s-1+S0-charge*s<2-epsilon := by
  have hp := EndpointBudgetPolynomial.real_certificate_positive hs
  have hXlo := polynomial_primary_lower hs
  have hXcmp := profile_polynomial_comparison hs
  have hpow := pow_le_pow_left₀ (show 0≤Polynomial.aeval s EndpointBudgetPolynomial.primary by
    linarith) hXcmp 2
  obtain ⟨_,hY,_,hcircle⟩ := profile_bounds hs
  let Z : ℝ := (3-(EndpointBudgetPolynomial.sbar:ℝ)-
    (EndpointBudgetPolynomial.reserve:ℝ))/2+(25/49)*s
  have hZ : 0<Z := by
    dsimp [Z,EndpointBudgetPolynomial.sbar,EndpointBudgetPolynomial.reserve]
    norm_num
    linarith [hs.1]
  have hsmall : profileY s<Z := by
    change (Polynomial.aeval s EndpointBudgetPolynomial.primary)^2+Z^2>
      (9789/2500 : ℝ) at hp
    dsimp [qCap] at hcircle
    nlinarith
  have hS := radical_bounds.2.2.1
  dsimp [Z,EndpointBudgetPolynomial.sbar,EndpointBudgetPolynomial.reserve,charge,epsilon] at *
  norm_num at *
  linarith

theorem optimized_stress_identity {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    baseline (weight s)+weight s*positiveGain s=2*profileY s-1 := by
  obtain ⟨hX,hY,_,hcircle⟩ := profile_bounds hs
  have hY0 : 0<profileY s := by linarith
  have hL : weight s*profileY s=profileX s := by
    dsimp [weight]
    field_simp [hY0.ne']
  have hL2 := congrArg (fun z : ℝ => z^2) hL
  have hN2 := congrArg (fun z : ℝ => z*(profileY s)^2) (zero_norm_sq (weight s))
  have hN0 : 0≤pairNorm (weight s) 1 0 := Real.sqrt_nonneg _
  have hYN : profileY s*pairNorm (weight s) 1 0=R := by
    have hn := mul_nonneg hY0.le hN0
    nlinarith [R_sq,R_nonneg]
  have hRNY : R*pairNorm (weight s) 1 0*profileY s=qCap := by
    calc
      R*pairNorm (weight s) 1 0*profileY s=R*(profileY s*pairNorm (weight s) 1 0) := by ring
      _=qCap := by rw [hYN]; simpa only [pow_two] using R_sq
  have hLXY : weight s*profileX s*profileY s=(profileX s)^2 := by
    nlinarith [congrArg (fun z : ℝ => profileX s*z) hL]
  have hgain : 3-positiveGain s=2*profileX s := by dsimp [profileX]; ring
  have hgain' := congrArg (fun z : ℝ => weight s*profileY s*z) hgain
  have he : (baseline (weight s)+weight s*positiveGain s-(2*profileY s-1))*profileY s=0 := by
    dsimp [baseline]
    linear_combination 2*hRNY-2*hLXY-2*hcircle-hgain'
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hY0.ne')

theorem positive_short {s : ℝ} (hs : s∈Icc 0 (1/2 : ℝ)) :
    baseline (weight s)+weight s*positiveGain s-charge*s+S0<2-epsilon := by
  rw [optimized_stress_identity hs]
  exact positive_short_profile hs

theorem positive_long {s : ℝ} (hs : s∈Icc (1/2 : ℝ) frameCap) :
    baseline (4/5)+(4/5)*((41/40)*s)-charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.2.2
  have hS := radical_bounds.2.2.2
  dsimp [baseline,charge,epsilon]
  linarith [hs.1]

theorem negative_short {s : ℝ} (hs : s∈Icc 0 (6/25 : ℝ)) :
    baseline (7/6)+(7/6)*negativeGain (183/200) s+charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.1
  have hS := radical_bounds.2.2.2
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(6/25 : ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hs3 := mul_le_mul_of_nonneg_right hs2 hs.1
  have hshort := mul_nonneg hs.1 (show 0≤6/25-s by linarith [hs.2])
  dsimp [baseline,negativeGain,K,charge,epsilon]
  nlinarith

/-- A single fixed weight suffices on the whole long negative span.
The trigonometric expression is concave after moving it to the left. -/
theorem negative_long {s : ℝ} (hs : s∈Icc (6/25 : ℝ) frameCap) :
    baseline (7/4)+(7/4)*negativeGain (4/5) s+charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.2.1
  have hS := radical_bounds.2.2.2
  have hsinL := sin_lower_seven (show (0:ℝ)≤6/25 by norm_num)
  have hcosL := cos_lower_six (show (0:ℝ)≤6/25 by norm_num)
  have hsinH := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hcosH := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [frameCap] at hsinL hcosL hsinH hcosH
  have htrig :
      2*(9971/2500 : ℝ)-3*(7/4)-1+(7/4)*(4/5)+52/125-2+epsilon<
        -charge*s+((7/4)*K)*Real.sin s+((7/4)*(4/5))*Real.cos s := by
    apply trig_concave_gt (by norm_num [K]) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hs
    · dsimp [K,charge,epsilon]
      linarith
    · dsimp [K,charge,epsilon,frameCap]
      linarith
  dsimp [baseline,negativeGain]
  linarith

end SquaresInCircles.Eight.TableFree.EndpointBudgetScalars
