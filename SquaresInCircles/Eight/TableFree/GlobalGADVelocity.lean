module

public import SquaresInCircles.Eight.TableFree.GlobalGARadicals

/-!
# The full signed D-support derivative reserve

Uncompiled translation of Section 5 of the secondary-owner four-circle
exclusion.  The key comparison covers the whole interval by an explicit
positive-coefficient polynomial.  It supplies the derivative bound at
the actual interior-circle support, including cancellation between
the two original signed D arguments.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope PairNormCalculus

def dVelocity (s : ℝ) : ℝ := R*normD1 1 2 s
def dCancellation (s : ℝ) : ℝ := dVelocity s-Real.sin (frameCap-s)
def dCancellationD (s : ℝ) : ℝ :=
  R*normD2 1 2 s+Real.cos (frameCap-s)
def dCancellationDD (s : ℝ) : ℝ :=
  R*normD3 1 2 s+Real.sin (frameCap-s)

theorem dNorm_sq {s : ℝ} (hs : |s|≤frameCap) :
    (pairNorm 1 2 s)^2=5+4*Real.sin s := by
  simpa [pairEnergy,pairProduct] using
    pairNorm_sq (p:=1) (q:=2) (by norm_num) (by norm_num) hs

theorem dNorm_zero_upper : pairNorm 1 2 0<(2237/1000:ℝ) := by
  have h := dNorm_sq (s:=0) (by norm_num [frameCap])
  norm_num at h
  nlinarith [Real.sqrt_nonneg ((1:ℝ)^2+2^2+2*1*2*Real.sin 0)]

theorem dNorm_cap_upper : pairNorm 1 2 frameCap<(1377/500:ℝ) := by
  have h := dNorm_sq (s:=frameCap) (by norm_num [frameCap])
  have ht := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  nlinarith [Real.sqrt_nonneg ((1:ℝ)^2+2^2+2*1*2*Real.sin frameCap)]

theorem dVelocity_zero_lower : charge+Real.sin frameCap<dVelocity 0 := by
  have hN := pairNorm_pos (p:=1) (q:=2) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hs := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  have hm := mul_le_mul
    (show charge+Real.sin frameCap≤charge+6443/10000 by linarith)
    dNorm_zero_upper.le hN.le (by norm_num [charge])
  have he : dVelocity 0=2*R/pairNorm 1 2 0 := by
    simp [dVelocity,normD1,pairProduct]
    ring
  rw [he,lt_div_iff₀ hN]
  norm_num [charge] at hm ⊢
  linarith [radius_bounds.1]

theorem dVelocity_cap_lower : charge<dVelocity frameCap := by
  have hN := pairNorm_pos (p:=1) (q:=2) (t:=frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  obtain ⟨hc,_,_,_,_⟩ := transport_trig (x:=frameCap) (by norm_num [frameCap])
  have hm := mul_le_mul radius_bounds.1.le hc.le
    (by norm_num : (0:ℝ)≤7648/10000) (Real.sqrt_nonneg qCap)
  have hn := mul_lt_mul_of_pos_left dNorm_cap_upper (by norm_num : (0:ℝ)<charge)
  have he : dVelocity frameCap=2*R*Real.cos frameCap/pairNorm 1 2 frameCap := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he,lt_div_iff₀ hN]
  norm_num [charge] at hn ⊢
  nlinarith

/-- The velocity is no smaller than its aligned value on the entire
negative half.  The square comparison retains the original signed sine. -/
theorem dVelocity_negative_lower {s : ℝ} (hs : s∈Icc (-frameCap) 0) :
    dVelocity 0≤dVelocity s := by
  have hsi : |s|≤frameCap := abs_le.mpr
    ⟨hs.1,hs.2.trans (by norm_num [frameCap])⟩
  have hN := pairNorm_pos (p:=1) (q:=2) (by norm_num) (by norm_num) hsi
  have hN0 := pairNorm_pos (p:=1) (q:=2) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hsq := dNorm_sq hsi
  have hsq0 := dNorm_sq (s:=0) (by norm_num [frameCap])
  norm_num at hsq0
  have hn : -s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have ht := transport_trig hn
  have hsin : -(6443/10000:ℝ)<Real.sin s ∧ Real.sin s≤0 := by
    have he := Real.sin_neg s
    constructor <;> linarith [ht.2.2.1,ht.2.2.2.1]
  have hp : 0≤ -Real.sin s*(5*Real.sin s+4) :=
    mul_nonneg (by linarith [hsin.2]) (by linarith [hsin.1])
  have hc := transport_cos_pos hsi
  have hcomp : pairNorm 1 2 s≤pairNorm 1 2 0*Real.cos s := by
    have he : (pairNorm 1 2 0*Real.cos s)^2-(pairNorm 1 2 s)^2=
        -Real.sin s*(5*Real.sin s+4) := by
      rw [mul_pow,hsq0,hsq]
      nlinarith [Real.sin_sq_add_cos_sq s]
    nlinarith [mul_pos hN0 hc]
  have hmul := mul_le_mul_of_nonneg_left hcomp
    (show 0≤2*R by positivity)
  have he (x : ℝ) : dVelocity x=2*R*Real.cos x/pairNorm 1 2 x := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he 0,he s,Real.cos_zero,mul_one,div_le_div_iff₀ hN0 hN]
  nlinarith only [hmul]

/-- A positive-coefficient identity gives the strict second-derivative
reserve without locating any internal angular event. -/
theorem dVelocity_curvature_reserve {s : ℝ} (hs : s∈Icc 0 frameCap) :
    frameCap-s< -R*normD3 1 2 s := by
  have hsi : |s|≤frameCap := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hN := pairNorm_pos (p:=1) (q:=2) (by norm_num) (by norm_num) hsi
  have hsq := dNorm_sq hsi
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsin := Real.sin_ge_sub_cube hs.1
  have hsinup := Real.sin_le hs.1
  obtain ⟨hc,_,hsin0,_,_⟩ := transport_trig hs
  have hs2 : s^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 2
  have hs3 : s^3≤(7/10:ℝ)^3 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 3
  have hC0 : 0≤1-s^2/2 := by nlinarith
  have hP0 : 0≤13+10*s-(5/3)*s^3 := by nlinarith
  have hP : 13+10*s-(5/3)*s^3≤13+10*Real.sin s+4*(Real.sin s)^2 := by
    nlinarith [sq_nonneg (Real.sin s)]
  have hCP := mul_le_mul hcos hP hP0 (by linarith : 0≤Real.cos s)
  have hR : (197/50:ℝ)≤2*R := by linarith [radius_bounds.1]
  have hRmul := mul_le_mul_of_nonneg_right hR
    (mul_nonneg (by linarith : 0≤Real.cos s)
      (show 0≤13+10*Real.sin s+4*(Real.sin s)^2 by positivity))
  have hCPmul := mul_le_mul_of_nonneg_left hCP (by norm_num : (0:ℝ)≤197/50)
  have hnum : (197/50)*(1-s^2/2)*(13+10*s-(5/3)*s^3)≤
      2*R*Real.cos s*(13+10*Real.sin s+4*(Real.sin s)^2) := by
    nlinarith only [hRmul,hCPmul]
  have hNu : pairNorm 1 2 s<14/5 := by
    dsimp [frameCap] at hs
    nlinarith
  have hrad : 5+4*Real.sin s≤5+4*s := by linarith
  have hrad0 : 0≤5+4*Real.sin s := by positivity
  have hp2 := pow_le_pow_left₀ hrad0 hrad 2
  have hpow := mul_le_mul hNu.le hp2 (sq_nonneg _) (by norm_num : (0:ℝ)≤14/5)
  have hN5 : (pairNorm 1 2 s)^5=pairNorm 1 2 s*(5+4*Real.sin s)^2 := by
    rw [show (pairNorm 1 2 s)^5=pairNorm 1 2 s*((pairNorm 1 2 s)^2)^2 by ring,hsq]
  have hden : (pairNorm 1 2 s)^5≤(14/5)*(5+4*s)^2 := by
    rw [hN5]
    exact hpow
  have hdenmul := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hs.2)
  have hid : (197/50)*(1-s^2/2)*(13+10*s-(5/3)*s^3)-
      (14/5)*(5+4*s)^2*(frameCap-s)=
      111/50+31*s+(5503/100)*s^2+(278/15)*s^3+(197/60)*s^5 := by
    dsimp [frameCap]
    ring
  have hp : 0<(197/50)*(1-s^2/2)*(13+10*s-(5/3)*s^3)-
      (14/5)*(5+4*s)^2*(frameCap-s) := by
    rw [hid]
    positivity
  have he : -R*normD3 1 2 s=
      (2*R*Real.cos s*(13+10*Real.sin s+4*(Real.sin s)^2))/(pairNorm 1 2 s)^5 := by
    norm_num [normD3,pairEnergy,pairProduct]
    ring
  rw [he,lt_div_iff₀ (pow_pos hN 5)]
  nlinarith only [hnum,hdenmul,hp]

theorem dCancellation_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellation (dCancellationD s) s := by
  have hn := (normD1_hasDerivAt (p:=1) (q:=2) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_sin (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  convert hn.sub ht using 1 <;>
    dsimp [dCancellation,dVelocity,dCancellationD] <;> ring

theorem dCancellationD_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellationD (dCancellationDD s) s := by
  have hn := (normD2_hasDerivAt (p:=1) (q:=2) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_cos (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  convert hn.add ht using 1 <;>
    dsimp [dCancellationD,dCancellationDD] <;> ring

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

/-- The actual signed cancellation constraint is retained: `s+w` is
the original other D argument, so it is at most the full frame cap. -/
theorem dVelocity_sine_lower {s w : ℝ}
    (hs : s∈Icc (-frameCap) frameCap) (hw : w∈Icc 0 frameCap)
    (hsw : s+w≤frameCap) : charge<dVelocity s-Real.sin w := by
  by_cases hs0 : s≤0
  · have hv := dVelocity_negative_lower ⟨hs.1,hs0⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hw.2
    linarith [dVelocity_zero_lower]
  · have hs0' : 0≤s := (lt_of_not_ge hs0).le
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap] at hs; linarith [hs0',Real.pi_gt_three])
      (show w≤frameCap-s by linarith)
    have hh := dCancellation_lower ⟨hs0',hs.2⟩
    dsimp [dCancellation] at hh
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
