module

public import SquaresInCircles.Eight.TableFree.PositiveSplitComparison

/-!
# Calculus of a positive tilted primary and its outer anchor

Uncompiled source draft. The negative square term in the exact second
derivative is retained until the final upper estimate. This provides the
continuous split calculation in Section 9 of the complete core-E proof.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.PositiveSplitCalculus
open PositivePrimaryBaselines

def f (η t : ℝ) : ℝ := Real.cos t+η*Real.sin t
def df (η t : ℝ) : ℝ := -Real.sin t+η*Real.cos t
def beta (R η : ℝ) : ℝ := 1+2*η-R*Real.sqrt (1+η^2)
def radicand (r k η t : ℝ) : ℝ := r^2+(k*f η t)^2
def norm (r k η t : ℝ) : ℝ := Real.sqrt (radicand r k η t)
def normDeriv (r k η t : ℝ) : ℝ := (k*f η t)*(k*df η t)/norm r k η t
def normSecond (r k η t : ℝ) : ℝ :=
  r^2*(k*df η t)^2/(norm r k η t)^3-(k*f η t)^2/norm r k η t

def g (R r k η t : ℝ) : ℝ :=
  k*primaryCoefficient R η t-R*norm r k η t

def gDeriv (R r k η t : ℝ) : ℝ :=
  k*(-2*Real.sin t+beta R η*Real.cos t)-R*normDeriv r k η t

def gSecond (R r k η t : ℝ) : ℝ :=
  k*(-2*Real.cos t-beta R η*Real.sin t)-R*normSecond r k η t

theorem f_hasDerivAt (η t : ℝ) : HasDerivAt (f η) (df η t) t := by
  simpa [f,df] using (Real.hasDerivAt_cos t).add ((Real.hasDerivAt_sin t).const_mul η)

theorem df_hasDerivAt (η t : ℝ) : HasDerivAt (df η) (-f η t) t := by
  convert (Real.hasDerivAt_sin t).neg.add ((Real.hasDerivAt_cos t).const_mul η) using 1 <;>
    simp [f,df] <;> ring

theorem f_energy (η t : ℝ) : (f η t)^2+(df η t)^2=1+η^2 := by
  dsimp [f,df]
  linear_combination (1+η^2)*(Real.sin_sq_add_cos_sq t)

theorem radicand_pos {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    0<radicand r k η t := by unfold radicand; positivity

theorem norm_pos {r : ℝ} (hr : 0<r) (k η t : ℝ) : 0<norm r k η t :=
  Real.sqrt_pos.mpr (radicand_pos hr k η t)

theorem norm_sq {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    (norm r k η t)^2=radicand r k η t := Real.sq_sqrt (radicand_pos hr k η t).le

theorem norm_hasDerivAt {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    HasDerivAt (norm r k η) (normDeriv r k η t) t := by
  have h := ((hasDerivAt_const t (r^2)).add
    (((f_hasDerivAt η t).const_mul k).pow 2)).sqrt (radicand_pos hr k η t).ne'
  convert h using 1
  · rfl
  · dsimp [normDeriv,norm,radicand]
    ring

private theorem quotient_second_identity {r m v L : ℝ}
    (hL : L≠0) (hLsq : L^2=r^2+m^2) :
    ((v^2-m^2)*L-m*v*(m*v/L))/L^2=r^2*v^2/L^3-m^2/L := by
  field_simp [hL]
  nlinarith [congrArg (fun z : ℝ => v^2*z) hLsq]

theorem normDeriv_hasDerivAt {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    HasDerivAt (normDeriv r k η) (normSecond r k η t) t := by
  have hN := norm_pos hr k η t
  have hnum := ((f_hasDerivAt η t).const_mul k).mul
    ((df_hasDerivAt η t).const_mul k)
  have h := hnum.div (norm_hasDerivAt hr k η t) hN.ne'
  have hid := quotient_second_identity hN.ne' (norm_sq hr k η t)
  convert h using 1
  · rfl
  · dsimp [normSecond,normDeriv] at *
    convert hid.symm using 1 <;> ring

theorem g_hasDerivAt {r : ℝ} (hr : 0<r) (R k η t : ℝ) :
    HasDerivAt (g R r k η) (gDeriv R r k η t) t := by
  have hc := ((hasDerivAt_const t (1:ℝ)).add
    ((Real.hasDerivAt_cos t).const_mul 2)).add
    ((Real.hasDerivAt_sin t).const_mul (beta R η))
  convert (hc.const_mul k).sub ((norm_hasDerivAt hr k η t).const_mul R) using 1 <;>
    simp [g,gDeriv,primaryCoefficient,beta] <;> ring

theorem gDeriv_hasDerivAt {r : ℝ} (hr : 0<r) (R k η t : ℝ) :
    HasDerivAt (gDeriv R r k η) (gSecond R r k η t) t := by
  have hc := ((Real.hasDerivAt_sin t).const_mul (-2)).add
    ((Real.hasDerivAt_cos t).const_mul (beta R η))
  convert (hc.const_mul k).sub ((normDeriv_hasDerivAt hr k η t).const_mul R) using 1 <;>
    simp [gDeriv,gSecond] <;> ring

/-- The only discarded term is an explicit nonnegative square. -/
theorem gSecond_le {R r k η t a c : ℝ}
    (hR : 0≤R) (hr : 0<r) (hk : 0≤k) (hη : 0≤η)
    (hcos : 0≤Real.cos t) (hsin : 0≤Real.sin t)
    (hratio : R*(k*f η t)/norm r k η t≤a)
    (hbeta : R*Real.sqrt (1+η^2)-1+(a-2)*η≤c) :
    gSecond R r k η t≤k*((a-2)*Real.cos t+c*Real.sin t) := by
  have hN := norm_pos hr k η t
  have hf : 0≤f η t := add_nonneg hcos (mul_nonneg hη hsin)
  have hm := mul_nonneg hk hf
  have hsupport := mul_le_mul_of_nonneg_right hratio hm
  have hcoef := mul_le_mul_of_nonneg_left hbeta (mul_nonneg hk hsin)
  have hterm : 0≤R*(r^2*(k*df η t)^2/(norm r k η t)^3) := by positivity
  have hid : R*((k*f η t)^2/norm r k η t)=
      (R*(k*f η t)/norm r k η t)*(k*f η t) := by ring
  unfold gSecond normSecond
  simp only [mul_sub]
  rw [hid]
  dsimp [f,beta] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.PositiveSplitCalculus
