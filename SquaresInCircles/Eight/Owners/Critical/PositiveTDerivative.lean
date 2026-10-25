module

public import SquaresInCircles.Eight.Owners.Critical.EExclusion
public import SquaresInCircles.Eight.Owners.Critical.PositiveTScalar

/-!
# Eight squares: strict growth from the original hard-chain zero

The supporting chain is the exact minimizing
position at q,t. At z=0 the scalar is the previously proved sharp
endpoint; on the entire triangle its derivative exceeds 9/5000.
Neither the exact zero nor the original stationary radius is perturbed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTDerivative
open Stationary.FiveCornerGeometry ExceptionalContactStress ExceptionalContactSupport
open CriticalPositiveTCoefficients

def k (q t z : ℝ) : ℝ := adaptedK (CriticalEExclusion.K q t) z
def ell (q t z : ℝ) : ℝ := adaptedL (CriticalEExclusion.L q t) z
def c (q t z : ℝ) : ℝ := adaptedC (CriticalEExclusion.Cc q t) z
def eta (q t : ℝ) : ℝ := CriticalEExclusion.Eta q t
def p (q t z : ℝ) : ℝ := tilt (eta q t) (t-z)
def m (q t z : ℝ) : ℝ := c q t z*tilt (eta q t) z

def scalar (q t z : ℝ) : ℝ :=
  CriticalPositiveTScalar.scalar (Real.sqrt q) (CriticalEExclusion.K q t)
    (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) (eta q t) t z
def slope (q t z : ℝ) : ℝ :=
  CriticalPositiveTScalar.slope (Real.sqrt q) (CriticalEExclusion.K q t)
    (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) (eta q t) t z

theorem scalar_formula (q t z : ℝ) :
    scalar q t z=3*k q t z+2*ell q t z+c q t z*contactScalar (Real.sqrt q) (eta q t) z+
      contactScalar (Real.sqrt q) (eta q t) (t-z)+m q t z*(Real.cos t-1)-
      Real.sqrt q*(Real.sqrt (p q t z^2+k q t z^2)+Real.sqrt (k q t z^2+ell q t z^2)+
        Real.sqrt (ell q t z^2+m q t z^2-2*ell q t z*m q t z*Real.sin t)+
        Real.sqrt (1+c q t z^2)) := rfl

theorem coefficients {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    Bounds t z (k q t z) (ell q t z) (c q t z) (m q t z) (eta q t) :=
  adapted_bounds (CriticalEExclusion.coefficient_bounds hq ht) hz

theorem hasDerivAt_scalar {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    HasDerivAt (scalar q t) (slope q t z) z :=
  CriticalPositiveTScalar.hasDerivAt_scalar (CriticalEExclusion.coefficient_bounds hq ht) hz

theorem slope_lower {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) : 9/5000<slope q t z := by
  have h := CriticalPositiveTModel.minimizing_derivative_lower hq ht hz
  rw [CriticalPositiveTScalar.model_value] at h
  exact h

theorem deriv_lower {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    9/5000<deriv (scalar q t) z := by
  rw [(hasDerivAt_scalar hq ht hz).deriv]
  exact slope_lower hq ht hz

/-- Exact cancellation of the unshifted B norm at the hard endpoint. -/
theorem scalar_zero (q t : ℝ) :
    scalar q t 0=atE (Real.sqrt q) (CriticalEExclusion.K q t) (CriticalEExclusion.L q t)
      (CriticalEExclusion.Cc q t) (eta q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt q) (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) t := by
  simp only [scalar,CriticalPositiveTScalar.scalar,CriticalPositiveTScalar.p,
    CriticalPositiveTScalar.hSquare,CriticalPositiveTScalar.aSquare,CriticalPositiveTScalar.bSquare,
    CriticalPositiveTScalar.dSquare,adaptedK,adaptedL,adaptedC,adaptedM,tilt,
    atE,contactScalar,OrdinaryAngleConcavity.V,PositiveAngularEnvelope.pairNorm,
    Real.sin_zero,Real.cos_zero,Real.sin_neg,mul_zero,sub_zero,add_zero,mul_one,one_pow]
  ring

theorem scalar_zero_nonneg {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0≤ scalar d.q t 0 := by
  rw [scalar_zero]
  exact (CriticalEExclusion.scalar_endpoints hd hq ht).1

/-- The strict derivative inequality is used on the full interval.
The endpoint itself is still the exact supporting-chain scalar. -/
theorem scalar_growth {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Ioc 0 t) :
    scalar q t 0+(9/5000)*z<scalar q t z := by
  have hc : ContinuousOn (scalar q t) (Icc 0 t) := by
    intro s hs
    exact (hasDerivAt_scalar hq ht hs).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (scalar q t) (interior (Icc 0 t)) := by
    intro s hs
    exact (hasDerivAt_scalar hq ht (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hl : ∀s∈interior (Icc 0 t),(9/5000:ℝ)<deriv (scalar q t) s := by
    intro s hs
    exact deriv_lower hq ht (interior_subset hs)
  have h := (convex_Icc (0:ℝ) t).mul_sub_lt_image_sub_of_lt_deriv hc hd hl
    0 (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,by linarith [ht.1]⟩)
    z (Ioc_subset_Icc_self hz) hz.1
  linarith

theorem scalar_pos_of_z_pos {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Ioc 0 t) :
    (9/5000)*z<scalar d.q t z := by
  have h0 := scalar_zero_nonneg hd hq ht
  have h := scalar_growth hq ht hz
  linarith

theorem scalar_nonneg {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) : 0≤ scalar d.q t z := by
  rcases eq_or_lt_of_le hz.1 with hzero | hpos
  · subst z
    exact scalar_zero_nonneg hd hq ht
  · have h := scalar_pos_of_z_pos hd hq ht ⟨hpos,hz.2⟩
    nlinarith

end SquaresInCircles.Eight.CriticalPositiveTDerivative
