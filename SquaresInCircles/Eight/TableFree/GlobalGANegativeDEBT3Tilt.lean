module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Data
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# The total-dependent high tilt on the complete interval

Uncompiled coefficient geometry for equations (25)--(26). Multiplying
the half-angle inequality by its positive sine gives the equivalent
harmonic inequality cos(theta)+eta(theta) sin(theta)>=1. Its exact second
derivative is negative, so its two intrinsic endpoint values suffice.
The fixed-total split then uses ordinary harmonic concavity. No sampled
angle interval or coefficient hypothesis is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Arithmetic
open SecondWord.ReferenceTrig

def highFactor (θ : ℝ) : ℝ := Real.cos θ+eta .high θ*Real.sin θ
def highFactorD (θ : ℝ) : ℝ :=
  -(8649/10000)*Real.sin θ+eta .high θ*Real.cos θ
def highFactorDD (θ : ℝ) : ℝ :=
  -(3649/5000)*Real.cos θ-eta .high θ*Real.sin θ

theorem high_eta {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (293/1000:ℝ)≤eta .high θ ∧ eta .high θ<(183/500:ℝ) := by
  dsimp [eta,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_eta_derivative (θ : ℝ) : HasDerivAt (eta .high) (1351/10000) θ := by
  have h : HasDerivAt (fun x : ℝ => 293/1000+(1351/10000)*(x-L)) ((1351/10000)*1) θ :=
    ((hasDerivAt_id' θ).sub_const L).const_mul (1351/10000) |>.const_add (293/1000)
  have he : eta .high=fun x : ℝ => 293/1000+(1351/10000)*(x-L) := by
    funext x
    rfl
  rw [he]
  simpa using h

theorem highFactor_hasDerivAt (θ : ℝ) : HasDerivAt highFactor (highFactorD θ) θ := by
  have h := (Real.hasDerivAt_cos θ).add ((high_eta_derivative θ).mul (Real.hasDerivAt_sin θ))
  unfold highFactor
  exact h.congr_deriv (by dsimp [highFactorD]; ring)

theorem highFactorD_hasDerivAt (θ : ℝ) : HasDerivAt highFactorD (highFactorDD θ) θ := by
  have h := ((Real.hasDerivAt_sin θ).const_mul (-(8649/10000:ℝ))).add
    ((high_eta_derivative θ).mul (Real.hasDerivAt_cos θ))
  unfold highFactorD
  exact h.congr_deriv (by dsimp [highFactorDD]; ring)

theorem highFactor_concave : ConcaveOn ℝ (Icc (1/6:ℝ) (7/10)) highFactor := by
  apply concave_of_deriv2 (fun θ _ => highFactor_hasDerivAt θ)
    (fun θ _ => highFactorD_hasDerivAt θ)
  intro θ hθ
  have ht := transport_trig (show θ∈Icc 0 frameCap from
    ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩)
  have hp := mul_nonneg (show 0≤eta .high θ by linarith [(high_eta hθ).1]) ht.2.2.1
  dsimp [highFactorDD]
  linarith [ht.1]

theorem highFactor_left : 1≤highFactor (1/6) := by
  have hh := PositiveTD.Explicit.low_factor (show (1/6:ℝ)∈Icc 0 (1/6) by norm_num)
  simpa [highFactor,eta,L,PositiveTD.eta] using hh.1

theorem highFactor_right : 1<highFactor (7/10) := by
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos10,cos8] at hs hc
  dsimp [highFactor,eta,L]
  linarith

theorem highFactor_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : 1≤highFactor θ := by
  have hh := highFactor_concave.min_le_of_mem_Icc
    (show (1/6:ℝ)∈Icc (1/6) (7/10) by norm_num)
    (show (7/10:ℝ)∈Icc (1/6) (7/10) by norm_num) hθ
  exact (le_min highFactor_left highFactor_right.le).trans hh

theorem fixed_factor_concave {θ e : ℝ} (hθ : θ∈Icc 0 frameCap) (he : 0≤e) :
    ConcaveOn ℝ (Icc 0 θ) (fun z => Real.cos z+e*Real.sin z) := by
  apply concave_of_deriv2
    (fun z _ => by
      convert (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul e) using 1 <;> ring)
    (fun z _ => by
      convert (Real.hasDerivAt_sin z).neg.add ((Real.hasDerivAt_cos z).const_mul e) using 1 <;> ring)
  intro z hz
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1,hz.2.trans hθ.2⟩)
  have hp := mul_nonneg he ht.2.2.1
  linarith [ht.1]

theorem high_factor_lower {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) : 1≤Real.cos z+eta .high θ*Real.sin z := by
  have htf := frame_domain .high hθ
  have hc := fixed_factor_concave htf (show 0≤eta .high θ by linarith [(high_eta hθ).1])
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,htf.1⟩ ⟨htf.1,le_rfl⟩ hz
  have he := highFactor_lower hθ
  norm_num only [Real.sin_zero,Real.cos_zero,mul_zero,add_zero] at hh
  dsimp [highFactor] at he
  simpa only [min_eq_left he] using hh

theorem high_factor_upper {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos z+eta .high θ*Real.sin z<(213/200:ℝ) := by
  have he := high_eta hθ
  have he2 := pow_le_pow_left₀ (show 0≤eta .high θ by linarith [he.1]) he.2.le 2
  have hid : (Real.cos z+eta .high θ*Real.sin z)^2+
      (Real.sin z-eta .high θ*Real.cos z)^2=1+(eta .high θ)^2 := by
    linear_combination (1+(eta .high θ)^2)*(Real.sin_sq_add_cos_sq z)
  nlinarith [sq_nonneg (Real.sin z-eta .high θ*Real.cos z)]

theorem sigma_upper {e : ℝ} (he : e∈Icc (293/1000:ℝ) (183/500)) :
    fullSupport 1 e<(57/40:ℝ) := by
  have hR := Real.sqrt_nonneg qCap
  have hN := Real.sqrt_nonneg (1+e^2)
  have hN2 := Real.sq_sqrt (show 0≤1+e^2 by positivity)
  have hprod := mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr he.2)
  have htarget : 0<57/40+(1+e)/2 := by linarith [he.1]
  have hsq : (R*Real.sqrt (1+e^2))^2<(57/40+(1+e)/2)^2 := by
    rw [mul_pow,radius_sq,hN2]
    norm_num [qCap]
    nlinarith
  have hh : R*Real.sqrt (1+e^2)<57/40+(1+e)/2 := by
    nlinarith [mul_nonneg hR hN]
  simpa [fullSupport] using (show R*Real.sqrt (1+e^2)-(1+e)/2<57/40 by linarith)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Explicit
