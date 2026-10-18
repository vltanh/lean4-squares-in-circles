module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import SquaresInCircles.Eight.ExactFamily.EnvelopeUniqueness

/-!
# Scalar implicit roots and envelope derivatives

The implicit function theorem constructs a local root of an actual
equation. Uniqueness in an open position window identifies that root
with an independently chosen minimizing position. No continuity of the
chosen minimizer is assumed. The derivative formulas below follow by
differentiating the equation and the actual objective.

These general calculus lemmas do not supply the geometric hypotheses
for the five-corner family. Those must be proved at the application.
This Lean source remains uncompiled.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.EnvelopeGeometry

open Set Filter
open scoped Topology ContDiff

def pairDerivative (dt du : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  dt • ContinuousLinearMap.fst ℝ ℝ ℝ+du • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem pairDerivative_apply (dt du : ℝ) (v : ℝ × ℝ) :
    pairDerivative dt du v=dt*v.1+du*v.2 := by
  simp [pairDerivative,smul_eq_mul]

/-- Identify the two-variable differential from the actual two partial
derivatives. Joint differentiability is an explicit hypothesis. -/
theorem pair_hasFDerivAt {H : ℝ × ℝ → ℝ} {t u dt du : ℝ}
    (hH : DifferentiableAt ℝ H (t,u))
    (ht : HasDerivAt (fun x => H (x,u)) dt t)
    (hu : HasDerivAt (fun y => H (t,y)) du u) :
    HasFDerivAt H (pairDerivative dt du) (t,u) := by
  have h₁ := hH.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))
  have h₂ := hH.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u t).prodMk (hasDerivAt_id u))
  have hdt : fderiv ℝ H (t,u) (1,0)=dt := h₁.unique ht
  have hdu : fderiv ℝ H (t,u) (0,1)=du := h₂.unique hu
  have he : fderiv ℝ H (t,u)=pairDerivative dt du := by
    ext v
    have hv : v=v.1 • ((1,0):ℝ × ℝ)+v.2 • ((0,1):ℝ × ℝ) := by
      ext <;> simp
    calc
      fderiv ℝ H (t,u) v =
          fderiv ℝ H (t,u) (v.1 • ((1,0):ℝ × ℝ)+v.2 • ((0,1):ℝ × ℝ)) := by rw [← hv]
      _ = v.1*dt+v.2*du := by rw [map_add,map_smul,map_smul,hdt,hdu]; rfl
      _ = pairDerivative dt du v := by simp; ring
  rw [← he]
  exact hH.hasFDerivAt

theorem pairDerivative_position_invertible {dt du : ℝ} (hu : du≠0) :
    ((pairDerivative dt du).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1/du) • ContinuousLinearMap.id ℝ ℝ)
  · ext y
    simp [ContinuousLinearMap.comp_apply,smul_eq_mul]
    field_simp [hu]
  · ext y
    simp [ContinuousLinearMap.comp_apply,smul_eq_mul]
    field_simp [hu]

/-- The local implicit root equals any chosen root which is unique in
the open position window. This proves regularity of a chosen minimizer
without assuming its continuity in advance. -/
theorem contDiffAt_of_unique_root {G : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t : ℝ} {W : Set ℝ} {dt du : ℝ}
    (hG : ContDiffAt ℝ 2 G (t,g t))
    (hd : HasFDerivAt G (pairDerivative dt du) (t,g t)) (hdu : du≠0)
    (hW : IsOpen W) (hmem : g t∈W) (hzero : G (t,g t)=0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ y∈W, G (x,y)=0 → y=g x) :
    ContDiffAt ℝ 2 g t := by
  have hn : (2:ℕ∞ω)≠0 := by norm_num
  have hinv : (fderiv ℝ G (t,g t) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hd.fderiv]
    exact pairDerivative_position_invertible hdu
  let ψ : ℝ → ℝ := hG.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ 2 ψ t := hG.contDiffAt_implicitFunction hn hinv
  have hψself : ψ t=g t := hG.implicitFunction_apply_self hn hinv
  have hψroot : ∀ᶠ x in 𝓝 t, G (x,ψ x)=0 := by
    simpa only [hzero] using hG.eventually_apply_implicitFunction hn hinv
  have hψmem : ∀ᶠ x in 𝓝 t, ψ x∈W :=
    hψ.continuousAt.eventually (hW.mem_nhds (by rw [hψself]; exact hmem))
  have he : g =ᶠ[𝓝 t] ψ := by
    filter_upwards [hψroot,hψmem,hunique] with x hx hm hu
    exact (hu (ψ x) hm hx).symm
  exact hψ.congr_of_eventuallyEq he

/-- Differentiating an actual root equation gives its slope. -/
theorem implicit_root_derivative {G : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t dt du : ℝ} (hg : DifferentiableAt ℝ g t)
    (hG : HasFDerivAt G (pairDerivative dt du) (t,g t)) (hdu : du≠0)
    (hzero : ∀ᶠ x in 𝓝 t, G (x,g x)=0) :
    HasDerivAt g (-dt/du) t := by
  have hcomp := hG.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hg.hasDerivAt)
  have hcomp' : HasDerivAt (fun x => G (x,g x)) (dt+du*deriv g t) t := by
    simpa using hcomp
  have hconst : HasDerivAt (fun x => G (x,g x)) 0 t :=
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hzero
  have he : dt+du*deriv g t=0 := hcomp'.unique hconst
  have hslope : deriv g t= -dt/du := by
    apply (eq_div_iff hdu).2
    nlinarith
  simpa only [hslope] using hg.hasDerivAt

/-- The position derivative vanishes at the minimum, leaving the actual
tilt partial as the derivative of the envelope. -/
theorem envelope_first_derivative {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t dt dg : ℝ} (hg : HasDerivAt g dg t)
    (hF : HasFDerivAt F (pairDerivative dt 0) (t,g t)) :
    HasDerivAt (fun x => F (x,g x)) dt t := by
  simpa using hF.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hg)

/-- The Schur complement is obtained by differentiating the actual tilt
partial along the actual implicit root. This lemma supplies only the
calculus identity; positivity comes from the geometric Hessian proof. -/
theorem envelope_tilt_derivative {T : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    {t tt tu uu : ℝ} (hg : HasDerivAt g (-tu/uu) t)
    (hT : HasFDerivAt T (pairDerivative tt tu) (t,g t)) :
    HasDerivAt (fun x => T (x,g x)) (tt-tu^2/uu) t := by
  have hh := hT.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hg)
  convert hh using 1 <;> simp only [pairDerivative_apply,mul_one] <;> ring

theorem schur_positive {tt tu uu : ℝ} (huu : 0<uu) (hdet : 0<uu*tt-tu^2) :
    0<tt-tu^2/uu := by
  have hh := (div_lt_iff₀ huu).mpr (show tu^2<tt*uu by nlinarith)
  linarith

end SquaresInCircles.Eight.ExactFamily.EnvelopeGeometry
