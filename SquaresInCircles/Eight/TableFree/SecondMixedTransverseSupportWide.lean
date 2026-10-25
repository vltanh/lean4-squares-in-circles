module

public import SquaresInCircles.Eight.TableFree.SecondMixedTransverseSupport

/-!
# Whole lower-half concavity for the wider mixed support slopes

The exact circular norm curvature bound remains sufficient when the
transverse coefficient is as large as .95 of the separator multiplier.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTransverseSupport
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma lower_domain_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    0<CircularNorm.energy (g^2+p^2) (-2*g*p) 0 φ := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (sub_nonneg.mpr (Real.cos_le_one φ))
  dsimp [CircularNorm.energy]
  nlinarith

lemma lower_sq_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    (lowerN g p φ)^2=g^2+p^2-2*g*p*Real.cos φ := by
  have h := CircularNorm.norm_sq (lower_domain_wide hg hp hpg φ).le
  simp only [lowerN]
  rw [h]
  simp only [CircularNorm.energy]
  ring

lemma lower_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (C φ : ℝ) :
    HasDerivAt (lower g p C) (lowerD g p φ) φ := by
  have h1 : HasDerivAt (fun y => y+C+(g+p)/2) 1 φ :=
    ((hasDerivAt_id' φ).add_const C).add_const ((g+p)/2)
  have h2 : HasDerivAt (fun y => g*Real.sin y) (g*Real.cos φ) φ :=
    (Real.hasDerivAt_sin φ).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*lowerN g p y)
      (CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.norm_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  unfold lowerD
  ring

lemma lowerD_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    HasDerivAt (lowerD g p) (lowerDD g p φ) φ := by
  have h1 : HasDerivAt (fun y => 1+g*Real.cos y) (g*(-Real.sin φ)) φ :=
    ((Real.hasDerivAt_cos φ).const_mul g).const_add 1
  have h2 : HasDerivAt (fun y => CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 y)
      (CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.d1_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul CommonQuarter.radius
  refine (h1.sub h2).congr_deriv ?_
  unfold lowerDD
  ring

lemma lower_curvature_wide {g p φ : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g)
    (hφ : Lower φ) : lowerDD g p φ<0 := by
  have ht := lower_trig hφ
  have hn := lower_sq_wide hg hp hpg φ
  have hNpos : 0<lowerN g p φ := CircularNorm.norm_pos (lower_domain_wide hg hp hpg φ)
  have hp2 := pow_le_pow_left₀ hp hpg 2
  have hcos := mul_nonneg (mul_nonneg hg.le hp) ht.2.2.1
  have hN : lowerN g p φ<(7/5)*g := by nlinarith
  have hc := CircularNorm.curvature_lower (lower_domain_wide hg hp hpg φ)
    (show (-2*g*p)^2+(0:ℝ)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(7/5)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.1.le hg.le
  change CommonQuarter.radius*(-lowerN g p φ/4)≤CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ at hcurv
  dsimp [lowerDD]
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTransverseSupport
