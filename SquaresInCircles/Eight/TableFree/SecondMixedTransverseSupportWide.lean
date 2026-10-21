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
  simpa [lowerN,CircularNorm.energy] using CircularNorm.norm_sq (lower_domain_wide hg hp hpg φ).le

lemma lower_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (C φ : ℝ) :
    HasDerivAt (lower g p C) (lowerD g p φ) φ := by
  convert ((((hasDerivAt_id φ).add_const C).add_const ((g+p)/2)).add
    ((Real.hasDerivAt_sin φ).const_mul g)).sub
      ((CircularNorm.norm_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul radius) using 1 <;>
    dsimp [lower,lowerD,lowerN] <;> ring

lemma lowerD_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    HasDerivAt (lowerD g p) (lowerDD g p φ) φ := by
  convert (((Real.hasDerivAt_cos φ).const_mul g).const_add 1).sub
    ((CircularNorm.d1_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul radius) using 1 <;>
    dsimp [lowerD,lowerDD] <;> ring

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
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(7/5)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.1.le hg.le
  change radius*(-lowerN g p φ/4)≤radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ at hcurv
  dsimp [lowerDD]
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTransverseSupport
