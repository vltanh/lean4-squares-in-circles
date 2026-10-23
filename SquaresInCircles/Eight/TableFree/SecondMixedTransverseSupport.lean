module

public import SquaresInCircles.Eight.TableFree.SecondMixedAffineScalars
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Whole-half concavity of mixed transverse circle supports

The support slope may exceed the source label slope.  This freedom is
useful at an early contact: the remaining nonnegative source coordinate
pays for the stronger separator.  Both scalar supports below retain
their unsquared circular norm on a complete closed quarter half.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTransverseSupport
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig)

def lowerN (g p φ : ℝ) : ℝ := CircularNorm.norm (g^2+p^2) (-2*g*p) 0 φ
def lower (g p C φ : ℝ) : ℝ := φ+C+(g+p)/2+g*Real.sin φ-radius*lowerN g p φ
def lowerD (g p φ : ℝ) : ℝ := 1+g*Real.cos φ-
  radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 φ
def lowerDD (g p φ : ℝ) : ℝ := -g*Real.sin φ-
  radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ
def upperN (g p x : ℝ) : ℝ := CircularNorm.norm (g^2+p^2) 0 (2*g*p) x
def upper (g p C x : ℝ) : ℝ := Real.pi/2+x+C+(g+p)/2+
  g*(Real.sin x+Real.cos x)-radius*upperN g p x
def upperD (g p x : ℝ) : ℝ := 1+g*(Real.cos x-Real.sin x)-
  radius*CircularNorm.d1 (g^2+p^2) 0 (2*g*p) x
def upperDD (g p x : ℝ) : ℝ := -g*(Real.sin x+Real.cos x)-
  radius*CircularNorm.d2 (g^2+p^2) 0 (2*g*p) x

lemma lower_domain {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    0<CircularNorm.energy (g^2+p^2) (-2*g*p) 0 φ := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (sub_nonneg.mpr (Real.cos_le_one φ))
  dsimp [CircularNorm.energy]
  nlinarith

lemma upper_domain {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    0<CircularNorm.energy (g^2+p^2) 0 (2*g*p) x := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (show 0≤1+Real.sin x by linarith [Real.neg_one_le_sin x])
  dsimp [CircularNorm.energy]
  nlinarith

lemma lower_sq {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    (lowerN g p φ)^2=g^2+p^2-2*g*p*Real.cos φ := by
  simpa [lowerN,CircularNorm.energy] using CircularNorm.norm_sq (lower_domain hg hp hpg φ).le

lemma upper_sq {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    (upperN g p x)^2=g^2+p^2+2*g*p*Real.sin x := by
  simpa [upperN,CircularNorm.energy] using CircularNorm.norm_sq (upper_domain hg hp hpg x).le

lemma lower_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C φ : ℝ) :
    HasDerivAt (lower g p C) (lowerD g p φ) φ := by
  convert ((((hasDerivAt_id φ).add_const C).add_const ((g+p)/2)).add
    ((Real.hasDerivAt_sin φ).const_mul g)).sub
      ((CircularNorm.norm_hasDerivAt (lower_domain hg hp hpg φ)).const_mul radius) using 1 <;>
    dsimp [lower,lowerD,lowerN] <;> ring

lemma lowerD_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    HasDerivAt (lowerD g p) (lowerDD g p φ) φ := by
  convert (((Real.hasDerivAt_cos φ).const_mul g).const_add 1).sub
    ((CircularNorm.d1_hasDerivAt (lower_domain hg hp hpg φ)).const_mul radius) using 1 <;>
    dsimp [lowerD,lowerDD] <;> ring

lemma upper_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C x : ℝ) :
    HasDerivAt (upper g p C) (upperD g p x) x := by
  convert (((((hasDerivAt_id x).const_add (Real.pi/2)).add_const C).add_const ((g+p)/2)).add
    (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).const_mul g)).sub
      ((CircularNorm.norm_hasDerivAt (upper_domain hg hp hpg x)).const_mul radius) using 1 <;>
    dsimp [upper,upperD,upperN] <;> ring

lemma upperD_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    HasDerivAt (upperD g p) (upperDD g p x) x := by
  convert ((((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul g).const_add 1).sub
    ((CircularNorm.d1_hasDerivAt (upper_domain hg hp hpg x)).const_mul radius) using 1 <;>
    dsimp [upperD,upperDD] <;> ring

lemma lower_curvature {g p φ : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g)
    (hφ : Lower φ) : lowerDD g p φ<0 := by
  have ht := lower_trig hφ
  have hn := lower_sq hg hp hpg φ
  have hNpos : 0<lowerN g p φ := CircularNorm.norm_pos (lower_domain hg hp hpg φ)
  have hp2 := pow_le_pow_left₀ hp hpg 2
  have hcos := mul_nonneg (mul_nonneg hg.le hp) ht.2.2.1
  have hN : lowerN g p φ<(13/10)*g := by nlinarith
  have hc := CircularNorm.curvature_lower (lower_domain hg hp hpg φ)
    (show (-2*g*p)^2+(0:ℝ)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(13/10)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.1.le hg.le
  change radius*(-lowerN g p φ/4)≤radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ at hcurv
  dsimp [lowerDD]
  nlinarith

lemma upper_curvature {g p x : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g)
    (hx : x∈Icc (0:ℝ) (7/10)) : upperDD g p x<0 := by
  have ht := positive_trig hx
  have hn := upper_sq hg hp hpg x
  have hNpos : 0<upperN g p x := CircularNorm.norm_pos (upper_domain hg hp hpg x)
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one x) (mul_nonneg hg.le hp)
  have hN : upperN g p x≤g+p := by nlinarith
  have hc := CircularNorm.curvature_lower (upper_domain hg hp hpg x)
    (show (0:ℝ)^2+(2*g*p)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_le_mul_of_nonneg_left (hN.trans (by linarith : g+p≤(9/5)*g)) hR.le).trans_lt
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(9/5)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.2.2.2.2.2 hg.le
  change radius*(-upperN g p x/4)≤radius*CircularNorm.d2 (g^2+p^2) 0 (2*g*p) x at hcurv
  dsimp [upperDD]
  nlinarith

theorem lower_concave {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C : ℝ) :
    ConcaveOn ℝ (Icc lowerAngle (Real.pi/2)) (lower g p C) :=
  concave_of_deriv2 (fun x _ => lower_hasDerivAt hg hp hpg C x)
    (fun x _ => lowerD_hasDerivAt hg hp hpg x)
    (fun _ hx => (lower_curvature hg hp hpg hx).le)

theorem upper_concave {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C : ℝ) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (upper g p C) :=
  concave_of_deriv2 (fun x _ => upper_hasDerivAt hg hp hpg C x)
    (fun x _ => upperD_hasDerivAt hg hp hpg x)
    (fun _ hx => (upper_curvature hg hp hpg hx).le)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTransverseSupport
