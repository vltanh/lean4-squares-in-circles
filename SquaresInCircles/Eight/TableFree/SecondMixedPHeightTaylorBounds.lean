module

public import SquaresInCircles.Eight.TableFree.SecondMixedPHeightTaylor

/-!
# Whole-interval curvature bounds for the P height minorant

The endpoint-curve curvature is a cubic polynomial with negative
second derivative, so its two rational endpoint values give a uniform
positive bound. The core-coordinate growth comparison is decreasing
on its entire early height range. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.PHeightTaylor
open CommonQuarter CorePairGeometry Arithmetic PHeightBounds

def mass : ℝ := 112479/100000
def curvature (u : ℝ) : ℝ := d2 u*(mass-(u-1)^2)-d1 u*(u-1)
def curvatureD (u : ℝ) : ℝ := c3*(mass-(u-1)^2)-3*d2 u*(u-1)-d1 u
def curvatureDD (u : ℝ) : ℝ := -5*c3*(u-1)-4*d2 u

lemma d1_monotone : MonotoneOn d1 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (d1_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => d1_hasDerivAt u)
    (fun u hu => (d2_positive (Ioo_subset_Icc_self hu)).le)

lemma curvature_hasDerivAt (u : ℝ) : HasDerivAt curvature (curvatureD u) u := by
  have hJ := (((hasDerivAt_id u).sub_const 1).pow 2).const_sub mass
  convert ((d2_hasDerivAt u).mul hJ).sub
    ((d1_hasDerivAt u).mul ((hasDerivAt_id u).sub_const 1)) using 1 <;>
    dsimp [curvature,curvatureD] <;> ring

lemma curvatureD_hasDerivAt (u : ℝ) : HasDerivAt curvatureD (curvatureDD u) u := by
  have hJ := (((hasDerivAt_id u).sub_const 1).pow 2).const_sub mass
  convert ((hJ.const_mul c3).sub
    (((d2_hasDerivAt u).mul ((hasDerivAt_id u).sub_const 1)).const_mul 3)).sub
      (d1_hasDerivAt u) using 1 <;> dsimp [curvatureD,curvatureDD] <;> ring

theorem curvature_lower {u : ℝ} (hu : u∈Icc (133/100:ℝ) (17/10)) :
    (1/20:ℝ)<curvature u := by
  have hc : ConcaveOn ℝ (Icc (133/100:ℝ) (17/10)) curvature :=
    concave_of_deriv2 (fun u _ => curvature_hasDerivAt u)
      (fun u _ => curvatureD_hasDerivAt u)
      (fun u hu => by
        have hh := d2_positive (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
        dsimp [curvatureDD,c3]
        linarith [hu.1])
  exact concave_gt_of_endpoints hc hu
    (by norm_num [curvature,d1,d2,mass,r,c1,c2,c3])
    (by norm_num [curvature,d1,d2,mass,r,c1,c2,c3])

theorem early_growth {u : ℝ} (hu : u∈Icc (7/5:ℝ) (17/10)) :
    d2 u<(27/5)*d1 u-25869/6250 := by
  have hm : AntitoneOn (fun u => d2 u-(27/5)*d1 u) (Icc (7/5:ℝ) (17/10)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun u _ => ((d2_hasDerivAt u).sub ((d1_hasDerivAt u).const_mul (27/5))).continuousAt.continuousWithinAt)
      (fun u _ => (d2_hasDerivAt u).sub ((d1_hasDerivAt u).const_mul (27/5)))
    intro u hu
    dsimp [d2,c2,c3,r]
    linarith [hu.1]
  have hh := hm (show (7/5:ℝ)∈Icc (7/5:ℝ) (17/10) by norm_num) hu hu.1
  have hr : d2 (7/5)-(27/5)*d1 (7/5)< -(25869/6250:ℝ) := by
    norm_num [d1,d2,c1,c2,c3,r]
  linarith

lemma late_bounds {u : ℝ} (hu : u∈Icc (133/100:ℝ) (373/250)) :
    (909/1000:ℝ)<d1 u ∧ 0<d2 u ∧ d2 u<(61/50:ℝ) := by
  have hh := d1_monotone
    (show (133/100:ℝ)∈heights by norm_num [heights])
    (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩) hu.1
  have hr : (909/1000:ℝ)<d1 (133/100) := by norm_num [d1,c1,c2,c3,r]
  refine ⟨hr.trans_le hh,d2_positive ⟨by linarith [hu.1],by linarith [hu.2]⟩,?_⟩
  dsimp [d2,c2,c3,r]
  linarith [hu.2]

lemma terminal_bounds {u : ℝ} (hu : u∈Icc (6689/5000:ℝ) (701/500)) :
    (4581/5000:ℝ)<d1 u ∧ d2 u<(493/500:ℝ) := by
  have hh := d1_monotone
    (show (6689/5000:ℝ)∈heights by norm_num [heights])
    (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩) hu.1
  have hr : (4581/5000:ℝ)<d1 (6689/5000) := by norm_num [d1,c1,c2,c3,r]
  refine ⟨hr.trans_le hh,?_⟩
  dsimp [d2,c2,c3,r]
  linarith [hu.2]

end SquaresInCircles.Eight.TableFree.SecondWord.PHeightTaylor
