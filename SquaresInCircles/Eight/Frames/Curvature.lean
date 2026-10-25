module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: whole-interval upper-curvature estimates for frame supports

These two elementary calculus consequences retain the complete interval.
The second is the chord bound with an explicit curvature loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCurvature

theorem upper_tangent {l u x t M : ℝ} {f d dd : ℝ → ℝ}
    (hx : x∈Icc l u) (ht : t∈Icc l u)
    (hd : ∀z∈Icc l u,HasDerivAt f (d z) z)
    (he : ∀z∈Icc l u,HasDerivAt d (dd z) z)
    (hM : ∀z∈Icc l u,dd z≤M) :
    f x≤f t+d t*(x-t)+M/2*(x-t)^2 := by
  have hh := curvature_tangent (f := fun z => -f z) (d := fun z => -d z)
    (dd := fun z => -dd z) (κ := -M) hx ht
    (fun z hz => (hd z hz).neg) (fun z hz => (he z hz).neg)
    (fun z hz => neg_le_neg (hM z hz))
  linarith

theorem lower_of_upper_curvature {l u x M m : ℝ} {f d dd : ℝ → ℝ}
    (hx : x∈Icc l u) (hM0 : 0≤M)
    (hd : ∀z∈Icc l u,HasDerivAt f (d z) z)
    (he : ∀z∈Icc l u,HasDerivAt d (dd z) z)
    (hM : ∀z∈Icc l u,dd z≤M) (hl : m<f l) (hu : m<f u) :
    m-M*(u-l)^2/8<f x := by
  let F : ℝ → ℝ := fun z => f z+M/2*(z-l)*(u-z)
  let D : ℝ → ℝ := fun z => d z+M/2*(u+l-2*z)
  have hF {z : ℝ} (hz : z∈Icc l u) : HasDerivAt F (D z) z := by
    have h := (hd z hz).fun_add ((((hasDerivAt_id' z).sub_const l).const_mul (M/2)).fun_mul
      ((hasDerivAt_id' z).const_sub u))
    convert h using 1
    simp only [D]
    ring
  have hD {z : ℝ} (hz : z∈Icc l u) : HasDerivAt D (dd z-M) z := by
    have h := (he z hz).fun_add
      ((((hasDerivAt_id' z).const_mul 2).const_sub (u+l)).const_mul (M/2))
    convert h using 1
    ring
  have hc : ConcaveOn ℝ (Icc l u) F := concave_of_deriv2
    (fun z hz => hF hz) (fun z hz => hD hz) (fun z hz => by linarith [hM z hz])
  have hpos : m<F x := concave_gt_of_endpoints hc hx
    (by simpa [F] using hl) (by simpa [F] using hu)
  have hquad : (x-l)*(u-x)≤(u-l)^2/4 := by nlinarith [sq_nonneg (2*x-l-u)]
  have hm := mul_le_mul_of_nonneg_left hquad hM0
  dsimp [F] at hpos
  linarith

theorem product_cage {s c sl su cl cu : ℝ}
    (hsl : 0≤ sl) (hcl : 0≤cl) (hs : sl≤ s ∧ s≤ su) (hc : cl≤c ∧ c≤cu) :
    sl^2≤ s^2 ∧ s^2≤ su^2 ∧ cl^2≤c^2 ∧ c^2≤cu^2 ∧ sl*cl≤ s*c ∧ s*c≤ su*cu := by
  have hs0 := hsl.trans hs.1
  have hc0 := hcl.trans hc.1
  exact ⟨pow_le_pow_left₀ hsl hs.1 2,pow_le_pow_left₀ hs0 hs.2 2,
    pow_le_pow_left₀ hcl hc.1 2,pow_le_pow_left₀ hc0 hc.2 2,
    mul_le_mul hs.1 hc.1 hcl hs0,mul_le_mul hs.2 hc.2 hc0 (hs0.trans hs.2)⟩

end SquaresInCircles.Eight.FrameCurvature
