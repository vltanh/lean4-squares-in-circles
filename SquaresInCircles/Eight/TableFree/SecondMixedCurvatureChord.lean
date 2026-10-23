module

public import SquaresInCircles.Eight.TableFree.SecondMixedPHeightTaylorBounds

/-!
# An exact endpoint loss from an upper curvature bound

Subtracting the endpoint-vanishing quadratic produces a concave
function. Its two endpoint values and one square completion bound the
whole closed interval. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

theorem curvature_chord_lower {f d dd : ℝ→ℝ} {l u x κ m : ℝ}
    (hx : x∈Icc l u) (hκ : 0≤κ)
    (hf : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hd : ∀t∈Icc l u,HasDerivAt d (dd t) t)
    (hdd : ∀t∈Icc l u,dd t≤κ) (hl : m<f l) (hu : m<f u) :
    m-κ*(u-l)^2/8<f x := by
  let g : ℝ→ℝ := fun t => f t-(κ/2)*(t-l)*(t-u)
  let gd : ℝ→ℝ := fun t => d t-(κ/2)*(2*t-l-u)
  have hg {t : ℝ} (ht : t∈Icc l u) : HasDerivAt g (gd t) t := by
    convert (hf t ht).sub
      ((((hasDerivAt_id t).sub_const l).mul ((hasDerivAt_id t).sub_const u)).const_mul (κ/2))
      using 1 <;> dsimp [g,gd] <;> ring
  have hgd {t : ℝ} (ht : t∈Icc l u) : HasDerivAt gd (dd t-κ) t := by
    convert (hd t ht).sub
      (((((hasDerivAt_id t).const_mul 2).sub_const l).sub_const u).const_mul (κ/2))
      using 1 <;> dsimp [gd] <;> ring
  have hc : ConcaveOn ℝ (Icc l u) g := concave_of_deriv2
    (fun _ ht => hg ht) (fun _ ht => hgd ht) (fun t ht => sub_nonpos.mpr (hdd t ht))
  have hh := concave_gt_of_endpoints hc hx
    (show m<g l by simpa [g] using hl) (show m<g u by simpa [g] using hu)
  have hp := mul_nonneg hκ (sq_nonneg (2*x-l-u))
  dsimp [g] at hh
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord
