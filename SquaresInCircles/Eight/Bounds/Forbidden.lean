module

public import SquaresInCircles.Eight.Bounds.Forbidden.Analytic

/-!
# The two forbidden intervals of the central square

Both bounds follow from supporting points and radial projection. Shallow depths
use a few elementary supports; larger depths use a circular arc. The remaining
middle range is controlled by an angle derivative for the narrower rectangle
and a linear supporting direction for the wider one.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.CentralForbidden

theorem bandA_forbidden {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (347/200) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (11/12) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  by_cases hsmall : d ≤ 1/12
  · simpa only [L] using Analytic.bandA_small_depth ⟨hd.1,hsmall⟩
  by_cases hlarge : c ≤ d
  · simpa only [L] using Analytic.bandA_large_depth ⟨hlarge,hd.2⟩
  simpa only [L] using Analytic.bandA_middle_depth
    ⟨(lt_of_not_ge hsmall).le,(lt_of_not_ge hlarge).le⟩


theorem bandB_forbidden {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (899/500) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (19/20) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d :=
  Analytic.bandB_forbidden hd

end SquaresInCircles.Eight.CentralForbidden
