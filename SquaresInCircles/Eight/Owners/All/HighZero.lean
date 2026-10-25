module

public import SquaresInCircles.Eight.Owners.All.HighZeroNegative
public import SquaresInCircles.Eight.Owners.All.HighZeroNonpositive

/-!
# Eight squares: the zero edges and their shared variation budget

A weak witness of owner `0` or `2` on a zero edge into an outer target with nonpositive transverse
coordinate makes the zero charge exceed `gammaZero - 7/1000`, and reach `gammaZero` unless the
error exceeds `7/20` on a high target from a source with negative transverse coordinate
(`zero_charge`). This covers every error, source sign, core piece and outer chart of the target.
At most one of three zero edges can use that loss range, since their positive variations add up
to less than `7/10` (`three_zero_charge_bound`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair GlobalOuterAnchor

/-- The zero charge of a weak witness of owner `0` or `2`. The only sign premise, that owner `0`
has a source with positive transverse coordinate, is the implication given by the sign
classification of the zero owners. -/
theorem zero_charge (s t : State) (htOuter : t.branch.type≠0)
    (ht : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=0 ∨ j=2) (hd : |d|≤frameCap)
    (hm : s.Feasible t j d) (hsource : j=0 → 0<transverse s) :
    gammaZero-7/1000<zeroCharge s t d ∧
      ((d≤7/20 ∨ 0≤transverse s ∨ t.branch≠.high) → gammaZero≤zeroCharge s t d) := by
  have hproj : GlobalOuterAnchor.width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      GlobalOuterAnchor.width d≤ s.a*Real.sin d+transverse s*Real.cos d+t.b := by
    rcases hj with rfl | rfl
    · left
      have hh := (left_margin s t false hd ht).1 (by
        simpa only [leftOwner,Bool.false_eq_true,ite_false] using hm)
      exact hh
    · right
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,ite_true] using hm)
      exact hh
  by_cases hy : 0≤transverse s
  · have hc := zero_nonnegative_source s t htOuter hy hd hproj
    exact ⟨by linarith,fun _ => hc⟩
  · have hs : transverse s≤0 := (lt_of_not_ge hy).le
    have hj2 : j=2 := by
      rcases hj with hj | hj
      · exact (hy (hsource hj).le).elim
      · exact hj
    have hdpos : 0<d := by
      by_contra! hdn
      exact hy (zero_nonpositive_error_source s t hd hdn hproj).le
    have hm2 : GlobalOuterAnchor.width d≤ s.a*Real.sin d+transverse s*Real.cos d+t.b := by
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,ite_true,hj2] using hm)
      exact hh
    have hc := nonpositive_zero_charge s t htOuter hs
      ⟨hdpos.le,(le_abs_self d).trans hd⟩ hm2
    refine ⟨hc.1,?_⟩
    rintro (hshort | hpositive | hlower)
    · exact hc.2 (Or.inl hshort)
    · exact (hy hpositive).elim
    · exact hc.2 (Or.inr hlower)

theorem three_zero_charge_bound {d₀ d₁ d₂ C₀ C₁ C₂ : ℝ}
    (hvariation : max d₀ 0+max d₁ 0+max d₂ 0<frameCap)
    (h₀ : gammaZero-7/1000<C₀ ∧ (d₀≤7/20 → gammaZero≤C₀))
    (h₁ : gammaZero-7/1000<C₁ ∧ (d₁≤7/20 → gammaZero≤C₁))
    (h₂ : gammaZero-7/1000<C₂ ∧ (d₂≤7/20 → gammaZero≤C₂)) :
    3*gammaZero-7/1000<C₀+C₁+C₂ := by
  by_cases hd₀ : d₀≤7/20
  · by_cases hd₁ : d₁≤7/20
    · linarith [h₀.2 hd₀,h₁.2 hd₁,h₂.1]
    · have hbad₁ : (7/20:ℝ)<d₁ := lt_of_not_ge hd₁
      have hd₂ : d₂≤7/20 := by
        by_contra! hn
        dsimp [frameCap] at hvariation
        linarith [le_max_right d₀ 0,le_max_left d₁ 0,le_max_left d₂ 0]
      linarith [h₀.2 hd₀,h₁.1,h₂.2 hd₂]
  · have hbad₀ : (7/20:ℝ)<d₀ := lt_of_not_ge hd₀
    have hd₁ : d₁≤7/20 := by
      by_contra! hn
      dsimp [frameCap] at hvariation
      linarith [le_max_left d₀ 0,le_max_left d₁ 0,le_max_right d₂ 0]
    have hd₂ : d₂≤7/20 := by
      by_contra! hn
      dsimp [frameCap] at hvariation
      linarith [le_max_left d₀ 0,le_max_right d₁ 0,le_max_left d₂ 0]
    linarith [h₀.1,h₁.2 hd₁,h₂.2 hd₂]

end SquaresInCircles.Eight.GlobalAllHigh
