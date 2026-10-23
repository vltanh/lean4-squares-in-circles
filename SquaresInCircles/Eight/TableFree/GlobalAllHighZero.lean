module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighZeroNonpositive

/-!
# Complete original zero-owner rows and their shared variation budget

The actual original owner-0 sign implication is retained.  Every
original error, source sign, core piece, and target outer chart is
covered.  At most one of three zeros may use the loss range because
their total positive variation is less than `7/10`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair GlobalOuterAnchor

/-- A row for each original weak zero witness.  The only owner sign
premise is precisely the implication supplied by the established
global original zero-owner classifier. -/
theorem zero_charge (s t : State) (htOuter : t.branch.type≠0)
    (ht : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=0 ∨ j=2) (hd : |d|≤frameCap)
    (hm : s.Feasible t j d) (hsource : j=0 → 0<transverse s) :
    gammaZero-7/1000<zeroCharge s t d ∧
      ((d≤7/20 ∨ 0≤transverse s ∨ t.branch≠.high) → gammaZero≤zeroCharge s t d) := by
  have hproj : width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      width d≤s.a*Real.sin d+transverse s*Real.cos d+t.b := by
    rcases hj with rfl | rfl
    · left
      have hh := (left_margin s t false hd ht).1 (by
        simpa only [leftOwner,Bool.false_eq_true,if_false] using hm)
      exact hh
    · right
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,if_true] using hm)
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
    have hm2 : width d≤s.a*Real.sin d+transverse s*Real.cos d+t.b := by
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,if_true,hj2] using hm)
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

/-- The three-source theorem has only original states, actual weak
witnesses, their proved owner sign implication, and the real variation
cap as input.  It supplies the common cyclic zero component directly. -/
theorem three_zero_charge (s t : Fin 3→State) (j : Fin 3→Fin 4) (d : Fin 3→ℝ)
    (htOuter : ∀i,(t i).branch.type≠0) (ht : ∀i,transverse (t i)≤0)
    (hj : ∀i,j i=0 ∨ j i=2) (hd : ∀i,|d i|≤frameCap)
    (hm : ∀i,(s i).Feasible (t i) (j i) (d i))
    (hsource : ∀i,j i=0 → 0<transverse (s i))
    (hvariation : ∑i,max (d i) 0<frameCap) :
    3*gammaZero-7/1000<∑i,zeroCharge (s i) (t i) (d i) := by
  have hc (i : Fin 3) := zero_charge (s i) (t i) (htOuter i) (ht i)
    (hj i) (hd i) (hm i) (hsource i)
  have hvar : max (d 0) 0+max (d 1) 0+max (d 2) 0<frameCap := by
    simpa [Fin.sum_univ_succ,add_assoc] using hvariation
  have hh := three_zero_charge_bound hvar
    ⟨(hc 0).1,fun hz => (hc 0).2 (Or.inl hz)⟩
    ⟨(hc 1).1,fun hz => (hc 1).2 (Or.inl hz)⟩
    ⟨(hc 2).1,fun hz => (hc 2).2 (Or.inl hz)⟩
  simpa [Fin.sum_univ_succ,add_assoc] using hh

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
