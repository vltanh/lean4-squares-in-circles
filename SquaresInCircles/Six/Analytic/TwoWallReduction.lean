import SquaresInCircles.Six.Analytic.FixedPairGap

/-!
# Concavity with two prescribed walls

An interval cut at 0 and k has at most four pieces. At a point x the containing
piece has endpoints chosen by max/min from the original endpoints and those
two walls. Concavity reduces the lower-bound question to those endpoints.
The cuts are supplied by the geometry, not chosen by a numerical search.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair

lemma max_choice (a b : ℝ) : max a b=a ∨ max a b=b := by
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

lemma min_choice (a b : ℝ) : min a b=a ∨ min a b=b := by
  rcases le_total a b with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

lemma nonneg_on_concave_interval {l r x : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Icc l r) f) (hx : l≤x ∧ x≤r)
    (hl : 0≤f l) (hr : 0≤f r) : 0≤f x :=
  (le_min hl hr).trans (hf.min_le_of_mem_Icc
    (Set.left_mem_Icc.mpr (hx.1.trans hx.2))
    (Set.right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

lemma hasSign_neg {p : Bool} {x : ℝ} (hx : HasSign p x) : HasSign (!p) (-x) := by
  cases p <;> simp only [HasSign,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    ite_false,ite_true] at * <;> linarith

lemma exists_hasSign (x : ℝ) : ∃ p : Bool, HasSign p x := by
  by_cases h : 0≤x
  · exact ⟨true,h⟩
  · exact ⟨false,(lt_of_not_ge h).le⟩

/-- No point of [l,r] is missed, including either wall and both outer endpoints. -/
theorem two_wall_nonnegative {l r k x : ℝ} {f : ℝ → ℝ}
    (hx : l≤x ∧ x≤r)
    (hconc : ∀ p q : Bool, ∀ a b : ℝ,
      (∀ y ∈ Set.Icc a b, (l≤y ∧ y≤r) ∧ HasSign p y ∧ HasSign q (y-k)) →
      ConcaveOn ℝ (Set.Icc a b) f)
    (hboundary : ∀ y, (l≤y ∧ y≤r) →
      (y=l ∨ y=r ∨ y=0 ∨ y=k) → 0≤f y) : 0≤f x := by
  by_cases hx0 : 0≤x
  · by_cases hxk : k≤x
    · let a := max l (max 0 k)
      have hax : a≤x := max_le hx.1 (max_le hx0 hxk)
      have hla : l≤a := le_max_left _ _
      have h0a : 0≤a := (le_max_left 0 k).trans (le_max_right _ _)
      have hka : k≤a := (le_max_right 0 k).trans (le_max_right _ _)
      have hf := hconc true true a r (fun y hy =>
        ⟨⟨hla.trans hy.1,hy.2⟩,h0a.trans hy.1,by dsimp [HasSign]; linarith [hy.1]⟩)
      apply nonneg_on_concave_interval hf ⟨hax,hx.2⟩
      · apply hboundary a ⟨hla,hax.trans hx.2⟩
        rcases max_choice l (max 0 k) with h | h
        · exact Or.inl h
        · rcases max_choice 0 k with h0 | hk
          · exact Or.inr (Or.inr (Or.inl (h.trans h0)))
          · exact Or.inr (Or.inr (Or.inr (h.trans hk)))
      · exact hboundary r ⟨hx.1.trans hx.2,le_rfl⟩ (Or.inr (Or.inl rfl))
    · let a := max l 0
      let b := min r k
      have hax : a≤x := max_le hx.1 hx0
      have hxb : x≤b := le_min hx.2 (le_of_not_ge hxk)
      have hla : l≤a := le_max_left _ _
      have hbr : b≤r := min_le_left _ _
      have h0a : 0≤a := le_max_right _ _
      have hbk : b≤k := min_le_right _ _
      have hf := hconc true false a b (fun y hy =>
        ⟨⟨hla.trans hy.1,hy.2.trans hbr⟩,h0a.trans hy.1,
          by dsimp [HasSign]; linarith [hy.2]⟩)
      apply nonneg_on_concave_interval hf ⟨hax,hxb⟩
      · apply hboundary a ⟨hla,hax.trans hx.2⟩
        rcases max_choice l 0 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · apply hboundary b ⟨hx.1.trans hxb,hbr⟩
        rcases min_choice r k with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
  · by_cases hxk : k≤x
    · let a := max l k
      let b := min r 0
      have hax : a≤x := max_le hx.1 hxk
      have hxb : x≤b := le_min hx.2 (le_of_not_ge hx0)
      have hla : l≤a := le_max_left _ _
      have hbr : b≤r := min_le_left _ _
      have hka : k≤a := le_max_right _ _
      have hb0 : b≤0 := min_le_right _ _
      have hf := hconc false true a b (fun y hy =>
        ⟨⟨hla.trans hy.1,hy.2.trans hbr⟩,hy.2.trans hb0,
          by dsimp [HasSign]; linarith [hy.1]⟩)
      apply nonneg_on_concave_interval hf ⟨hax,hxb⟩
      · apply hboundary a ⟨hla,hax.trans hx.2⟩
        rcases max_choice l k with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
      · apply hboundary b ⟨hx.1.trans hxb,hbr⟩
        rcases min_choice r 0 with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · let b := min r (min 0 k)
      have hxb : x≤b := le_min hx.2 (le_min (le_of_not_ge hx0) (le_of_not_ge hxk))
      have hbr : b≤r := min_le_left _ _
      have hb0 : b≤0 := (min_le_right _ _).trans (min_le_left 0 k)
      have hbk : b≤k := (min_le_right _ _).trans (min_le_right 0 k)
      have hf := hconc false false l b (fun y hy =>
        ⟨⟨hy.1,hy.2.trans hbr⟩,hy.2.trans hb0,
          by dsimp [HasSign]; linarith [hy.2]⟩)
      apply nonneg_on_concave_interval hf ⟨hx.1,hxb⟩
      · exact hboundary l ⟨le_rfl,hx.1.trans hx.2⟩ (Or.inl rfl)
      · apply hboundary b ⟨hx.1.trans hxb,hbr⟩
        rcases min_choice r (min 0 k) with h | h
        · exact Or.inr (Or.inl h)
        · rcases min_choice 0 k with h0 | hk
          · exact Or.inr (Or.inr (Or.inl (h.trans h0)))
          · exact Or.inr (Or.inr (Or.inr (h.trans hk)))

end SquaresInCircles.Six.Analytic.FixedPair
