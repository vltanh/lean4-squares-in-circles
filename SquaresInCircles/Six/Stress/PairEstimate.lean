import SquaresInCircles.Six.Stress.PairEstimate.Curvature
import SquaresInCircles.Six.Stress.PairEstimate.Vertices

/-!
# Six squares: the pair estimate

On its domain the value of the pair N, W is at least
`pairBase + line w + |n|/1000`, and at zero angles it is `pairBase` only for the
two facets of the contact of the model. The gap, the value less this bound, is
concave on every segment of a line in `n`, in `w` or along the diagonal `n = w`
that stays in one sign sector (`gap_sweep_concave`), and nonnegative at the
corners and axis points of the domain and where the diagonal meets them
(`gap_vertices`). A segment in `n` reaches a side, the axis `n = 0` or the
diagonal; a segment in `w` from there reaches the corner and axis points or the
diagonal; and the diagonal, cut at the origin, ends at the listed points. So the
gap is nonnegative everywhere.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress.Pair

lemma exists_hasSign (x : ℝ) : ∃ p : Bool, HasSign p x := by
  by_cases h : 0≤x
  · exact ⟨true,h⟩
  · exact ⟨false,(lt_of_not_ge h).le⟩

lemma hasSign_neg {p : Bool} {x : ℝ} (hx : HasSign p x) : HasSign (!p) (-x) := by
  cases p <;> simp only [HasSign,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,
    ite_true] at hx ⊢ <;> linarith

/-- A function concave on each piece of `[l, r]` on which `y` and `y - k` keep their
signs is nonnegative on `[l, r]` once it is nonnegative at `l`, `r`, `0` and `k`. -/
lemma two_wall_nonneg {f : ℝ → ℝ} {l r k x : ℝ} (hx : l≤x ∧ x≤r)
    (hconc : ∀ p q : Bool, ∀ a b, (∀ y ∈ Set.Icc a b,
      (l≤y ∧ y≤r) ∧ HasSign p y ∧ HasSign q (y-k)) → ConcaveOn ℝ (Set.Icc a b) f)
    (hpts : ∀ y, (l≤y ∧ y≤r) → (y=l ∨ y=r ∨ y=0 ∨ y=k) → 0≤f y) : 0≤f x := by
  classical
  set a := max l (max (if 0≤x then 0 else l) (if k≤x then k else l)) with ha_def
  set b := min r (min (if 0≤x then r else 0) (if k≤x then r else k)) with hb_def
  have hax : a≤x := max_le hx.1 (max_le (by split_ifs <;> linarith) (by split_ifs <;> linarith))
  have hxb : x≤b := le_min hx.2 (le_min (by split_ifs <;> linarith) (by split_ifs <;> linarith))
  have hla : l≤a := le_max_left _ _
  have hbr : b≤r := min_le_left _ _
  have hf := hconc (decide (0≤x)) (decide (k≤x)) a b fun y hy => by
    refine ⟨⟨hla.trans hy.1,hy.2.trans hbr⟩,?_,?_⟩
    · by_cases h : 0≤x <;> simp only [HasSign,h,decide_true,decide_false,ite_true,
        Bool.false_eq_true,ite_false]
      · have : (0:ℝ)≤a := le_trans (by simp [h]) ((le_max_left _ _).trans (le_max_right l _))
        linarith [hy.1]
      · have : b≤0 := ((min_le_right _ _).trans (min_le_left _ _)).trans (by simp [h])
        linarith [hy.2]
    · by_cases h : k≤x <;> simp only [HasSign,h,decide_true,decide_false,ite_true,
        Bool.false_eq_true,ite_false]
      · have : k≤a := le_trans (by simp [h]) ((le_max_right _ _).trans (le_max_right l _))
        linarith [hy.1]
      · have : b≤k := ((min_le_right _ _).trans (min_le_right _ _)).trans (by simp [h])
        linarith [hy.2]
  have ha : 0≤f a := hpts a ⟨hla,hax.trans hx.2⟩ (by
    rw [ha_def]
    rcases max_choice l (max (if 0≤x then (0:ℝ) else l) (if k≤x then k else l)) with h | h <;>
      rw [h]
    · exact Or.inl rfl
    · rcases max_choice (if 0≤x then (0:ℝ) else l) (if k≤x then k else l) with h' | h' <;>
        rw [h'] <;> split_ifs <;> simp)
  have hb : 0≤f b := hpts b ⟨hx.1.trans hxb,hbr⟩ (by
    rw [hb_def]
    rcases min_choice r (min (if 0≤x then r else (0:ℝ)) (if k≤x then r else k)) with h | h <;>
      rw [h]
    · exact Or.inr (Or.inl rfl)
    · rcases min_choice (if 0≤x then r else (0:ℝ)) (if k≤x then r else k) with h' | h' <;>
        rw [h'] <;> split_ifs <;> simp)
  exact (le_min ha hb).trans (hf.min_le_of_mem_Icc (Set.left_mem_Icc.mpr (hax.trans hxb))
    (Set.right_mem_Icc.mpr (hax.trans hxb)) ⟨hax,hxb⟩)

/-- A function on a rectangle containing the origin, concave on every segment of
a line in one sign sector, is nonnegative once it is nonnegative at the corner and
axis points and at the points `max nl wl`, `min nr wr` and `0` of the diagonal. -/
theorem rectangle_nonneg {g : ℝ → ℝ → ℝ} {nl nr wl wr : ℝ}
    (hconc : ∀ pn pw pq : Bool, ∀ k : Sweep, ∀ n w l r : ℝ,
      (∀ x ∈ Set.Icc l r,
        (nl≤k.n n w x ∧ k.n n w x≤nr) ∧ (wl≤k.w n w x ∧ k.w n w x≤wr)) →
      (∀ x ∈ Set.Icc l r, Sector pn pw pq (k.n n w x) (k.w n w x)) →
      ConcaveOn ℝ (Set.Icc l r) (fun x => g (k.n n w x) (k.w n w x)))
    (hcorner : ∀ x y, (x=nl ∨ x=nr ∨ x=0) → (y=wl ∨ y=wr ∨ y=0) → 0≤g x y)
    (hdiag : ∀ z, (z=max nl wl ∨ z=min nr wr ∨ z=0) → 0≤g z z)
    {n w : ℝ} (hn : nl≤n ∧ n≤nr) (hw : wl≤w ∧ w≤wr) : 0≤g n w := by
  have hdline (z : ℝ) (hzn : nl≤z ∧ z≤nr) (hzw : wl≤z ∧ z≤wr) : 0≤g z z := by
    apply two_wall_nonneg (f := fun z => g z z) (k := 0)
      ⟨max_le hzn.1 hzw.1,le_min hzn.2 hzw.2⟩
    · intro p q a b hseg
      exact hconc p q true .diagonal 0 0 a b
        (fun x hx => ⟨⟨(le_max_left _ _).trans (hseg x hx).1.1,(hseg x hx).1.2.trans
          (min_le_left _ _)⟩,⟨(le_max_right _ _).trans (hseg x hx).1.1,(hseg x hx).1.2.trans
          (min_le_right _ _)⟩⟩)
        (fun x hx => ⟨(hseg x hx).2.1,by simpa [Sweep.w] using (hseg x hx).2.2,
          by simp [Sweep.n,Sweep.w,HasSign]⟩)
    · intro y _ hy
      rcases hy with rfl | rfl | rfl | rfl
      exacts [hdiag _ (Or.inl rfl),hdiag _ (Or.inr (Or.inl rfl)),hdiag _ (Or.inr (Or.inr rfl)),
        hdiag _ (Or.inr (Or.inr rfl))]
  have hvline (v : ℝ) (hv : v=nl ∨ v=nr ∨ v=0) (hvn : nl≤v ∧ v≤nr) (y : ℝ)
      (hy : wl≤y ∧ y≤wr) : 0≤g v y := by
    obtain ⟨pn,hpn⟩ := exists_hasSign v
    apply two_wall_nonneg (f := fun y => g v y) (k := v) hy
    · intro p q a b hseg
      exact hconc pn p (!q) .west v 0 a b (fun x hx => ⟨hvn,(hseg x hx).1⟩)
        (fun x hx => ⟨hpn,(hseg x hx).2.1,
          by simpa [Sweep.n,Sweep.w] using hasSign_neg (hseg x hx).2.2⟩)
    · intro y hy hcut
      rcases hcut with rfl | rfl | rfl | rfl
      exacts [hcorner _ _ hv (Or.inl rfl),hcorner _ _ hv (Or.inr (Or.inl rfl)),
        hcorner _ _ hv (Or.inr (Or.inr rfl)),hdline _ hvn hy]
  obtain ⟨pw,hpw⟩ := exists_hasSign w
  apply two_wall_nonneg (f := fun x => g x w) (k := w) hn
  · intro p q a b hseg
    exact hconc p pw q .north 0 w a b (fun x hx => ⟨(hseg x hx).1,hw⟩)
      (fun x hx => ⟨(hseg x hx).2.1,hpw,(hseg x hx).2.2⟩)
  · intro x hx hcut
    rcases hcut with rfl | rfl | rfl | rfl
    exacts [hvline _ (Or.inl rfl) hx w hw,hvline _ (Or.inr (Or.inl rfl)) hx w hw,
      hvline _ (Or.inr (Or.inr rfl)) hx w hw,hdline _ hx hw]

/-- On the domain the value of the pair is at least `pairBase + line w + |n|/1000`. -/
theorem lower_bound {no wo : Bool} (f : Facet) {n w : ℝ} (hd : Domain no wo n w) :
    pairBase+line w+|n|/1000≤value no wo f n w := by
  have h := rectangle_nonneg (g := gap no wo f)
    (fun pn pw pq k n w l r hrect hs => gap_sweep_concave f k hrect hs)
    (gap_vertices no wo f).1 (gap_vertices no wo f).2 hd.1 hd.2
  simp only [gap] at h
  linarith

/-- At zero angles the value is `pairBase` only for the facets of the model. -/
theorem model_of_value_origin {no wo : Bool} {f : Facet} (he : value no wo f 0 0=pairBase) :
    f.model=true := by
  by_contra hf
  have := (gap_origin no wo f).2 (by simpa using hf)
  simp only [gap,he] at this
  norm_num [line] at this

end SquaresInCircles.Six.Stress.Pair
