import SquaresInCircles.Six.Analytic.TwoWallReduction

/-!
# A rectangle cut by `n = 0`, `w = 0` and `n = w`

Let `f` be concave in `n`, in `w`, and along the diagonal `n = w`, on every
segment of a rectangle on which the signs of `n`, `w` and `n - w` are fixed.
Then `f ≥ 0` on the rectangle once it holds at the points whose coordinates are
both ends of the rectangle or `0`, and at the points of the diagonal with one
such coordinate: a segment in `n` reaches a side, the axis `n = 0` or the
diagonal, and a segment in `w` or along the diagonal reaches the listed points.
The angles `n` of N and `w` of W lie in such a rectangle, so the gap of the
fixed pair is nonnegative once it is nonnegative at these points.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair

def AxisBoundary (l r x : ℝ) : Prop := x=l ∨ x=0 ∨ x=r

def InRectangle (nl nr wl wr n w : ℝ) : Prop :=
  (nl≤n ∧ n≤nr) ∧ (wl≤w ∧ w≤wr)

def SectorSliceConcave (f : ℝ → ℝ → ℝ) (nl nr wl wr : ℝ) : Prop :=
  ∀ pn pw pq : Bool, ∀ k : Fin 3, ∀ n w l r : ℝ,
    (∀ x ∈ Set.Icc l r, InRectangle nl nr wl wr (sliceN k n w x) (sliceW k n w x)) →
    (∀ x ∈ Set.Icc l r, Sector pn pw pq (sliceN k n w x) (sliceW k n w x)) →
    ConcaveOn ℝ (Set.Icc l r) (fun x => f (sliceN k n w x) (sliceW k n w x))

/-- A function concave on the slices of each sector is nonnegative on the
rectangle once it is nonnegative at the corner, axis and diagonal points. -/
theorem rectangle_wall_nonnegative {f : ℝ → ℝ → ℝ} {nl nr wl wr n w : ℝ}
    (hconc : SectorSliceConcave f nl nr wl wr)
    (hcorner : ∀ x y, AxisBoundary nl nr x → AxisBoundary wl wr y → 0≤f x y)
    (hdiagonal : ∀ z, InRectangle nl nr wl wr z z →
      (AxisBoundary nl nr z ∨ AxisBoundary wl wr z) → 0≤f z z)
    (hpoint : InRectangle nl nr wl wr n w) : 0≤f n w := by
  have hvertical (v : ℝ) (hv : nl≤v ∧ v≤nr) (hvb : AxisBoundary nl nr v)
      (y : ℝ) (hy : wl≤y ∧ y≤wr) : 0≤f v y := by
    obtain ⟨pn,hpn⟩ := exists_hasSign v
    apply two_wall_nonnegative (k := v) hy
    · intro pw pq a b hseg
      apply hconc pn pw (!pq) 1 v 0 a b
      · intro z hz
        exact ⟨hv,(hseg z hz).1⟩
      · intro z hz
        refine ⟨hpn,(hseg z hz).2.1,?_⟩
        have hh := hasSign_neg (hseg z hz).2.2
        rw [neg_sub] at hh
        exact hh
    · intro z hz hcut
      rcases hcut with h | h | h | h <;> subst z
      · exact hcorner v wl hvb (Or.inl rfl)
      · exact hcorner v wr hvb (Or.inr (Or.inr rfl))
      · exact hcorner v 0 hvb (Or.inr (Or.inl rfl))
      · exact hdiagonal v ⟨hv,hz⟩ (Or.inl hvb)
  have hdiagline (z : ℝ) (hz : InRectangle nl nr wl wr z z) : 0≤f z z := by
    let l := max nl wl
    let r := min nr wr
    have hzr : l≤z ∧ z≤r := ⟨max_le hz.1.1 hz.2.1,le_min hz.1.2 hz.2.2⟩
    have hrect (v : ℝ) (hv : l≤v ∧ v≤r) : InRectangle nl nr wl wr v v :=
      ⟨⟨(le_max_left _ _).trans hv.1,hv.2.trans (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans hv.1,hv.2.trans (min_le_right _ _)⟩⟩
    apply two_wall_nonnegative (f := fun v => f v v) (k := 0) hzr
    · intro pn pq a b hseg
      apply hconc pn pn true 2 0 0 a b
      · intro v hv
        exact hrect v (hseg v hv).1
      · intro v hv
        exact ⟨(hseg v hv).2.1,(hseg v hv).2.1,by simp [HasSign,sliceN,sliceW]⟩
    · intro v hv hcut
      apply hdiagonal v (hrect v hv)
      rcases hcut with h | h | h | h
      · rcases max_choice nl wl with hn | hw
        · exact Or.inl (Or.inl (h.trans hn))
        · exact Or.inr (Or.inl (h.trans hw))
      · rcases min_choice nr wr with hn | hw
        · exact Or.inl (Or.inr (Or.inr (h.trans hn)))
        · exact Or.inr (Or.inr (Or.inr (h.trans hw)))
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inl h))
  obtain ⟨pw,hpw⟩ := exists_hasSign w
  apply two_wall_nonnegative (k := w) hpoint.1
  · intro pn pq a b hseg
    apply hconc pn pw pq 0 0 w a b
    · intro x hx
      exact ⟨(hseg x hx).1,hpoint.2⟩
    · intro x hx
      exact ⟨(hseg x hx).2.1,hpw,(hseg x hx).2.2⟩
  · intro x hx hcut
    rcases hcut with h | h | h | h <;> subst x
    · exact hvertical nl hx (Or.inl rfl) w hpoint.2
    · exact hvertical nr hx (Or.inr (Or.inr rfl)) w hpoint.2
    · exact hvertical 0 hx (Or.inr (Or.inl rfl)) w hpoint.2
    · exact hdiagline w ⟨hx,hpoint.2⟩

def northLo (no : Bool) : ℚ := if no then -3/10 else -203/1000
def northHi (no : Bool) : ℚ := if no then 5/12 else 203/1000
def westLo (wo : Bool) : ℚ := if wo then -11/25 else -2/5
def westHi (wo : Bool) : ℚ := if wo then 2/25 else 2/5

lemma domain_iff_rectangle (no wo : Bool) (n w : ℝ) :
    Domain no wo n w ↔
      InRectangle (northLo no) (northHi no) (westLo wo) (westHi wo) n w := by
  cases no <;> cases wo <;> norm_num [Domain,InRectangle,northLo,northHi,westLo,westHi]

def EndpointCondition (no wo : Bool) (u : Fin 4) : Prop :=
  (∀ n w, AxisBoundary (northLo no) (northHi no) n →
    AxisBoundary (westLo wo) (westHi wo) w → 0≤gap no wo u n w) ∧
  (∀ z, Domain no wo z z →
    (AxisBoundary (northLo no) (northHi no) z ∨
      AxisBoundary (westLo wo) (westHi wo) z) → 0≤gap no wo u z z)

/-- The gap is nonnegative on its domain once it is nonnegative at the corner,
axis and diagonal points of the rectangle. -/
theorem nonnegative_of_endpoints {no wo : Bool} {u : Fin 4}
    (he : EndpointCondition no wo u) {n w : ℝ} (hd : Domain no wo n w) :
    0≤gap no wo u n w := by
  apply rectangle_wall_nonnegative (f := gap no wo u)
    (nl := northLo no) (nr := northHi no) (wl := westLo wo) (wr := westHi wo)
  · intro pn pw pq k n w l r hrect hsector
    apply gap_slice_concave u k
    · intro x hx
      exact (domain_iff_rectangle no wo _ _).mpr (hrect x hx)
    · exact hsector
  · exact he.1
  · intro z hz hb
    exact he.2 z ((domain_iff_rectangle no wo z z).mpr hz) hb
  · exact (domain_iff_rectangle no wo n w).mp hd

end SquaresInCircles.Six.Analytic.FixedPair
