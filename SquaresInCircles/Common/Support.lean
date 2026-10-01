import SquaresInCircles.Common.Separation

/-!
# Safe radial extension

If the centres of two squares with disjoint interiors are within distance 1
of the disk centre, the separating functional of `support_separator`
(`Separation.lean`) keeps the radial sweep of either square away from the
other square (`safe_openRay_of_disjoint`): the disk centre is within the sum of
the two widths of each centre, along every direction.
-/
noncomputable section
namespace SquaresInCircles

/-- If the centre of `S` is within distance 1 of `o`, then in every direction
`n` the disk centre is within the sum of the widths of `S` and of any `T` from
`c_S`. -/
lemma dot_center_le (S T : UnitSquare) (o n : Point) (h : normSq (sub S.center o) ≤ 1) :
    |dot n (sub S.center o)| ≤ width S n+width T n := by
  have hn := Real.abs_le_sqrt ((cauchy_sq n (sub S.center o)).trans
    (mul_le_of_le_one_right (normSq_nonneg n) h))
  have hS := width_lower S n
  have hT := width_lower T n
  unfold width
  linarith

/-- Union of translates of the *open* square along the ray away from `o`. -/
def openRay (S : UnitSquare) (o : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ ∃ q, openSquare S q ∧
    p = add q (scale t (sub S.center o))}

lemma frame_abs_sum_pos (S : UnitSquare) {n : Point} (hn : n ≠ (0,0)) :
    0 < |frameX S n|+|frameY S n| := by
  have hp := normSq_pos_of_ne hn
  rw [← frame_norm S n,← sq_abs (frameX S n),← sq_abs (frameY S n)] at hp
  by_contra h
  nlinarith [abs_nonneg (frameX S n),abs_nonneg (frameY S n)]

lemma Separation.center_signs {S T : UnitSquare} (e : Separation S T) (o : Point)
    (hS : normSq (sub S.center o) ≤ 1) (hT : normSq (sub T.center o) ≤ 1) :
    dot e.normal (sub S.center o) ≤ 0 ∧ 0 ≤ dot e.normal (sub T.center o) := by
  have h₁ := dot_center_le S T o e.normal hS
  have h₂ := dot_center_le T S o e.normal hT
  have hsep := e.separates
  rcases abs_le.mp h₁ with ⟨h₁a,h₁b⟩
  rcases abs_le.mp h₂ with ⟨h₂a,h₂b⟩
  simp only [dot_sub_right] at *
  exact ⟨by linarith,by linarith⟩

lemma dot_open_bound_of_ne (S : UnitSquare) {n : Point} (hn : n ≠ (0,0))
    {p : Point} (hp : openSquare S p) : |dot n (sub p S.center)| < width S n := by
  have hh := weighted_strict (abs_nonneg (frameX S n)) (abs_nonneg (frameY S n))
    (frame_abs_sum_pos S hn) hp.1 hp.2
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| < width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  dsimp [width]
  linarith

/-- The radial sweep of `S` misses a square `T` with a disjoint interior when both
centres are within distance 1 of `o`. -/
theorem safe_openRay_of_disjoint (S T : UnitSquare) (o : Point)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hS : normSq (sub S.center o) ≤ 1) (hT : normSq (sub T.center o) ≤ 1) :
    Disjoint (openRay S o) {p | openSquare T p} := by
  obtain ⟨e⟩ := support_separator S T hd
  rw [Set.disjoint_left]
  rintro p ⟨t,ht,q,hq,rfl⟩ hp
  have hsign := e.center_signs o hS hT
  have hmove := mul_nonpos_of_nonneg_of_nonpos ht hsign.1
  have hqB := (abs_lt.mp (dot_open_bound_of_ne S e.nonzero hq)).2
  have hpB := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hp)).1
  have hsep := e.separates
  simp only [dot_sub_right,dot_add_right,dot_scale_right] at *
  linarith

lemma closed_dot_bound (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) : |dot n (sub p S.center)| ≤ width S n := by
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| ≤ width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  have hx := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX S n))
  have hy := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY S n))
  dsimp [width]
  linarith

lemma closed_open_disjoint (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    {p : Point} (hS : closedSquare S p) : ¬ openSquare T p := by
  obtain ⟨e⟩ := support_separator S T hd
  intro hT
  have h₁ := (abs_le.mp (closed_dot_bound S e.normal hS)).2
  have h₂ := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hT)).1
  have hsep := e.separates
  simp only [dot_sub_right] at *
  linarith

end SquaresInCircles
