import SquaresInCircles.Common.Tangents
import SquaresInCircles.Common.Separation

/-!
# The common octagon support estimate and safe radial extension

The support estimate does not require a bound on the angle between squares.
The final `safe_openRay_of_disjoint` theorem uses an arbitrary nonzero separating
functional from `support_separator` (`Separation.lean`).  No separating-axis
enumeration or additional geometric hypothesis is required.
-/
noncomputable section
namespace SquaresInCircles

/-- The octagon support estimate: for `(a, b)` in `P8` and nonnegative `p, q, u,
v` with `p² + q² = u² + v²`, `p a + q b ≤ (p + q)/2 + (u + v)/2`. Over the
quadrilateral `P8 ∩ {a, b ≥ 0}`, `p a + q b` is largest at a vertex. -/
lemma octagon_support {a b p q u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (he : p^2+q^2=u^2+v^2) (h : P8 a b) :
    p*a+q*b ≤ (p+q)/2+(u+v)/2 := by
  have hp' : p ≤ u+v := by nlinarith [sq_nonneg q,mul_nonneg hu hv]
  have hq' : q ≤ u+v := by nlinarith [sq_nonneg p,mul_nonneg hu hv]
  rcases h with ⟨h₀,h₁⟩
  by_cases hdom : 3*q ≤ p
  · nlinarith [mul_le_mul_of_nonneg_left h₀ (show 0 ≤ p/3 by positivity),
      mul_nonneg (show 0 ≤ p/3-q by linarith) hb]
  · by_cases hdom' : 3*p ≤ q
    · nlinarith [mul_le_mul_of_nonneg_left h₁ (show 0 ≤ q/3 by positivity),
        mul_nonneg (show 0 ≤ q/3-p by linarith) ha]
    · nlinarith [mul_le_mul_of_nonneg_left h₀ (show 0 ≤ (3*p-q)/8 by linarith),
        mul_le_mul_of_nonneg_left h₁ (show 0 ≤ (3*q-p)/8 by linarith)]

/-- If `(a_S, b_S)` lies in the octagon, then in every direction `n` the disk
centre is within the sum of the widths of `S` and of any `T` from `c_S`. -/
lemma dot_center_le (S T : UnitSquare) (o n : Point) (h : P8 (alpha S o) (beta S o)) :
    |dot n (sub S.center o)| ≤ width S n+width T n := by
  have he : |frameX S n|^2+|frameY S n|^2=|frameX T n|^2+|frameY T n|^2 := by
    simp only [sq_abs,frame_norm]
  calc |dot n (sub S.center o)|
      ≤ |frameX S n*frameX S (sub S.center o)|+|frameY S n*frameY S (sub S.center o)| := by
        rw [← frame_dot S]; exact abs_add_le _ _
    _ = |frameX S n| * alpha S o+|frameY S n| * beta S o := by
        rw [abs_mul,abs_mul,abs_frame_centerX,abs_frame_centerY]
    _ ≤ width S n+width T n := octagon_support (alpha_nonneg _ _) (beta_nonneg _ _)
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) he h

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
    (hS : P8 (alpha S o) (beta S o)) (hT : P8 (alpha T o) (beta T o)) :
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

/-- Safe extension, directly from ordinary disjointness and the center polygon. -/
theorem safe_openRay_of_disjoint (S T : UnitSquare) (o : Point)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hS : P8 (alpha S o) (beta S o)) (hT : P8 (alpha T o) (beta T o)) :
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
