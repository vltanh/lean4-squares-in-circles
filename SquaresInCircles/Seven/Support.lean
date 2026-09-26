import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.Construction

/-!
# The support function

The support function of the closed axis-parallel unit square at a point, bounded
below by the points of the square and, for an admissible state, by the distance
of its centre from the disk centre; and Cauchy–Schwarz for a linear form on the
disk `φ ≤ 13/4`.
-/
noncomputable section
namespace SquaresInCircles.Seven

def support (a b z : ℝ) : ℝ :=
  a*Real.cos z+b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2

lemma point_le_support {a b x y : ℝ}
    (hx : |x-a| ≤ 1/2) (hy : |y-b| ≤ 1/2) (z : ℝ) :
    x*Real.cos z+y*Real.sin z ≤ support a b z := by
  have hx0 : (x-a)*Real.cos z ≤ (1/2)*|Real.cos z| := by
    calc
      _ ≤ |(x-a)*Real.cos z| := le_abs_self _
      _ = |x-a| * |Real.cos z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hy0 : (y-b)*Real.sin z ≤ (1/2)*|Real.sin z| := by
    calc
      _ ≤ |(y-b)*Real.sin z| := le_abs_self _
      _ = |y-b| * |Real.sin z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  dsimp [support]
  linarith

lemma sqrt_three_bounds : (173 : ℝ)/100 < Real.sqrt 3 ∧ Real.sqrt 3 < 1733/1000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]

lemma dot_sq_le {X Y p r : ℝ} (h : X^2+Y^2 ≤ targetSq) :
    (p*X+r*Y)^2 ≤ targetSq*(p^2+r^2) := by
  nlinarith [sq_nonneg (p*Y-r*X),
    mul_le_mul_of_nonneg_left h (add_nonneg (sq_nonneg p) (sq_nonneg r))]

/-- Cauchy–Schwarz on the disk of squared radius `13/4`: a linear form whose
squared norm is at most `4c²/13` is at least `-c` there. -/
lemma dot_ge {X Y p r c : ℝ} (h : X^2+Y^2 ≤ targetSq) (hc : 0 ≤ c)
    (hpr : targetSq*(p^2+r^2) ≤ c^2) : -c ≤ p*X+r*Y :=
  (abs_le_of_sq_le_sq' ((dot_sq_le h).trans hpr) hc).1

lemma dot_gt {X Y p r c : ℝ} (h : X^2+Y^2 ≤ targetSq) (hc : 0 ≤ c)
    (hpr : targetSq*(p^2+r^2) < c^2) : -c < p*X+r*Y :=
  (abs_lt_of_sq_lt_sq' ((dot_sq_le h).trans_lt hpr) hc).1

/-- The centre of an admissible square is within `31/25` of the disk centre, so
its support in every direction exceeds `1/2 - 31/25`. -/
lemma support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    -37/50 < support a b z := by
  have hp := h.phi_le
  dsimp [phi,targetSq] at hp
  have hb := sq_abs b
  have hn : a^2+b^2 < (31/25)^2 := by
    nlinarith [h.a_nonneg,abs_nonneg b,mul_nonneg h.a_nonneg (abs_nonneg b)]
  have hcs := (abs_lt_of_sq_lt_sq' (show (a*Real.cos z+b*Real.sin z)^2 < (31/25)^2 by
    nlinarith [sq_nonneg (a*Real.sin z-b*Real.cos z),Real.sin_sq_add_cos_sq z])
    (by norm_num)).1
  have hw : 1 ≤ |Real.cos z|+|Real.sin z| := by
    nlinarith [sq_abs (Real.cos z),sq_abs (Real.sin z),Real.sin_sq_add_cos_sq z,
      abs_nonneg (Real.cos z),abs_nonneg (Real.sin z),
      mul_nonneg (abs_nonneg (Real.cos z)) (abs_nonneg (Real.sin z))]
  dsimp [support]
  linarith

end SquaresInCircles.Seven
