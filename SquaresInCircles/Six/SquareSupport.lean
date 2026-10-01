import SquaresInCircles.Common.Contacts

/-!
# Projections of a square

Along a direction `n`, a closed square projects into the closed interval of
half-length `width S n` about the projection of its centre, and for `n ≠ 0` the
open square projects into the open interval. So if `n` separates two squares,
`width S n + width T n ≤ ⟨n, c_T - c_S⟩`, then every point of the open square S
projects below every point of the open square T: a point inside each square
fixes the direction of a separating normal.
-/
noncomputable section
namespace SquaresInCircles.Six

/-- The unit normal to the sides `x = ±1/2` of `S`, its first frame axis. -/
def normalX (S : UnitSquare) : Point := (S.cosine,S.sine)

/-- The unit normal to the sides `y = ±1/2` of `S`, its second frame axis. -/
def normalY (S : UnitSquare) : Point := (-S.sine,S.cosine)

lemma projection_local (S : UnitSquare) (n p : Point) :
    dot n (sub p S.center) = frameX S n * localX S p + frameY S n * localY S p := by
  have hh := frame_dot S n (sub p S.center)
  exact hh.symm

lemma width_pos (S : UnitSquare) {n : Point} (hn : n ≠ (0,0)) : 0 < width S n := by
  have hp := normSq_pos_of_ne hn
  have hf := frame_norm S n
  have h0 := abs_nonneg (frameX S n)
  have h1 := abs_nonneg (frameY S n)
  dsimp [width]
  nlinarith [sq_abs (frameX S n),sq_abs (frameY S n)]

lemma closed_projection_abs (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) : |dot n (sub p S.center)| ≤ width S n := by
  rw [projection_local]
  have hsum := abs_add_le (frameX S n * localX S p) (frameY S n * localY S p)
  rw [abs_mul,abs_mul] at hsum
  have hx := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX S n))
  have hy := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY S n))
  dsimp [width]
  linarith

lemma open_projection_abs (S : UnitSquare) {n p : Point} (hn : n ≠ (0,0))
    (hp : openSquare S p) : |dot n (sub p S.center)| < width S n := by
  rw [projection_local]
  have hsum := abs_add_le (frameX S n * localX S p) (frameY S n * localY S p)
  rw [abs_mul,abs_mul] at hsum
  have hw := width_pos S hn
  have hstrict := weighted_strict (abs_nonneg (frameX S n)) (abs_nonneg (frameY S n))
    (show 0 < |frameX S n| + |frameY S n| by dsimp [width] at hw; linarith)
    hp.1 hp.2
  dsimp [width]
  linarith

lemma closed_projection_bounds (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) :
    dot n S.center - width S n ≤ dot n p ∧ dot n p ≤ dot n S.center + width S n := by
  have hh := abs_le.mp (closed_projection_abs S n hp)
  rw [dot_sub_right] at hh
  constructor <;> linarith [hh.1,hh.2]

lemma open_projection_bounds (S : UnitSquare) {n p : Point} (hn : n ≠ (0,0))
    (hp : openSquare S p) :
    dot n S.center - width S n < dot n p ∧ dot n p < dot n S.center + width S n := by
  have hh := abs_lt.mp (open_projection_abs S hn hp)
  rw [dot_sub_right] at hh
  constructor <;> linarith [hh.1,hh.2]

/-- If `n` separates S from T, every point of the open square S projects below
every point of the open square T. -/
lemma separator_orients_pins {S T : UnitSquare} {n p q : Point}
    (hn : n ≠ (0,0)) (hp : openSquare S p) (hq : openSquare T q)
    (hsep : width S n + width T n ≤ dot n (sub T.center S.center)) :
    dot n p < dot n q := by
  have hS := open_projection_bounds S hn hp
  have hT := open_projection_bounds T hn hq
  rw [dot_sub_right] at hsep
  linarith [hS.2,hT.1]

end SquaresInCircles.Six
