import SquaresInCircles.Six.SquareSupport
import SquaresInCircles.Common.Support

/-!
# Geometric support inequalities used by the n=6 stresses

The support bounds are proved from actual closed-square containment. In
particular the vertex bound is valid in every force direction, including zero;
it is not the invalid cap estimate selected merely by coordinate dominance.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

def vectorLength (v : Point) : ℝ := Real.sqrt (normSq v)

def vertexSupport (R : ℝ) (S : UnitSquare) (v : Point) : ℝ :=
  R*vectorLength v-width S v

def boxSupport (h : ℝ) (v : Point) : ℝ := h*(max v.1 0+max v.2 0)

lemma vectorLength_nonneg (v : Point) : 0 ≤ vectorLength v := Real.sqrt_nonneg _
lemma vectorLength_sq (v : Point) : vectorLength v^2=normSq v := Real.sq_sqrt (normSq_nonneg v)

lemma dot_le_radius {v p : Point} {R : ℝ} (hR : 0 ≤ R) (hp : normSq p ≤ R^2) :
    dot v p ≤ R*vectorLength v := by
  have hcs := cauchy_sq v p
  have hm := mul_le_mul_of_nonneg_left hp (normSq_nonneg v)
  have hs : (dot v p)^2 ≤ (R*vectorLength v)^2 := by
    calc
      (dot v p)^2 ≤ normSq v*normSq p := hcs
      _ ≤ normSq v*R^2 := hm
      _ = (R*vectorLength v)^2 := by rw [← vectorLength_sq]; ring
  have hn : 0 ≤ R*vectorLength v := mul_nonneg hR (vectorLength_nonneg v)
  by_contra! h
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0 < dot v p+R*vectorLength v by linarith)
  nlinarith

/-- A genuine vertex realizes the support width in the chosen direction. -/
lemma exists_support_vertex (S : UnitSquare) (n : Point) :
    ∃ p, closedSquare S p ∧ dot n p=dot n S.center+width S n := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (frameX S n) (c := (1:ℝ)/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (frameY S n) (c := (1:ℝ)/2) (by norm_num)
  let p := add S.center (rotate S (u,v))
  have hp : closedSquare S p := by
    constructor
    · simpa only [p,localX_rotated,hu] using (le_rfl : (1:ℝ)/2 ≤ 1/2)
    · simpa only [p,localY_rotated,hv] using (le_rfl : (1:ℝ)/2 ≤ 1/2)
  have hproj := Six.projection_local S n p
  dsimp [p] at hproj
  rw [localX_rotated,localY_rotated,dot_sub_right] at hproj
  refine ⟨p,hp,?_⟩
  dsimp [width]
  linarith

/-- Every contained square obeys the full far-vertex support inequality. -/
theorem center_le_vertexSupport {S : UnitSquare} {R : ℝ}
    (hR : 0 ≤ R) (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p) (n : Point) :
    dot n S.center ≤ vertexSupport R S n := by
  obtain ⟨p,hp,he⟩ := exists_support_vertex S n
  have hd : normSq p ≤ R^2 := by simpa [inDisk,sub] using hcontain p hp
  have hb := dot_le_radius (v := n) hR hd
  rw [he] at hb
  dsimp [vertexSupport]
  linarith

lemma scalar_box_support {x h v : ℝ} (hx : 0 ≤ x ∧ x ≤ h) : x*v ≤ h*max v 0 := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv]
    exact mul_le_mul_of_nonneg_right hx.2 hv
  · rw [max_eq_right (le_of_not_ge hv),mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hx.1 (le_of_not_ge hv)

lemma center_le_boxSupport {c : Point} {h : ℝ}
    (hc : (0 ≤ c.1 ∧ c.1 ≤ h) ∧ (0 ≤ c.2 ∧ c.2 ≤ h)) (v : Point) :
    dot v c ≤ boxSupport h v := by
  have hx := scalar_box_support (v := v.1) hc.1
  have hy := scalar_box_support (v := v.2) hc.2
  dsimp [dot,boxSupport]
  nlinarith

/-- Discarding a nonnegative half-width term produces the weaker primary
support used in some rows of Appendix A. -/
lemma center_le_primaryVertexSupport {S : UnitSquare} {R : ℝ}
    (hR : 0 ≤ R) (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p) (n : Point) :
    dot n S.center ≤ R*vectorLength n-|frameX S n|/2 := by
  have hh := center_le_vertexSupport hR hcontain n
  dsimp [vertexSupport,width] at hh
  linarith [abs_nonneg (frameY S n)]

end SquaresInCircles.Six.Stress
