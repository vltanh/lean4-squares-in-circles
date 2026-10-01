import SquaresInCircles.Six.SquareSupport
import SquaresInCircles.Common.Support

/-!
# The far-vertex support

A square in the closed disk of radius `R` about the origin has centre `c` with
`⟨n, c⟩ ≤ R |n| - width S n` for every vector `n`, where
`width S n = (|⟨n, e₁⟩| + |⟨n, e₂⟩|)/2` for the frame `e₁`, `e₂` of the square:
some vertex lies `width S n` beyond the centre along `n`, and as it lies in the
disk, Cauchy–Schwarz bounds its projection by `R |n|` (`dot_le_radius`).
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

def vectorLength (v : Point) : ℝ := Real.sqrt (normSq v)

/-- The far-vertex support `R |v| - width S v`. -/
def vertexSupport (R : ℝ) (S : UnitSquare) (v : Point) : ℝ :=
  R*vectorLength v-width S v

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

/-- Some vertex of the square lies `width S n` beyond its centre along `n`. -/
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

/-- A square in the closed disk of radius `R` about the origin has
`⟨n, c⟩ ≤ R |n| - width S n` for every `n`. -/
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

end SquaresInCircles.Six.Stress
