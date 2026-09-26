import SquaresInCircles.Two.Construction
import SquaresInCircles.Common.Contacts

/-!
# Two squares: the lower bound

The smallest disk containing two non-overlapping unit squares has radius `sqrt 5
/ 2`, half the diagonal of a 2 × 1 rectangle.

In a disk of radius at most `sqrt 5 / 2` the farthest-vertex bound keeps both
centres within `1/2` of the disk centre. Centres of interior-disjoint unit
squares are at least 1 apart, so by the parallelogram law both are exactly
`1/2` from it (`centers_at_half`), which puts the farthest vertices at least
`sqrt 5 / 2` away.
-/
noncomputable section
namespace SquaresInCircles.Two

/-- A square whose farthest vertex is within `sqrt 5 / 2` of the disk centre
has its centre within `1/2` of it. -/
lemma center_near {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : phi a b ≤ 5/4) : a^2+b^2 ≤ 1/4 := by
  unfold phi at h
  nlinarith [mul_nonneg ha hb]

/-- The parallelogram law, with the disk centre `o` as the common origin. -/
lemma normSq_parallelogram (c d o : Point) :
    normSq (sub c d)+normSq (sub (add c d) (scale 2 o)) =
      2*normSq (sub c o)+2*normSq (sub d o) := by
  simp only [normSq,sub,add,scale]
  ring

/-- In a disk of radius at most `sqrt 5 / 2`, both centres are exactly `1/2`
from the disk centre. -/
lemma centers_at_half (S : Fin 2 → UnitSquare) (o : Point) (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 5/4) :
    ∀ i, alpha (S i) o^2+beta (S i) o^2=1/4 := by
  have hnear (i : Fin 2) := center_near (alpha_nonneg _ _) (beta_nonneg _ _) (hφ i)
  simp only [← local_center_norm] at hnear ⊢
  have hfar := centers_distance_sq_ge_one (S 0) (S 1) (hd 0 1 (by decide))
  have hpar := normSq_parallelogram (S 1).center (S 0).center o
  have hmid := normSq_nonneg (sub (add (S 1).center (S 0).center) (scale 2 o))
  exact Fin.forall_fin_two.mpr ⟨by linarith [hnear 0,hnear 1],by linarith [hnear 0,hnear 1]⟩

theorem squared_lower (S : Fin 2 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (5:ℝ)/4 ≤ R^2 := by
  by_contra hn
  have hφ (i : Fin 2) := (hp.phi_le i).trans_lt (lt_of_not_ge hn)
  have h := centers_at_half S o hp.disjoint (fun i => (hφ i).le) 0
  have h0 := hφ 0
  unfold phi at h0
  nlinarith [mul_nonneg (alpha_nonneg (S 0) o) (beta_nonneg (S 0) o),alpha_nonneg (S 0) o,
    beta_nonneg (S 0) o]

theorem optimality (S : Fin 2 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact squared_lower S o R hp) hp.1

end SquaresInCircles.Two
