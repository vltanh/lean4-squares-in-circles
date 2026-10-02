import SquaresInCircles.Two.Construction
import SquaresInCircles.Common.Contacts
import SquaresInCircles.Common.Angles
import SquaresInCircles.Common.Optimum

/-!
# Two squares: uniqueness

At the optimal radius both centres are exactly `1/2` from the disk centre, `1`
apart, with the disk centre as their midpoint. Squares with centres `1` apart
share an edge; with their frames turned to have the step between the centres
as first axis, they sit at `(-1/2, 0)` and `(1/2, 0)` in the frame along it.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
namespace SquaresInCircles.Two

/-- The parallelogram law, with the disk centre `o` as the common origin. -/
lemma normSq_parallelogram (c d o : Point) :
    normSq (sub c d)+normSq (sub (add c d) (scale 2 o)) =
      2*normSq (sub c o)+2*normSq (sub d o) := by
  simp only [normSq,sub,add,scale]
  ring

/-- In a disk of radius at most `sqrt 5 / 2`, both centres are exactly `1/2`
from the disk centre; they are `1` apart, and the disk centre is their
midpoint. -/
lemma centers_at_half (S : Fin 2 → UnitSquare) (o : Point) (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 5/4) :
    (∀ i, alpha (S i) o^2+beta (S i) o^2=1/4) ∧ normSq (sub (S 1).center (S 0).center)=1 ∧
      sub (S 0).center o=scale (-1/2) (sub (S 1).center (S 0).center) ∧
      sub (S 1).center o=scale (1/2) (sub (S 1).center (S 0).center) := by
  have hnear (i : Fin 2) := radial_sq_le_of_phi (ρ := 1/2) (alpha_nonneg _ _) (beta_nonneg _ _)
    ((hφ i).trans_eq (by norm_num))
  simp only [← local_center_norm] at hnear ⊢
  obtain ⟨hu,hv⟩ := Fin.forall_fin_two.mp hnear
  have hfar := centers_distance_sq_ge_one (S 0) (S 1) (hd 0 1 (by decide))
  have hpar := normSq_parallelogram (S 1).center (S 0).center o
  have hmid := normSq_nonneg (sub (add (S 1).center (S 0).center) (scale 2 o))
  -- equality throughout, so the diagonal `u + v` vanishes
  have hsum : sub (add (S 1).center (S 0).center) (scale 2 o)=(0,0) :=
    not_ne_iff.mp fun h => by linarith [normSq_pos_of_ne h]
  simp only [sub,add,scale,Prod.mk.injEq] at hsum
  refine ⟨Fin.forall_fin_two.mpr ⟨by linarith,by linarith⟩,by linarith,?_,?_⟩ <;>
    ext <;> simp only [sub,scale] <;> linarith

/-- The coordinates of a multiple of a vector in the frame of a square. -/
lemma frame_scale (S : UnitSquare) (s : ℝ) (v : Point) :
    (frameX S (scale s v),frameY S (scale s v))=(s*frameX S v,s*frameY S v) := by
  simp only [frameX,frameY,scale]; ext <;> ring

/-- At the optimal radius the two squares form the rectangle. -/
theorem uniqueness (S : Fin 2 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : Congruent S o model := by
  obtain ⟨-,hunit,e0,e1⟩ := centers_at_half S o hp.disjoint fun i => radius_sq ▸ hp.phi_le i
  -- the squares share an edge: `S 1` has the axes of `S 0`, one unit along an axis
  obtain ⟨haxes,hslots⟩ := unit_contact (S 0) (S 1) (hp.disjoint 0 1 (by decide)) hunit
  set d := sub (S 1).center (S 0).center
  -- so the step `d` is along a side of each square
  have hd (i : Fin 2) : frameX (S i) d=0 ∨ frameY (S i) d=0 := by
    obtain ⟨hX,hY⟩ := relative_normal (S 0) (S 1) d
    fin_cases i <;> rcases haxes with h|h <;>
      rcases hslots with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩ <;> simp [hX,hY,h,hx,hy]
  -- turned by quarter turns, the frame of each square has `d` as first axis: `U c`
  have hd1 : d.1^2+d.2^2=1 := hunit
  let U (c : Point) : UnitSquare := ⟨c,d.1,d.2,hd1⟩
  have hU (c : Point) : frameX (U c) d=1 ∧ frameY (U c) d=0 :=
    ⟨by simp only [U,frameX]; linear_combination hd1,by simp only [U,frameY]; ring⟩
  -- in the frame along `d` the squares sit at `c - o = ∓d/2`, that is at `(∓1/2, 0)`
  obtain ⟨u,huc,hus⟩ := frame_angle (U o)
  refine congruent_of_slots (φ := u) hp.disjoint fun i => ⟨i,fun x y => ?_⟩
  rw [← same_axes_open (S := S i) (T := U (S i).center) rfl (hd i),
    self_represents (U (S i).center) o u huc hus]
  fin_cases i <;> simp [U,e0,e1,frame_scale,hU,centers,neg_div]

/-- The optimum for two squares: `radius`, attained only by the configurations
congruent to `model`. -/
def optimum : Optimum 2 :=
  .ofUnique model model_packing
    ⟨1,(1,1/2),(axisSquare_closed _ _).2 (by norm_num [centers,closedAxisSquare]),by norm_num [normSq,radius_sq]⟩
    uniqueness

end SquaresInCircles.Two
