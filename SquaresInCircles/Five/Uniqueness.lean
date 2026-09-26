import SquaresInCircles.Five.Containing
import SquaresInCircles.Five.Construction
import SquaresInCircles.Common.ArcBudget
import SquaresInCircles.Common.Contacts
import SquaresInCircles.Common.Optimum

/-!
# Five squares: uniqueness

On the circle of radius `5/6`, exterior squares with centres in the 12-gon hold
arcs longer than 72 degrees, and the sweep of a containing square holds 72
degrees unless the square is centred at the disk centre. So some square is
centred there, and the other four, at distance at most 1 from the disk centre,
are its side-neighbours. The closed 12-gon alone is rigid, which is stronger
than uniqueness for the disk.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
open Set
namespace SquaresInCircles.Five

/-- The 12-gon lies in the unit disk. -/
lemma dodecagon_norm_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P5 a b) :
    a^2+b^2 ≤ 1 := by
  by_cases hs : a+b ≤ 1
  · nlinarith [mul_nonneg ha hb]
  · have hroot : Real.sqrt 5 < 12/5 := by
      have hh := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
      nlinarith [Real.sqrt_nonneg 5]
    have htop : a+b < 7/5 := by linarith [h.2]
    have hd0 : -(3-2*(a+b)) ≤ a-b := by linarith [h.1.2]
    have hd1 : a-b ≤ 3-2*(a+b) := by linarith [h.1.1]
    have hsq := mul_nonneg (show 0 ≤ (3-2*(a+b))+(a-b) by linarith)
      (show 0 ≤ (3-2*(a+b))-(a-b) by linarith)
    have hp := mul_neg_of_pos_of_neg (show 0 < a+b-1 by linarith)
      (show 5*(a+b)-7 < 0 by linarith)
    linarith

/-- Some square is centred at the disk centre; only the closed 12-gon is assumed. -/
lemma centered_square (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P5 (alpha (S i) o) (beta (S i) o)) :
    ∃ i, (S i).center=o := by
  by_contra hn
  push Not at hn
  refine ray_budget_impossible (n := 5) (by decide) hd (fun i => (hp i).1) (fun i hi => ?_)
    (fun i hi => by exact_mod_cast exterior_arc (S i) o (hp i) hi)
  obtain ⟨A,hA⟩ := containing_arc (square_chart (S i) o).some hi (hn i)
  exact ⟨A,by rw [hA]; norm_num⟩

/-- All five slots are forced by the centered square and unit-distance contacts. -/
theorem polygon_uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P5 (alpha (S i) o) (beta (S i) o)) :
    HasNormalForm S o centers := by
  classical
  obtain ⟨k,hk⟩ := centered_square S o hd hp
  obtain ⟨t,htc,hts⟩ := frame_angle (S k)
  let φ : Direction := (t:Direction)
  have hc : φ.cos=(S k).cosine := htc
  have hs : φ.sin=(S k).sine := hts
  apply normal_form_of_slots (φ := φ) hd
  intro i
  by_cases hi : i=k
  · subst i
    refine ⟨0,?_⟩
    have hh := self_represents (S k) o φ hc hs
    rw [show centers 0=(0,0) by simp [centers]]
    simpa only [hk,sub,sub_self,frameX,frameY,mul_zero,add_zero] using hh
  · have hlow := centers_distance_sq_ge_one (S k) (S i) (hd k i (Ne.symm hi))
    have hupp : normSq (sub (S i).center o) ≤ 1 := by
      rw [local_center_norm]
      exact dodecagon_norm_le (alpha_nonneg _ _) (beta_nonneg _ _) (hp i)
    have hone : normSq (sub (S i).center (S k).center)=1 := by rw [hk] at *; linarith
    obtain ⟨haxes,hslots⟩ := unit_contact (S k) (S i) (hd k i (Ne.symm hi)) hone
    have hrep := same_axes_represents (S k) (S i) o φ hc hs haxes
    rw [hk] at hslots
    rcases hslots with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rw [hx,hy] at hrep
    exacts [⟨1,hrep⟩,⟨2,hrep⟩,⟨3,hrep⟩,⟨4,hrep⟩]

/-- Geometric uniqueness of the radius-sqrt(5/2) disk packing. -/
theorem uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : HasNormalForm S o centers := by
  apply polygon_uniqueness S o hp.disjoint
  intro i
  apply p5_of_phi
  have h := hp.phi_le i
  rwa [radius_sq] at h

/-- The optimum for five squares: `radius`, attained only by the normal forms
of `centers`. -/
def optimum : Optimum 5 :=
  .ofUnique centers model_packing
    ⟨1,3/2,1/2,by norm_num [centers,closedAxisSquare],by norm_num [radius_sq]⟩ uniqueness

end SquaresInCircles.Five
