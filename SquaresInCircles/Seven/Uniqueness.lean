import SquaresInCircles.Seven.Uniqueness.ContactCycle
import SquaresInCircles.Seven.Uniqueness.CentralSquare
import SquaresInCircles.Common.Optimum

/-!
# Seven squares: uniqueness

Every packing of seven unit squares in the disk of radius `√13 / 2` is one of
the sliding packings of `Seven/Construction.lean`, moved by one rotation about
the disk centre and relabelled; the middle column may sit anywhere in its range.
Conversely every such normal form is an optimal packing (`Optimum.packing_iff`).

The equality case reruns the lower bound. Seven directions cannot be pairwise
at least `π/3` apart, since closed arcs of half-width `1/2` about them would be
disjoint, so some square contains the disk centre. The markers of the other six
form a regular hexagon and neighbouring squares touch as in the optimal packing
(`Uniqueness/ContactCycle.lean`), and the square in the middle is pinned between
the side columns (`Uniqueness/CentralSquare.lean`). The three squares of the
middle column have centres at least 1 apart, which gives the sliding normal
form.

The file ends with `optimum`: the case as an `Optimum`.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Seven directions cannot be pairwise at least `π/3` apart. -/
lemma seven_directions_impossible (c : Fin 7 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) : False := by
  have hballs : Pairwise (fun i j =>
      Disjoint (Metric.closedBall (c i) (1/2)) (Metric.closedBall (c j) (1/2))) := by
    intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hg := hsep i j hij
    dsimp [gap] at hg
    linarith [Real.pi_gt_d2]
  have hb := closed_arc_budget c (fun _ => (1/2 : ℝ))
    (fun _ => ⟨by norm_num,by linarith [Real.pi_pos,Real.pi_gt_d2]⟩) hballs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  norm_num at hb
  linarith [pi_lt_22_over_7]

/-- At the optimal radius some square contains the disk centre. -/
theorem exists_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ i, openSquare (S i) o := by
  classical
  by_contra hn
  have hext : ∀ i, ¬ openSquare (S i) o := by simpa only [not_exists] using hn
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hadm (i : Fin 7) : Admissible (C i).a (C i).b := by
    apply chart_admissible (C i) (hsort i) (hext i)
    have hh := hp.phi_le i
    simpa only [radius_sq,targetSq] using hh
  apply seven_directions_impossible (fun i => chartMarker (C i))
  intro i j hij
  exact marker_separation_closed (C i) (C j) (hadm i) (hadm j) (hp.disjoint i j hij)

/-- Two aligned squares in one column cannot have centers less than one apart. -/
lemma column_centers_separated {S T : UnitSquare} {o : Point} {φ : Direction} {x y : ℝ}
    (hS : Represents S o φ (0,x)) (hT : Represents T o φ (0,y))
    (hxy : x ≤ y) (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : x+1 ≤ y := by
  by_contra hn
  refine hd (pointInDirection o φ 0 ((x+y)/2)) ⟨(hS _ _).mpr ?_,(hT _ _).mpr ?_⟩ <;>
    exact ⟨by norm_num,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

def sideRingIndex : Fin 4 → Fin 6 := ![0,1,4,3]
def outerSlot : Fin 6 → Fin 7 := ![0,1,6,3,2,4]

/-- An optimal packing in which square `k` contains the disk centre has the
sliding normal form. -/
theorem normal_form_of_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) (k : Fin 7) (hk : openSquare (S k) o) :
    ∃ c : Column, HasNormalForm S o (slidingCenters c) := by
  obtain ⟨W⟩ := six_exterior_ring (fun i => S (k.succAbove i)) o
    (fun i j hij => hp.disjoint _ _ (Fin.succAbove_right_injective.ne hij))
    (fun i hi => hp.disjoint _ k (k.succAbove_ne i) o ⟨hi,hk⟩)
    (fun i => by simpa only [radius_sq,targetSq] using hp.phi_le (k.succAbove i))
  obtain ⟨z,hz,hcenter⟩ := central_square_represents
    (B := fun i => S (k.succAbove (W.order (sideRingIndex i)))) hk
    (fun i => by fin_cases i <;> exact W.represents _) (fun i => hp.disjoint _ k (k.succAbove_ne _))
  have htop : z+1 ≤ W.top := column_centers_separated hcenter (W.represents 2)
    (by linarith [W.top_bounds.1,abs_lt.mp hz]) (hp.disjoint k _ (k.succAbove_ne _).symm)
  have hbottom : -W.bottom+1 ≤ z := column_centers_separated (W.represents 5) hcenter
    (by linarith [W.bottom_bounds.1,abs_lt.mp hz]) (hp.disjoint _ k (k.succAbove_ne _))
  let c : Column :=
    { bottom := -W.bottom
      middle := z
      top := W.top
      lower := by linarith [W.bottom_bounds.2]
      gap_lower := hbottom
      gap_upper := htop
      upper := W.top_bounds.2 }
  refine ⟨c,normal_form_of_slots (φ := W.phase) hp.disjoint fun j => ?_⟩
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i,rfl⟩
  · exact ⟨5,by simpa [slidingCenters,c] using hcenter⟩
  obtain ⟨l,rfl⟩ := W.order.surjective i
  have hslot : ringCenters W.top W.bottom l = slidingCenters c (outerSlot l) := by
    fin_cases l <;> simp [ringCenters,slidingCenters,outerSlot,c]
  exact ⟨outerSlot l,hslot ▸ W.represents l⟩

/-- Every packing at the optimal radius is a sliding packing, rotated about the
disk centre and relabelled. -/
theorem uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ c : Column, HasNormalForm S o (slidingCenters c) :=
  (exists_containing S o hp).elim (normal_form_of_containing S o hp)

/-- The optimum for seven squares: `radius`, attained exactly by the normal
forms of the sliding packings. -/
def optimum : Optimum 7 where
  radius := radius
  layouts := Set.range slidingCenters
  optimality := optimality
  layouts_nonempty := ⟨_,centeredColumn,rfl⟩
  layout_packing := by
    rintro _ ⟨c,rfl⟩
    exact sliding_packing c
  uniqueness S o hp :=
    let ⟨c,h⟩ := uniqueness S o hp
    ⟨_,⟨c,rfl⟩,h⟩

/-- The optimal packings, parametrized by the four gaps of the column:
nonnegative, with sum `2√3 - 3`. -/
theorem classification_by_slots (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔
    ∃ g : SlotSimplex, HasNormalForm S o (slidingCenters (columnSlotEquiv.symm g)) :=
  ⟨fun hp => let ⟨c,h⟩ := uniqueness S o hp
    ⟨columnSlotEquiv c,by simpa only [Equiv.symm_apply_apply] using h⟩,
   fun ⟨_,h⟩ => h.packing (sliding_packing _)⟩

end SquaresInCircles.Seven
