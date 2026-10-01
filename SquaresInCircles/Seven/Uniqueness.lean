import SquaresInCircles.Seven.Ring
import SquaresInCircles.Seven.Containing
import SquaresInCircles.Common.Optimum

/-!
# Seven squares: uniqueness

Every packing of seven unit squares in the disk of radius `√13 / 2` is
congruent to one of the column packings of `Seven/Construction.lean`: the four
side squares are fixed, and each of the three middle squares can sit anywhere
on the middle axis, at least 1 from the others and inside the disk. Conversely
every such configuration is an optimal packing (`Optimum.packing_iff`).

Some square contains the disk centre, and it is pinned between the side
columns (`Containing.lean`). The markers of the other six form a regular
hexagon, and neighbouring squares touch as in the optimal packing
(`Ring.lean`). The three squares of the middle column have centres at least 1
apart, which gives a column packing.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
namespace SquaresInCircles.Seven

def sideRingIndex : Fin 4 → Fin 6 := ![0,1,4,3]
def outerSlot : Fin 6 → Fin 7 := ![0,1,6,3,2,4]

/-- An optimal packing in which square `k` contains the disk centre is
congruent to a column packing. -/
theorem congruent_of_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) (k : Fin 7) (hk : openSquare (S k) o) :
    ∃ c : Column, Congruent S o (columnModel c) := by
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
  refine ⟨c,congruent_of_slots (φ := W.phase) hp.disjoint fun j => ?_⟩
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i,rfl⟩
  · exact ⟨5,by simpa [columnCenters,c] using hcenter⟩
  obtain ⟨l,rfl⟩ := W.order.surjective i
  have hslot : ringCenters W.top W.bottom l = columnCenters c (outerSlot l) := by
    fin_cases l <;> simp [ringCenters,columnCenters,outerSlot,c]
  exact ⟨outerSlot l,hslot ▸ W.represents l⟩

/-- Every packing at the optimal radius is congruent to a column packing: the
four side squares at `(±1, ±1/2)` and the three middle squares at heights that
are at least 1 apart and within `√3 - 1/2` of the centre. -/
theorem uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ c : Column, Congruent S o (columnModel c) :=
  (exists_containing S o hp).elim (congruent_of_containing S o hp)

/-- The optimum for seven squares: `radius`, attained exactly by the
configurations congruent to a column packing. -/
def optimum : Optimum 7 where
  radius := radius
  models := Set.range columnModel
  models_nonempty := ⟨_,centeredColumn,rfl⟩
  model_packing := by
    rintro _ ⟨c,rfl⟩
    exact column_packing c
  model_reaches := by
    rintro _ ⟨c,rfl⟩
    exact ⟨0,(3/2,-1),(axisSquare_closed _ _).2 (by norm_num [columnCenters,closedAxisSquare]),
      by norm_num [normSq,radius_sq]⟩
  uniqueness S o hp :=
    let ⟨c,h⟩ := uniqueness S o hp
    ⟨_,⟨c,rfl⟩,h⟩

/-- The optimal packings, parametrized by the four gaps of the column:
nonnegative, with sum `2√3 - 3`. -/
theorem classification_by_slots (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔
    ∃ g : SlotSimplex, Congruent S o (columnModel (columnSlotEquiv.symm g)) :=
  ⟨fun hp => let ⟨c,h⟩ := uniqueness S o hp
    ⟨columnSlotEquiv c,by simpa only [Equiv.symm_apply_apply] using h⟩,
   fun ⟨_,h⟩ => h.packing (column_packing _)⟩

end SquaresInCircles.Seven
