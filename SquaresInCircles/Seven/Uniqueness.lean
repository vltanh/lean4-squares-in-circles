import SquaresInCircles.Seven.Optimality
import SquaresInCircles.Seven.Uniqueness.Reconstruction
import SquaresInCircles.Seven.Uniqueness.SevenMarkers
import SquaresInCircles.Seven.Uniqueness.Slots
import SquaresInCircles.Common.Optimum

/-!
# Seven squares: uniqueness

Every packing of seven unit squares in the disk of radius `√13 / 2` is one of
the sliding packings of `Seven/Construction.lean`, moved by one rotation about
the disk centre and relabelled; the middle column may sit anywhere in its range.
Conversely every such normal form is an optimal packing (`Optimum.packing_iff`).

The equality case reruns the lower bound: one square contains the disk centre
(`Uniqueness/SevenMarkers.lean`), the markers of the other six form a regular
hexagon and neighbouring squares touch as in the optimal packing
(`Uniqueness/ContactCycle.lean`), and the square in the middle is pinned between
the side columns (`Uniqueness/CentralSquare.lean`).

The file ends with `optimum`: the case as an `Optimum`.
-/
noncomputable section
namespace SquaresInCircles.Seven

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
