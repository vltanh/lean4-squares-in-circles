import SquaresInCircles.Seven.Uniqueness.ContactCycle
import SquaresInCircles.Six.Normalization.Constants

/-!
# The central square

In a packing of six unit squares in a disk of squared radius less than `13/4`,
exactly one square contains the disk centre in its open interior. Otherwise all
six squares would be exterior, and by the ring theorem of seven squares one of
them would have a corner at squared distance `13/4` from the centre. Removing
the central square leaves five exterior squares.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- In a disk of squared radius less than `13/4`, one of six squares contains
the disk centre in its open interior. -/
theorem exists_containing {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R ^ 2 < 13 / 4) :
    ∃ i, openSquare (S i) o := by
  classical
  by_contra! hext
  obtain ⟨W⟩ := Seven.six_exterior_ring S o hp.disjoint hext (fun i => by
    change phi (alpha (S i) o) (beta (S i) o) ≤ 13 / 4
    exact (hp.phi_le i).trans hR.le)
  let p : Point := pointInDirection o W.phase (3 / 2) (-1)
  have hmem : closedSquare (S (W.order 0)) p := by
    apply ((W.represents 0).closed (3 / 2) (-1)).mpr
    norm_num [Seven.ringCenters, closedAxisSquare]
  have hdist := frameEquiv_distance o W.phase (3 / 2, -1) (0, 0)
  rw [frameEquiv_zero] at hdist
  have hnorm : normSq (sub p o) = 13 / 4 := by
    calc
      normSq (sub p o) = normSq (sub (3 / 2, -1) (0, 0)) := hdist
      _ = 13 / 4 := by norm_num [normSq, sub]
  have hbound : normSq (sub p o) ≤ R ^ 2 := hp.2.1 (W.order 0) p hmem
  rw [hnorm] at hbound
  linarith

/-- Interior-disjointness makes the containing square unique. -/
theorem exists_unique_containing {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R ^ 2 < 13 / 4) :
    ∃! i, openSquare (S i) o := by
  obtain ⟨i, hi⟩ := exists_containing hp hR
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact hp.disjoint j i hji o ⟨hj, hi⟩

/-- The same in a disk of squared radius at most `Q0`, which is less than
`13/4`. -/
theorem exists_unique_containing_of_ceiling {S : Fin 6 → UnitSquare}
    {o : Point} {R : ℝ} (hp : Packing S o R) (hR : R ^ 2 ≤ Normalization.Q0) :
    ∃! i, openSquare (S i) o :=
  exists_unique_containing hp (lt_of_le_of_lt hR Normalization.Q0_lt_thirteen_fourths)

/-- Removing the containing square leaves exactly five exterior squares. -/
lemma remaining_exterior {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) {k : Fin 6} (hk : openSquare (S k) o) :
    ∀ i : Fin 5, ¬ openSquare (S (k.succAbove i)) o := by
  intro i hi
  exact hp.disjoint _ k (k.succAbove_ne i) o ⟨hi, hk⟩

end SquaresInCircles.Six
