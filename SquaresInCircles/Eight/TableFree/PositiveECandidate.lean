module

public import SquaresInCircles.Eight.TableFree.EPairOrderedEndpoint

/-!
# Actual same-radius E candidates for two nonnegative primaries

Uncompiled source. The larger of the original H/D primary coordinates
is chosen only for the scalar contact construction. Reversing that
choice reflects the local E tangent and then restores the original
DE/EH edges. The output includes both quarter-gap guards and an explicit
diagonal alternative; the global tie theorem is not assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveEPair
open EPairOrderedEndpoint

structure Endpoint (q : ℝ) (D H : SignedPoint) (t : ℝ) where
  point : SignedPoint
  deError : ℝ
  de_mem : deError∈Icc 0 t
  sorted : point.Sorted
  outer : point.Outer q
  core : point.AvoidsCore
  DE : quarterFeasible D point deError 3
  EH : quarterFeasible point H (t-deError) 1
  de_guard : 0<deError ∨ point.y<point.a
  eh_guard : 0<t-deError ∨ -point.a<point.y
  terminal : deError=0 ∨ deError=t ∨ |point.y|=point.a

theorem candidate {q u v : ℝ} {D E H : SignedPoint}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hDs : D.Sorted) (hDo : D.Outer q) (hHs : H.Sorted) (hHo : H.Outer q)
    (hEs : E.Sorted) (hEc : E.Contained q)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    Nonempty (Endpoint q D H (u+v)) := by
  have hDb := SignedPoint.outer_bounds hDs hDo
  have hHb := SignedPoint.outer_bounds hHs hHo
  by_cases horder : H.a≤D.a
  · obtain ⟨F⟩ := ordered_endpoint hQL hQU ⟨hDb.1,hDb.2.2⟩ horder
      hu hv ht0 ht hEs hEc
      (by simpa [quarterFeasible,quarterProjection] using hDE)
      (by simpa [quarterFeasible,quarterProjection,add_comm,add_left_comm,add_assoc] using hEH)
    refine ⟨{
      point := F.point
      deError := F.firstError
      de_mem := F.first_mem
      sorted := F.sorted
      outer := F.outer
      core := F.avoids_core
      DE := by simpa [quarterFeasible,quarterProjection] using F.first_feasible
      EH := by simpa [quarterFeasible,quarterProjection,add_comm,add_left_comm,add_assoc] using F.second_feasible
      de_guard := ?_
      eh_guard := Or.inr F.lower_strict
      terminal := ?_ }⟩
    · by_cases hz : F.firstError=0
      · exact Or.inr (F.aligned_upper_strict hz)
      · exact Or.inl (lt_of_le_of_ne F.first_mem.1 (Ne.symm hz))
    · rcases F.endpoint with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (by rw [hh,abs_of_pos F.sorted.1]))
  · have horder' : D.a≤H.a := (lt_of_not_ge horder).le
    obtain ⟨F⟩ := ordered_endpoint (p := E.reflect) (u := v) (v := u)
      hQL hQU ⟨hHb.1,hHb.2.2⟩ horder' hv hu (by simpa [add_comm] using ht0)
      (by simpa [add_comm] using ht)
      ((SignedPoint.reflect_sorted E).mpr hEs) ((SignedPoint.reflect_contained E q).mpr hEc)
      (by simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc] using hEH)
      (by simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using hDE)
    let d := u+v-F.firstError
    have hr : u+v-d=F.firstError := by dsimp [d]; ring
    have hother : v+u-F.firstError=d := by dsimp [d]; ring
    refine ⟨{
      point := F.point.reflect
      deError := d
      de_mem := ⟨by dsimp [d]; linarith [F.first_mem.2],by dsimp [d]; linarith [F.first_mem.1]⟩
      sorted := (SignedPoint.reflect_sorted F.point).mpr F.sorted
      outer := (SignedPoint.reflect_outer F.point q).mpr F.outer
      core := (SignedPoint.reflect_avoidsCore F.point).mpr F.avoids_core
      DE := ?_
      EH := ?_
      de_guard := Or.inr (by dsimp [SignedPoint.reflect]; linarith [F.lower_strict])
      eh_guard := ?_
      terminal := ?_ }⟩
    · have hh := F.second_feasible
      rw [hother] at hh
      simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using hh
    · rw [hr]
      simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using F.first_feasible
    · by_cases hz : F.firstError=0
      · right
        have hh := F.aligned_upper_strict hz
        dsimp [SignedPoint.reflect]
        linarith
      · left
        rw [hr]
        exact lt_of_le_of_ne F.first_mem.1 (Ne.symm hz)
    · rcases F.endpoint with hh | hh | hh
      · right; left
        dsimp [d]
        linarith
      · left
        dsimp [d]
        linarith
      · right; right
        simp [SignedPoint.reflect,hh,abs_of_pos F.sorted.1]

theorem DE_aligned {q t : ℝ} {D H : SignedPoint} (F : Endpoint q D H t)
    (hd : F.deError=0) : quarterFeasible D F.point 0 2 := by
  have hh := F.DE
  simpa [hd,quarterFeasible,quarterProjection] using hh

theorem EH_aligned {q t : ℝ} {D H : SignedPoint} (F : Endpoint q D H t)
    (he : F.deError=t) : quarterFeasible F.point H 0 0 := by
  have hh := F.EH
  simpa [he,quarterFeasible,quarterProjection] using hh

end SquaresInCircles.Eight.TableFree.PositiveEPair
