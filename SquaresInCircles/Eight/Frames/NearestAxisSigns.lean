module

public import SquaresInCircles.Eight.Boundary.Realization

/-!
# Eight squares: diagonal ties on the zero edges

At a sorted point on a diagonal the local angle is `±π/4` (`localAngle_of_positive_diagonal`,
`localAngle_of_negative_diagonal`). On an edge with quarter increment zero, a negative diagonal at
the source, or a positive diagonal at the target, would make the physical gap smaller than the
frame cap, against a gap above `19/25` (`zero_source_negative_diagonal_impossible`,
`zero_target_positive_diagonal_impossible`). This applies to every ordered signed cycle on the
boundary at a level `q ≤ Q0` with feasible owners, whose gaps exceed `19/25`
(`realized_zero_tie_exclusions`). The opposite diagonals of G and T recode to another binary
quarter word, which the word argument excludes.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem localAngle_of_positive_diagonal {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hd : (C.point i).y=(C.point i).a) :
    C.localAngle i=Real.pi/4 := by
  simp [localAngle,hd,ne_of_gt hs.1,Real.arctan_one]

theorem localAngle_of_negative_diagonal {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hd : (C.point i).y= -(C.point i).a) :
    C.localAngle i= -(Real.pi/4) := by
  simp [localAngle,hd,ne_of_gt hs.1,Real.arctan_neg,Real.arctan_one]

theorem zero_source_negative_diagonal_impossible {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hf : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) (hg : 19/25<C.physicalGap i) :
    (C.point i).y≠ -(C.point i).a := by
  intro hd
  have hsource := localAngle_of_negative_diagonal (hs i) hd
  have htarget := (localAngle_mem hs (next i)).1
  have hdelta := (abs_lt.mp (hf (next i) i)).2
  have hgap : C.physicalGap i=
      delta C.theta i+C.localAngle i-C.localAngle (next i) := by
    simp [physicalGap,hw]
  rw [hgap,hsource] at hg
  dsimp [delta] at hg
  dsimp [delta,frameCap] at hdelta
  linarith

theorem zero_target_positive_diagonal_impossible {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hf : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) (hg : 19/25<C.physicalGap i) :
    (C.point (next i)).y≠(C.point (next i)).a := by
  intro hd
  have htarget := localAngle_of_positive_diagonal (hs (next i)) hd
  have hsource := (localAngle_mem hs i).2
  have hdelta := (abs_lt.mp (hf (next i) i)).2
  have hgap : C.physicalGap i=
      delta C.theta i+C.localAngle i-C.localAngle (next i) := by
    simp [physicalGap,hw]
  rw [hgap,htarget] at hg
  dsimp [delta] at hg
  dsimp [delta,frameCap] at hdelta
  linarith

/-- The two exclusions for an ordered signed cycle on the boundary at a level `q ≤ Q0` with
feasible owners: its gaps exceed `19/25` by `realized_gap_lower`. -/
theorem realized_zero_tie_exclusions {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (howner : ∀ i,C.Feasible i (owner i))
    (hq : q≤Q0) (hs : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) :
    (C.point i).y≠ -(C.point i).a ∧
      (C.point (next i)).y≠(C.point (next i)).a := by
  have hg := C.realized_gap_lower hn ho hr owner howner hq i
  exact ⟨zero_source_negative_diagonal_impossible hn.sorted hs hw hg,
    zero_target_positive_diagonal_impossible hn.sorted hs hw hg⟩

end SignedCycle
end SquaresInCircles.Eight
