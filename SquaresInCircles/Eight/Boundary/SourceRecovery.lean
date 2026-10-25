module

public import SquaresInCircles.Eight.Owners.Hard.Rigidity
public import SquaresInCircles.Eight.Frames.PhysicalCycle

/-!
# Eight squares: the aligned endpoint

A signed cycle with the frame angles `endpointTheta t`, `t` for H and G and `0` for the others,
has the frames of the five-corner model (`physical_frames`). If its points are sorted and lie in
the disk of squared radius `q`, `0 ≤ t ≤ π/4`, and each edge has a feasible terminal owner
(`endpointWitnesses`), then `qStar ≤ q` (`endpoint_lower_bound`), by the theorem of the aligned
endpoint. If moreover `q ≤ qStar`, then `t` is the angle of `FiveCorner.selected`, every
terminal owner of every edge is tight (`endpoint_all_slacks_zero`), and the five anchors lie on
the circle of squared radius `qStar` (`endpoint_all_anchors_on`); G and T, which are not anchors,
keep a free transverse coordinate.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
namespace SourceRecovery
open Candidate GeometricModel Stationary

/-- The frame angles of the aligned endpoint: `t` for H and G, `0` for the others. -/
def endpointTheta (t : ℝ) : Vertex → ℝ := ![t,t,0,0,0,0,0]

theorem physical_frames {C : SignedCycle} {t : ℝ}
    (htheta : C.theta=endpointTheta t) :
    OriginalFiveCorner.PhysicalFrames C.actualSquare t := by
  intro i
  fin_cases i <;>
    simp [SignedCycle.actualSquare,SignedPoint.square,htheta,endpointTheta,
      offsets,OriginalFiveCorner.frameCos,OriginalFiveCorner.frameSin,
      Real.cos_add,Real.sin_add,neg_div,Real.cos_neg,Real.sin_neg,
      Real.cos_pi_div_two,Real.sin_pi_div_two]

def endpointWitnesses {C : SignedCycle} (p : Vertex → Fin 4)
    (hp : ∀ i, p i∈terminalOwners i) (hf : ∀ i, C.Feasible i (p i)) :
    AlignedEndpoint.Witnesses C.actualSquare where
  owner := p
  allowed := hp
  feasible i := (C.actualSquare_feasible i (p i)).2 (hf i)

theorem endpoint_lower_bound {C : SignedCycle} {t q : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (htheta : C.theta=endpointTheta t)
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q)
    (p : Vertex → Fin 4) (hp : ∀ i, p i∈terminalOwners i)
    (hf : ∀ i, C.Feasible i (p i)) : qStar≤q :=
  AlignedEndpoint.squared_radius_lower_bound ht (physical_frames htheta)
    (endpointWitnesses p hp hf) (SignedCycle.actualSquare_points_contained hs hc)

/-- At an aligned endpoint with `q ≤ qStar`, `t` is the angle of `FiveCorner.selected` and every
terminal owner of every edge is tight, whichever of them is the witness. -/
theorem endpoint_all_slacks_zero {C : SignedCycle} {t q : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (htheta : C.theta=endpointTheta t)
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q)
    (p : Vertex → Fin 4) (hp : ∀ i, p i∈terminalOwners i)
    (hf : ∀ i, C.Feasible i (p i)) (hq : q≤qStar) :
    t=FiveCorner.selected.angle ∧
      ∀ i j, j∈terminalOwners i → C.slack i j=0 := by
  have h := AlignedEndpoint.sharp_rigidity ht (physical_frames htheta)
    (endpointWitnesses p hp hf) (SignedCycle.actualSquare_points_contained hs hc) hq
  refine ⟨h.2.1,?_⟩
  intro i j hj
  rw [← C.actualSquare_margin]
  rw [AlignedEndpoint.actual_slack ht (physical_frames htheta) i j hj]
  exact h.2.2.2.2.1 i

/-- At an aligned endpoint with `q ≤ qStar`, the five anchors lie on the circle of squared radius
`qStar`; G and T need not. -/
theorem endpoint_all_anchors_on {C : SignedCycle} {t q : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (htheta : C.theta=endpointTheta t)
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q)
    (p : Vertex → Fin 4) (hp : ∀ i, p i∈terminalOwners i)
    (hf : ∀ i, C.Feasible i (p i)) (hq : q≤qStar) :
    AllAnchorsOn qStar C := by
  have hframes := physical_frames htheta
  have h := AlignedEndpoint.sharp_rigidity ht hframes
    (endpointWitnesses p hp hf) (SignedCycle.actualSquare_points_contained hs hc) hq
  have hpoint (j : Fin 5) :
      normSq ((OriginalFiveCorner.chain C.actualSquare t).point j)=qStar := by
    rw [h.2.2.1,FiveCorner.selected_point]
    exact Coordinates.anchor_circle sharpData_stationary.toIsChain
      sharpData_stationary.zero_defect j
  have hanchor (j : Fin 5) :
      (C.point (OriginalFiveCorner.anchorIndex j)).circle=qStar := by
    let i := OriginalFiveCorner.anchorIndex j
    have hown : (C.point i).Contained (C.point i).circle := le_rfl
    have hphys : SqContained (C.point i).circle (C.actualSquare i) :=
      (C.actualSquare_contained_iff hs _ i).2 hown
    have hvert := OriginalFiveCorner.corner_is_original_vertex hframes j
    have hbound := (SqContained.iff_points (C.point i).circle_nonneg _).1 hphys _ hvert
    have hcircle := hpoint j
    exact le_antisymm ((hc i).trans hq) (hcircle ▸ hbound)
  intro i hi
  fin_cases i
  · simpa [H,OriginalFiveCorner.anchorIndex] using hanchor 4
  · simp [anchorVertices,H,A,B,D,E] at hi
  · simpa [A,OriginalFiveCorner.anchorIndex] using hanchor 0
  · simpa [B,OriginalFiveCorner.anchorIndex] using hanchor 1
  · simp [anchorVertices,H,A,B,D,E] at hi
  · simpa [D,OriginalFiveCorner.anchorIndex] using hanchor 2
  · simpa [E,OriginalFiveCorner.anchorIndex] using hanchor 3

end SourceRecovery
end SquaresInCircles.Eight
