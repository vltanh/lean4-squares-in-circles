module

public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Frames.PhysicalCycle
public import SquaresInCircles.Eight.Owners.Hard.Rigidity

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

section
/-!
## The boundary input after the two pair moves

Replacing G and T in a boundary input `I` at a level `q ≤ qCap` by the outputs `OG` and `OT` of
the pair moves of G between H and A and of T between B and D gives a boundary input at the same
level (`BoundaryInput.pairDescendant`). Its cycle is that of `I` with the two points replaced
(`pairDescendant_cycle`); the five anchors H, A, B, D and E keep their points and frames
(`pairDescendant_anchors`); its witnesses are the owners of the outputs on H–G, G–A, B–T and T–D
and those of `I` on the other edges (`pairDescendant_owners`); and its physical order follows
from the geometry of the new points (`SignedCycle.normal_necessary_ordered`). The terminal
alternatives of the two moves stay in the records of the outputs. A normalized input gives a
normalized input, since E is an anchor (`NormalizedBoundaryInput.pairDescendant`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate

theorem AnchorsUnchanged.normal {C K : SignedCycle}
    (h : AnchorsUnchanged C K) (ha : C.NormalAnchors) : K.NormalAnchors := by
  constructor
  · rw [(h H (by simp [anchorVertices])).1]
    exact ha.H_nonneg
  · rw [(h A (by simp [anchorVertices])).1]
    exact ha.A_nonneg
  · rw [(h B (by simp [anchorVertices])).1]
    exact ha.B_nonpos
  · rw [(h D (by simp [anchorVertices])).1]
    exact ha.D_nonpos

namespace SignedCycle.BoundaryInput

/-- The boundary input with G and T replaced by the outputs of the two pair moves. Its order is
proved from the new points, and its witnesses come from the two outputs and, on the other edges,
from `I`. -/
def pairDescendant {q : ℝ} (I : SignedCycle.BoundaryInput q) (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    SignedCycle.BoundaryInput q := by
  let CG := OG.cycle I.cycle
  let OT' : TPairOutput q (CG.point B) (CG.point D)
      (CG.theta B) (CG.theta T) (CG.theta D) := OT
  let CD := OT'.cycle CG
  let wG := OG.witnesses I.witnesses
  let wD : CD.Witnesses := OT'.witnesses wG
  have hz : CD.ZeroSignImplications wD :=
    OT'.zero_signs wG (OG.zero_signs I.witnesses I.zero_signs)
  have h := compose_primary_pair_outputs I.necessary I.radial I.witnesses
    I.zero_signs I.strict_spread OG OT
  have hn : CD.Necessary q := h.1
  have ha : AnchorsUnchanged I.cycle CD := h.2.2.2.1
  have hnormal : CD.NormalAnchors := ha.normal I.anchors_normal
  exact {
    cycle := CD
    necessary := hn
    ordered := SignedCycle.normal_necessary_ordered hn hq hnormal wD hz
    strict_spread := h.2.2.1
    positive_variation := h.2.2.2.2.1.trans_lt I.positive_variation
    negative_variation := h.2.2.2.2.2.1.trans_lt I.negative_variation
    radial := h.2.1
    anchors_outer := by
      intro i hi
      have hi' : i∈anchorVertices := by
        simp only [anchorVertices,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
        tauto
      rw [(ha i hi').1]
      exact I.anchors_outer i hi
    anchors_normal := hnormal
    witnesses := wD
    zero_signs := hz }

@[simp] theorem pairDescendant_cycle {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    (I.pairDescendant hq OG OT).cycle=
      replacePoint (replacePoint I.cycle G OG.point OG.theta) T OT.point OT.theta := rfl

theorem pairDescendant_anchors {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    AnchorsUnchanged I.cycle (I.pairDescendant hq OG OT).cycle := by
  rw [pairDescendant_cycle]
  exact (replacement_anchors_unchanged I.cycle (Or.inl rfl) OG.point OG.theta).trans
    (replacement_anchors_unchanged (replacePoint I.cycle G OG.point OG.theta)
      (Or.inr rfl) OT.point OT.theta)

/-- The witnesses after the two moves: the owners of `OG` on H–G and G–A, those of `OT` on B–T
and T–D, and those of `I` on A–B, D–E and E–H. -/
theorem pairDescendant_owners {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    let w := (I.pairDescendant hq OG OT).witnesses
    w.owner H=OG.hgOwner ∧ w.owner G=OG.gaOwner ∧
      w.owner A=I.witnesses.owner A ∧ w.owner B=OT.btOwner ∧
      w.owner T=OT.tdOwner ∧ w.owner D=I.witnesses.owner D ∧
      w.owner E=I.witnesses.owner E := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

/-- The same for a normalized input: E is an anchor, so it keeps `y ≤ 0`. -/
def pairDescendant {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    SignedCycle.NormalizedBoundaryInput q where
  toBoundaryInput := I.toBoundaryInput.pairDescendant hq OG OT
  E_nonpos := by
    have he := (I.toBoundaryInput.pairDescendant_anchors hq OG OT E
      (by simp [anchorVertices])).1
    rw [he]
    exact I.E_nonpos

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight
end
end
end

section
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
end
end
end
