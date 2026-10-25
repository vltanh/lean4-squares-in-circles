module

public import SquaresInCircles.Eight.Frames.Pair.Order
public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly

/-!
# Eight squares: the boundary input after the two pair moves

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
