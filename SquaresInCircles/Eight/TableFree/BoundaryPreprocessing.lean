module

public import SquaresInCircles.Eight.TableFree.PairOrder

/-!
# Same-radius boundary descendants for the complete primary-pair matrix

Uncompiled source. Both local output points are inserted into the actual
seven-cycle. The resulting `BoundaryInput` proves its physical order from
the endpoint geometry; it does not copy source gaps across a motion.

All five anchors and their physical frames are retained exactly. The four
local terminal alternatives on each side remain visible in the two output
records, so the subsequent global exclusions can inspect the actual
constructed points, signs, errors, and owners.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
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

/-- The actual composite endpoint, including a proved new cyclic order.
The selected owner record is constructed explicitly from the two transports
and the original retained edges. -/
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

/-- Both signed variation budgets are retained separately, including when
one source has cancelling frame errors. -/
theorem pairDescendant_variations {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    positiveVariation (I.pairDescendant hq OG OT).cycle.theta≤
        positiveVariation I.cycle.theta ∧
      negativeVariation (I.pairDescendant hq OG OT).cycle.theta≤
        negativeVariation I.cycle.theta := by
  have h := compose_primary_pair_outputs I.necessary I.radial I.witnesses
    I.zero_signs I.strict_spread OG OT
  exact ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩

/-- The finite owner matrix is the one belonging to the actual transported
points. Unchanged E edges retain their original selected axes. -/
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

/-- Every source in the complete boundary domain has an actual same-q
boundary descendant carrying both exhaustive local classifications. -/
theorem pair_preprocessing_boundary {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    ∃ (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
      (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
      (J : SignedCycle.BoundaryInput q),
      J.cycle=replacePoint (replacePoint I.cycle G OG.point OG.theta)
        T OT.point OT.theta ∧
      AnchorsUnchanged I.cycle J.cycle ∧
      positiveVariation J.cycle.theta≤positiveVariation I.cycle.theta ∧
      negativeVariation J.cycle.theta≤negativeVariation I.cycle.theta := by
  obtain ⟨OG⟩ := I.g_output hqL hqU
  obtain ⟨OT⟩ := I.t_output hqL hqU
  exact ⟨OG,OT,I.pairDescendant hqU OG OT,rfl,I.pairDescendant_anchors hqU OG OT,
    I.pairDescendant_variations hqU OG OT⟩

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

/-- E's signed tangent is retained as an actual unchanged anchor coordinate,
so the normalized descendant needs no new sign convention. -/
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

theorem pair_preprocessing_boundary {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    ∃ (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
      (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
      (J : SignedCycle.NormalizedBoundaryInput q),
      J.cycle=replacePoint (replacePoint I.cycle G OG.point OG.theta)
        T OT.point OT.theta ∧ AnchorsUnchanged I.cycle J.cycle := by
  obtain ⟨OG⟩ := I.toBoundaryInput.g_output hqL hqU
  obtain ⟨OT⟩ := I.toBoundaryInput.t_output hqL hqU
  exact ⟨OG,OT,I.pairDescendant hqU OG OT,rfl,
    I.toBoundaryInput.pairDescendant_anchors hqU OG OT⟩

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight.TableFree
