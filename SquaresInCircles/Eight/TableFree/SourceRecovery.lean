module

public import SquaresInCircles.Eight.TableFree.HardRigidity
public import SquaresInCircles.Eight.TableFree.PhysicalCycle
public import SquaresInCircles.Eight.TableFree.SourceEquality
public import SquaresInCircles.Eight.TableFree.NegativePrimaryPreprocessing

/-!
# Retained-contact obstructions on the source of independent pair moves

Uncompiled draft. This module connects the exact physical endpoint theorem
to signed necessary cycles. It proves that replacing the opposite free
intermediate preserves a strict HG or TD contact literally, and that
unchanged anchors preserve the two signed total frame differences.

The resulting equality obstructions are applied to an explicitly supplied
aligned endpoint with actual weak witnesses. No existence of such an
endpoint from arbitrary hard owners is assumed or claimed. In particular
these lemmas do not identify a moved G or T with its original point.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
namespace SourceRecovery
open Candidate GeometricModel ExactFamily

/-- This records the final two physical frame directions, before identifying
the tilt with the geometric minimizer. -/
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

/-- Every allowed owner at an aligned endpoint has the same tight physical
normal; this includes a retained transverse owner from an earlier pair move. -/
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

/-- These are actual anchor-circle equalities. They are not asserted of G
or T, whose unused transverse directions remain free. -/
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

def gTotal (C : SignedCycle) : ℝ := C.theta A-C.theta H
def tTotal (C : SignedCycle) : ℝ := C.theta D-C.theta B

theorem totals_of_anchors_unchanged {C D : SignedCycle}
    (h : AnchorsUnchanged C D) : gTotal C=gTotal D ∧ tTotal C=tTotal D := by
  have hH := (h H (by simp [anchorVertices])).2
  have hA := (h A (by simp [anchorVertices])).2
  have hB := (h B (by simp [anchorVertices])).2
  have hD := (h Candidate.D (by simp [anchorVertices])).2
  simp only [gTotal,tTotal,hH,hA,hB,hD,and_self]

theorem replace_nonincident_slack (C : SignedCycle) {v i : Vertex}
    (point : SignedPoint) (theta : ℝ) (j : Fin 4)
    (hi : i≠v) (hn : next i≠v) :
    (replacePoint C v point theta).slack i j=C.slack i j := by
  simp [SignedCycle.slack,SignedCycle.edge,replacePoint,delta,hi,hn,
    Function.update_of_ne]

theorem hg_slack_after_t (C : SignedCycle) (point : SignedPoint)
    (theta : ℝ) (j : Fin 4) :
    (replacePoint C T point theta).slack H j=C.slack H j :=
  replace_nonincident_slack C point theta j (by decide) (by decide)

theorem td_slack_after_g (C : SignedCycle) (point : SignedPoint)
    (theta : ℝ) (j : Fin 4) :
    (replacePoint C G point theta).slack T j=C.slack T j :=
  replace_nonincident_slack C point theta j (by decide) (by decide)

theorem negative_g_strict_after_t {C : SignedCycle} {q : ℝ}
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G))
    (hne : C.theta G≠C.theta H) (pT : SignedPoint) (tT : ℝ) :
    0<(replacePoint (replacePoint C G O.point O.theta) T pT tT).slack H O.owner := by
  rw [hg_slack_after_t]
  exact SignedCycle.negativeG_strict_source_slack O hne

theorem negative_t_strict_after_g {C : SignedCycle} {q : ℝ}
    (O : NegativeTEndpoint q (C.point B) (C.point D)
      (C.theta B) (C.theta D) (C.theta T))
    (hne : C.theta T≠C.theta D) (pG : SignedPoint) (tG : ℝ) :
    0<(replacePoint (replacePoint C T O.point O.theta) G pG tG).slack T O.owner := by
  rw [td_slack_after_g]
  have hh := O.strict_if_unaligned hne
  simpa [SignedCycle.slack,SignedCycle.edge,replacePoint,word,delta,next,T,D]
    using sub_pos.mpr hh

/-- A positive total at the original anchors or a retained strict HG slack
cannot lead, by anchor-preserving moves, to a sharp aligned endpoint. -/
theorem no_g_source_obstruction {C D : SignedCycle} {t q : ℝ}
    (hanchors : AnchorsUnchanged C D)
    (ht : 0≤t ∧ t≤Real.pi/4) (htheta : D.theta=endpointTheta t)
    (hs : ∀ i, (D.point i).Sorted) (hc : ∀ i, (D.point i).Contained q)
    (p : Vertex → Fin 4) (hp : ∀ i, p i∈terminalOwners i)
    (hf : ∀ i, D.Feasible i (p i)) (hq : q≤qStar)
    (j : Fin 4) (hj : j=0 ∨ j=2) :
    ¬ HardEndpointObstruction (gTotal C) (D.slack H j) := by
  obtain ⟨hangle,hzero⟩ := endpoint_all_slacks_zero ht htheta hs hc p hp hf hq
  have htotal : gTotal C= -t := by
    rw [(totals_of_anchors_unchanged hanchors).1]
    simp [gTotal,htheta,endpointTheta,A,H]
  have hcontact : D.slack H j=0 := hzero H j (by
    rcases hj with rfl | rfl <;> simp [terminalOwners,H])
  rintro (hpositive | hstrict)
  · rw [htotal] at hpositive
    linarith [ht.1]
  · rw [hcontact] at hstrict
    exact (lt_irrefl 0) hstrict

/-- The reflected total is zero at the endpoint. No sign normalization of E
is involved in this source obstruction. -/
theorem no_t_source_obstruction {C D : SignedCycle} {t q : ℝ}
    (hanchors : AnchorsUnchanged C D)
    (ht : 0≤t ∧ t≤Real.pi/4) (htheta : D.theta=endpointTheta t)
    (hs : ∀ i, (D.point i).Sorted) (hc : ∀ i, (D.point i).Contained q)
    (p : Vertex → Fin 4) (hp : ∀ i, p i∈terminalOwners i)
    (hf : ∀ i, D.Feasible i (p i)) (hq : q≤qStar)
    (j : Fin 4) (hj : j=0 ∨ j=2) :
    ¬ HardEndpointObstruction (tTotal C) (D.slack T j) := by
  obtain ⟨hangle,hzero⟩ := endpoint_all_slacks_zero ht htheta hs hc p hp hf hq
  have htotal : tTotal C=0 := by
    rw [(totals_of_anchors_unchanged hanchors).2]
    simp [tTotal,htheta,endpointTheta,Candidate.D,B]
  have hcontact : D.slack T j=0 := hzero T j (by
    rcases hj with rfl | rfl <;> simp [terminalOwners,T])
  exact fun h => t_obstruction_incompatible_with_hard_equality htotal hcontact h

end SourceRecovery
end SquaresInCircles.Eight.TableFree
