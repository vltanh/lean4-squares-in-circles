module

public import SquaresInCircles.Eight.TableFree.SourceAwareBoundaryPreprocessing
public import SquaresInCircles.Eight.TableFree.NonpositiveOuterSharp

/-!
# Recovering hard axes on the untouched primary source

Uncompiled source draft.  The two source-aware pair constructions retain
the original positive-total or strict-contact obstruction when a missing
hard axis becomes feasible.  Actual sharp contact equalities therefore
force both hard axes to have been available on the initial source.

Only after that conclusion do the constructors' `fixed_if_hard` fields
identify the descendant with the source.  In particular a moved point is
never declared equal to its ancestor merely because an endpoint is sharp.
The final theorem instantiates this argument with the full nonpositive
hard terminal; the global primary-owner entry remains a separate gate.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

namespace SignedCycle.BoundaryInput

/-- Exact source recovery from the two retained contact obstructions.
The hypotheses are literal descendant inequalities and slack equalities,
and the conclusion is about actual original GA0 and BT2 feasibility. -/
theorem original_hard_of_pair_contacts {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGA : (I.pairDescendant hq SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hq SG.output ST.output).cycle.Feasible B 2)
    (hGtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta H)
    (hTtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta B)
    (hHG : (I.pairDescendant hq SG.output ST.output).cycle.slack H SG.output.hgOwner=0)
    (hTD : (I.pairDescendant hq SG.output ST.output).cycle.slack T ST.output.tdOwner=0) :
    I.cycle.HardOwners := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hGsource : I.cycle.theta A≤I.cycle.theta H := by
    have h1 := (ha A (by simp [anchorVertices])).2
    have h2 := (ha H (by simp [anchorVertices])).2
    linarith
  have hTsource : I.cycle.theta D≤I.cycle.theta B := by
    have h1 := (ha D (by simp [anchorVertices])).2
    have h2 := (ha B (by simp [anchorVertices])).2
    linarith
  constructor
  · by_contra hnot
    rcases I.pairDescendant_g_source_obstruction hq SG ST hnot hGA with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hGsource)) ht
    · rw [hHG] at hs
      exact (lt_irrefl 0) hs
  · by_contra hnot
    rcases I.pairDescendant_t_source_obstruction hq SG ST hnot hBT with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hTsource)) ht
    · rw [hTD] at hs
      exact (lt_irrefl 0) hs

/-- Once the original hard axes have been proved feasible, source-aware
preprocessing fixes both intermediates; all five anchors were already fixed. -/
theorem pairDescendant_eq_original_of_hard {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hhard : I.cycle.HardOwners) :
    (I.pairDescendant hq SG.output ST.output).cycle=I.cycle := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hfixed := I.pairDescendant_fixed_sources hq SG ST
  have hG := hfixed.1 hhard.1
  have hT := hfixed.2 hhard.2
  have hpoint : (I.pairDescendant hq SG.output ST.output).cycle.point=I.cycle.point := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.1
    by_cases hiT : i=T
    · subst i; exact hT.1
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).1
  have htheta : (I.pairDescendant hq SG.output ST.output).cycle.theta=I.cycle.theta := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.2
    by_cases hiT : i=T
    · subst i; exact hT.2
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).2
  have hext : ∀ C D : SignedCycle, C.point=D.point → C.theta=D.theta → C=D := by
    rintro ⟨p,t⟩ ⟨p',t'⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    rfl
  exact hext _ _ hpoint htheta

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

/-- The actual nonpositive hard terminal recovers both original hard
witnesses and every original signed point and frame.  The descendant
geometry is explicit; no sharpness or source-equality premise is supplied. -/
theorem nonpositive_pair_source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap)
    (hGA : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible B 2)
    (hAB : (I.pairDescendant hcap SG.output ST.output).cycle.theta A=
      (I.pairDescendant hcap SG.output ST.output).cycle.theta B)
    (hnorm : ((I.pairDescendant hcap SG.output ST.output).cycle.point A).y-
      ((I.pairDescendant hcap SG.output ST.output).cycle.point B).y=1)
    (hAG : (I.pairDescendant hcap SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta G)
    (hGH : (I.pairDescendant hcap SG.output ST.output).cycle.theta G≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta H)
    (hDT : (I.pairDescendant hcap SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta T)
    (hTB : (I.pairDescendant hcap SG.output ST.output).cycle.theta T≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta B) :
    I.cycle.HardOwners ∧
      (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  let J := I.pairDescendant hcap SG.output ST.output
  let K := J.toHard hGA hBT
  have hs := K.nonpositive_owner_sharp hqL hqq hAB hnorm hAG hGH hDT hTB
  have hslack : ∀i j,j∈terminalOwners i → J.cycle.slack i j=0 := hs.2.2.2.2.2.2.2
  have hHGzero : J.cycle.slack H SG.output.hgOwner=0 := by
    apply hslack
    rcases SG.output.hg_allowed with h | h <;> simp [h,terminalOwners,H]
  have hTDzero : J.cycle.slack T ST.output.tdOwner=0 := by
    apply hslack
    rcases ST.output.td_allowed with h | h <;> simp [h,terminalOwners,T]
  have hhard := I.toBoundaryInput.original_hard_of_pair_contacts hcap SG ST hGA hBT
    (hAG.trans hGH) (hDT.trans hTB) hHGzero hTDzero
  have heq := I.toBoundaryInput.pairDescendant_eq_original_of_hard hcap SG ST hhard
  refine ⟨hhard,heq,?_⟩
  change q=qStar ∧ J.cycle.theta G=J.cycle.theta H ∧
    J.cycle.theta B=J.cycle.theta T ∧ J.cycle.theta T=J.cycle.theta D ∧
    J.cycle.theta E=J.cycle.theta D ∧
    J.cycle.theta H-J.cycle.theta D=FiveCorner.selected.angle ∧
    AllAnchorsOn qStar J.cycle ∧
    ∀i j,j∈terminalOwners i → J.cycle.slack i j=0 at hs
  simpa only [show J.cycle=I.cycle from heq] using hs

/-- Source recovery also requires no original or descendant AB
normalization: the hard-middle theorem derives it with its source loss
ledger before the retained-contact argument is applied. -/
theorem nonpositive_outer_pair_source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap)
    (hGA : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible B 2)
    (hGH : (I.pairDescendant hcap SG.output ST.output).cycle.theta G≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta H)
    (hDT : (I.pairDescendant hcap SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta T) :
    I.cycle.HardOwners ∧
      (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle := by
  let J := I.pairDescendant hcap SG.output ST.output
  let K := J.toHard hGA hBT
  obtain ⟨hAB,hrange,hnorm⟩ := K.nonpositive_outer_middle hqL hqq hGH hDT
  have hTB : J.cycle.theta T≤J.cycle.theta B := by
    have h1 : J.cycle.theta T≤J.cycle.theta A := hrange.1
    have h2 : J.cycle.theta A=J.cycle.theta B := hAB
    linarith
  have hs := I.nonpositive_pair_source_recovery hqL hqq SG ST hcap hGA hBT
    hAB hnorm hrange.2 hGH hDT hTB
  exact ⟨hs.1,hs.2.1⟩

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight.TableFree
