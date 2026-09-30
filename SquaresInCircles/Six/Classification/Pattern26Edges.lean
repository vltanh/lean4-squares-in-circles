import SquaresInCircles.Six.Classification.DiagonalEdges
import SquaresInCircles.Six.Stress.ExactCover

/-!
# W-cardinal / S-own diagonal-edge classification

This is the common fixed-stress classification used by Patterns 24--27. The
39 Pattern-26 Appendix-C rows eliminate every noncandidate D-edge source on
the normalized domain. The only surviving graph is W-secondary/S-secondary.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

private def q26 (r : ℚ) : PiBound := ⟨r,0⟩
private def p26 (r : ℚ) : PiBound := ⟨0,r⟩
private def edgeBox26 (wl wu sl su : PiBound) : PiBox :=
  ![(wl,wu),(sl,su),(q26 (1/2),p26 (1/4))]

private lemma mem_edgeBox26 {w s d : ℝ} {wl wu sl su : PiBound}
    (hw : wl.value≤w ∧ w≤wu.value) (hs : sl.value≤s ∧ s≤su.value)
    (hd : (q26 (1/2)).value≤d ∧ d≤(p26 (1/4)).value) :
    (edgeBox26 wl wu sl su).Mem ![w,s,d] := by
  intro i
  fin_cases i
  · simpa [edgeBox26] using hw
  · simpa [edgeBox26] using hs
  · simpa [edgeBox26] using hd

private abbrev fullW26 : PiBound × PiBound := (q26 (-2/5),q26 (2/5))
private abbrev fullS26 : PiBound × PiBound := (p26 (-1/4),p26 (1/4))
private abbrev posPrimaryS26 : PiBound × PiBound := (p26 (-1/12),p26 (1/4))
private abbrev negPrimaryS26 : PiBound × PiBound := (p26 (-1/4),p26 (-1/12))

private theorem cover26_2_1 : ExactCover.certify ⟨false,true,2,1⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true := by decide
private theorem cover26_2_2 : ExactCover.certify ⟨false,true,2,2⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true := by decide
private theorem cover26_2_4 : ExactCover.certify ⟨false,true,2,4⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 posPrimaryS26.1 posPrimaryS26.2)=true := by decide
private theorem cover26_2_5 : ExactCover.certify ⟨false,true,2,5⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 negPrimaryS26.1 negPrimaryS26.2)=true := by decide
private theorem cover26_6_1 : ExactCover.certify ⟨false,true,6,1⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true := by decide
private theorem cover26_6_2 : ExactCover.certify ⟨false,true,6,2⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true := by decide
private theorem cover26_6_4 : ExactCover.certify ⟨false,true,6,4⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 posPrimaryS26.1 posPrimaryS26.2)=true := by decide
private theorem cover26_6_5 : ExactCover.certify ⟨false,true,6,5⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 negPrimaryS26.1 negPrimaryS26.2)=true := by decide
private theorem cover26_6_6 : ExactCover.certify ⟨false,true,6,6⟩ 256
    (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true := by decide

/-- Common D-edge classification for the W-cardinal/S-own family. -/
theorem cardinalW_ownS_candidate_diagonal_edges {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=true) :
    DWSelected P 2 ∧ DSSelected P 6 ∧ 1/2<P.diagonalAngle := by
  obtain ⟨i,j,hwd,hds,hi,hj,hdhigh,_⟩ := diagonal_edges_exist P
  obtain ⟨_,⟨hslo,hsup⟩,⟨_,hdhi⟩,horder⟩ := baseline_ranges P
  have hwabs := abs_lt.mp (P.cardinal_angle 2 hW)
  have hdfull : (q26 (1/2)).value≤P.diagonalAngle ∧
      P.diagonalAngle≤(p26 (1/4)).value := by
    simp [q26,p26,PiBound.value]
    exact ⟨hdhigh.le,hdhi⟩
  have hwfull : fullW26.1.value≤P.helperAngle 2 ∧ P.helperAngle 2≤fullW26.2.value := by
    simp [fullW26,q26,PiBound.value]
    exact ⟨hwabs.1.le,hwabs.2.le⟩
  have hsfull : fullS26.1.value≤P.helperAngle 4 ∧ P.helperAngle 4≤fullS26.2.value := by
    simp [fullS26,p26,PiBound.value]
    exact ⟨hslo.le,hsup.le⟩
  have excludeFull (wd ds : Fin 8)
      (hc : ExactCover.certify ⟨false,true,wd,ds⟩ 256
        (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2)=true)
      (hwd' : DWSelected P wd) (hds' : DSSelected P ds) : False := by
    exact ExactCover.excludes ⟨false,true,wd,ds⟩ 256
      (edgeBox26 fullW26.1 fullW26.2 fullS26.1 fullS26.2) hc P hW hS hwd' hds'
      (mem_edgeBox26 hwfull hsfull hdfull) horder.le
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 2 1 cover26_2_1 hwd hds)
    · exact False.elim (excludeFull 2 2 cover26_2_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS26.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS26.2.value := by
        simp [posPrimaryS26,p26,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsup.le⟩
      exact False.elim (ExactCover.excludes ⟨false,true,2,4⟩ 256
        (edgeBox26 fullW26.1 fullW26.2 posPrimaryS26.1 posPrimaryS26.2) cover26_2_4
        P hW hS hwd hds (mem_edgeBox26 hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS26.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS26.2.value := by
        simp [negPrimaryS26,p26,PiBound.value]
        exact ⟨hslo.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨false,true,2,5⟩ 256
        (edgeBox26 fullW26.1 fullW26.2 negPrimaryS26.1 negPrimaryS26.2) cover26_2_5
        P hW hS hwd hds (mem_edgeBox26 hwfull hsneg hdfull) horder.le)
    · exact ⟨hwd,hds,hdhigh⟩
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 6 1 cover26_6_1 hwd hds)
    · exact False.elim (excludeFull 6 2 cover26_6_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS26.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS26.2.value := by
        simp [posPrimaryS26,p26,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsup.le⟩
      exact False.elim (ExactCover.excludes ⟨false,true,6,4⟩ 256
        (edgeBox26 fullW26.1 fullW26.2 posPrimaryS26.1 posPrimaryS26.2) cover26_6_4
        P hW hS hwd hds (mem_edgeBox26 hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS26.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS26.2.value := by
        simp [negPrimaryS26,p26,PiBound.value]
        exact ⟨hslo.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨false,true,6,5⟩ 256
        (edgeBox26 fullW26.1 fullW26.2 negPrimaryS26.1 negPrimaryS26.2) cover26_6_5
        P hW hS hwd hds (mem_edgeBox26 hwfull hsneg hdfull) horder.le)
    · exact False.elim (excludeFull 6 6 cover26_6_6 hwd hds)

end SquaresInCircles.Six.Classification
