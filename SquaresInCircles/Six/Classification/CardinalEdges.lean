import SquaresInCircles.Six.Classification.DiagonalEdges
import SquaresInCircles.Six.Stress.ExactCover

/-!
# Cardinal W/S diagonal-edge classification

For the W-cardinal / S-cardinal family (including Patterns 8 and 10), the
Pattern-10 fixed stresses eliminate every noncandidate D-edge source. The only
surviving graph is W-secondary/S-secondary.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

private def qc (r : ℚ) : PiBound := ⟨r,0⟩
private def pc (r : ℚ) : PiBound := ⟨0,r⟩
private def edgeBoxC (sl su : PiBound) : PiBox :=
  ![(qc (-2/5),qc (2/5)),(sl,su),(qc (1/2),pc (1/4))]

private lemma mem_edgeBoxC {w s d : ℝ} {sl su : PiBound}
    (hw : (qc (-2/5)).value≤w ∧ w≤(qc (2/5)).value)
    (hs : sl.value≤s ∧ s≤su.value)
    (hd : (qc (1/2)).value≤d ∧ d≤(pc (1/4)).value) :
    (edgeBoxC sl su).Mem ![w,s,d] := by
  intro i
  fin_cases i
  · simpa [edgeBoxC] using hw
  · simpa [edgeBoxC] using hs
  · simpa [edgeBoxC] using hd

private abbrev fullSC : PiBound × PiBound := (qc (-2/5),qc (2/5))
private abbrev posPrimarySC : PiBound × PiBound := (pc (-1/12),qc (2/5))
private abbrev negPrimarySC : PiBound × PiBound := (qc (-2/5),pc (-1/12))

private theorem coverC_2_1 : ExactCover.certify ⟨false,false,2,1⟩ 256
    (edgeBoxC fullSC.1 fullSC.2)=true := by decide
private theorem coverC_2_2 : ExactCover.certify ⟨false,false,2,2⟩ 256
    (edgeBoxC fullSC.1 fullSC.2)=true := by decide
private theorem coverC_2_4 : ExactCover.certify ⟨false,false,2,4⟩ 256
    (edgeBoxC posPrimarySC.1 posPrimarySC.2)=true := by decide
private theorem coverC_2_5 : ExactCover.certify ⟨false,false,2,5⟩ 256
    (edgeBoxC negPrimarySC.1 negPrimarySC.2)=true := by decide
private theorem coverC_6_1 : ExactCover.certify ⟨false,false,6,1⟩ 256
    (edgeBoxC fullSC.1 fullSC.2)=true := by decide
private theorem coverC_6_2 : ExactCover.certify ⟨false,false,6,2⟩ 256
    (edgeBoxC fullSC.1 fullSC.2)=true := by decide
private theorem coverC_6_4 : ExactCover.certify ⟨false,false,6,4⟩ 256
    (edgeBoxC posPrimarySC.1 posPrimarySC.2)=true := by decide
private theorem coverC_6_5 : ExactCover.certify ⟨false,false,6,5⟩ 256
    (edgeBoxC negPrimarySC.1 negPrimarySC.2)=true := by decide
private theorem coverC_6_6 : ExactCover.certify ⟨false,false,6,6⟩ 256
    (edgeBoxC fullSC.1 fullSC.2)=true := by decide

/-- Common D-edge classification when both W and S use cardinal central sides. -/
theorem cardinalWS_candidate_diagonal_edges {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    DWSelected P 2 ∧ DSSelected P 6 ∧ 1/2<P.diagonalAngle := by
  obtain ⟨i,j,hwd,hds,hi,hj,hdhigh,_⟩ := diagonal_edges_exist P
  obtain ⟨_,_,⟨_,hdhi⟩,horder⟩ := baseline_ranges P
  have hwabs := abs_lt.mp (P.cardinal_angle 2 hW)
  have hsabs := abs_lt.mp (P.cardinal_angle 4 hS)
  have hdfull : (qc (1/2)).value≤P.diagonalAngle ∧
      P.diagonalAngle≤(pc (1/4)).value := by
    simp [qc,pc,PiBound.value]
    exact ⟨hdhigh.le,hdhi⟩
  have hwfull : (qc (-2/5)).value≤P.helperAngle 2 ∧
      P.helperAngle 2≤(qc (2/5)).value := by
    simp [qc,PiBound.value]
    exact ⟨hwabs.1.le,hwabs.2.le⟩
  have hsfull : fullSC.1.value≤P.helperAngle 4 ∧ P.helperAngle 4≤fullSC.2.value := by
    simp [fullSC,qc,PiBound.value]
    exact ⟨hsabs.1.le,hsabs.2.le⟩
  have excludeFull (wd ds : Fin 8)
      (hc : ExactCover.certify ⟨false,false,wd,ds⟩ 256
        (edgeBoxC fullSC.1 fullSC.2)=true)
      (hwd' : DWSelected P wd) (hds' : DSSelected P ds) : False := by
    exact ExactCover.excludes ⟨false,false,wd,ds⟩ 256
      (edgeBoxC fullSC.1 fullSC.2) hc P hW hS hwd' hds'
      (mem_edgeBoxC hwfull hsfull hdfull) horder.le
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 2 1 coverC_2_1 hwd hds)
    · exact False.elim (excludeFull 2 2 coverC_2_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimarySC.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimarySC.2.value := by
        simp [posPrimarySC,pc,qc,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsabs.2.le⟩
      exact False.elim (ExactCover.excludes ⟨false,false,2,4⟩ 256
        (edgeBoxC posPrimarySC.1 posPrimarySC.2) coverC_2_4 P hW hS hwd hds
        (mem_edgeBoxC hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimarySC.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimarySC.2.value := by
        simp [negPrimarySC,pc,qc,PiBound.value]
        exact ⟨hsabs.1.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨false,false,2,5⟩ 256
        (edgeBoxC negPrimarySC.1 negPrimarySC.2) coverC_2_5 P hW hS hwd hds
        (mem_edgeBoxC hwfull hsneg hdfull) horder.le)
    · exact ⟨hwd,hds,hdhigh⟩
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 6 1 coverC_6_1 hwd hds)
    · exact False.elim (excludeFull 6 2 coverC_6_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimarySC.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimarySC.2.value := by
        simp [posPrimarySC,pc,qc,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsabs.2.le⟩
      exact False.elim (ExactCover.excludes ⟨false,false,6,4⟩ 256
        (edgeBoxC posPrimarySC.1 posPrimarySC.2) coverC_6_4 P hW hS hwd hds
        (mem_edgeBoxC hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimarySC.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimarySC.2.value := by
        simp [negPrimarySC,pc,qc,PiBound.value]
        exact ⟨hsabs.1.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨false,false,6,5⟩ 256
        (edgeBoxC negPrimarySC.1 negPrimarySC.2) coverC_6_5 P hW hS hwd hds
        (mem_edgeBoxC hwfull hsneg hdfull) horder.le)
    · exact False.elim (excludeFull 6 6 coverC_6_6 hwd hds)

end SquaresInCircles.Six.Classification
