module
public import SquaresInCircles.Six.Classification.DiagonalEdges
public import SquaresInCircles.Six.Stress.ExactCover

@[expose] public section

/-!
# A2.3 diagonal-edge classification

For the W-own / S-own bit pair (Patterns 28--31), the Appendix-C rows, repaired
hard table and exact-support bridge rows eliminate every noncandidate D-edge
source. The surviving graph is W-secondary / S-secondary.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

private def q23 (r : ℚ) : PiBound := ⟨r,0⟩
private def p23 (r : ℚ) : PiBound := ⟨0,r⟩
private def edgeBox23 (wl wu sl su : PiBound) : PiBox :=
  ![(wl,wu),(sl,su),(q23 (1/2),p23 (1/4))]

private lemma mem_edgeBox23 {w s d : ℝ} {wl wu sl su : PiBound}
    (hw : wl.value≤w ∧ w≤wu.value) (hs : sl.value≤s ∧ s≤su.value)
    (hd : (q23 (1/2)).value≤d ∧ d≤(p23 (1/4)).value) :
    (edgeBox23 wl wu sl su).Mem ![w,s,d] := by
  intro i
  fin_cases i
  · simpa [edgeBox23] using hw
  · simpa [edgeBox23] using hs
  · simpa [edgeBox23] using hd

private abbrev fullW23 : PiBound × PiBound := (q23 (-2/3),p23 (1/4))
private abbrev negW23 : PiBound × PiBound := (q23 (-2/3),q23 0)
private abbrev fullS23 : PiBound × PiBound := (p23 (-1/4),p23 (1/4))
private abbrev posPrimaryS23 : PiBound × PiBound := (p23 (-1/12),p23 (1/4))
private abbrev negPrimaryS23 : PiBound × PiBound := (p23 (-1/4),p23 (-1/12))

private theorem cover23_2_1 : ExactCover.certify ⟨true,true,2,1⟩ 256
    (edgeBox23 fullW23.1 fullW23.2 fullS23.1 fullS23.2)=true := by decide
private theorem cover23_2_2 : ExactCover.certify ⟨true,true,2,2⟩ 256
    (edgeBox23 fullW23.1 fullW23.2 fullS23.1 fullS23.2)=true := by decide
private theorem cover23_2_4 : ExactCover.certify ⟨true,true,2,4⟩ 256
    (edgeBox23 fullW23.1 fullW23.2 posPrimaryS23.1 posPrimaryS23.2)=true := by decide
private theorem cover23_2_5 : ExactCover.certify ⟨true,true,2,5⟩ 256
    (edgeBox23 fullW23.1 fullW23.2 negPrimaryS23.1 negPrimaryS23.2)=true := by decide
private theorem cover23_6_1 : ExactCover.certify ⟨true,true,6,1⟩ 256
    (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2)=true := by decide
private theorem cover23_6_2 : ExactCover.certify ⟨true,true,6,2⟩ 256
    (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2)=true := by decide
private theorem cover23_6_4 : ExactCover.certify ⟨true,true,6,4⟩ 256
    (edgeBox23 negW23.1 negW23.2 posPrimaryS23.1 posPrimaryS23.2)=true := by decide
private theorem cover23_6_5 : ExactCover.certify ⟨true,true,6,5⟩ 256
    (edgeBox23 negW23.1 negW23.2 negPrimaryS23.1 negPrimaryS23.2)=true := by decide
private theorem cover23_6_6 : ExactCover.certify ⟨true,true,6,6⟩ 256
    (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2)=true := by decide

/-- The common A2.3 D-edge classification for Patterns 28--31. -/
theorem a23_candidate_diagonal_edges {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    DWSelected P 2 ∧ DSSelected P 6 ∧ 1/2<P.diagonalAngle := by
  obtain ⟨i,j,hwd,hds,hi,hj,hdhigh,hown⟩ := diagonal_edges_exist P
  obtain ⟨⟨hwlo,hwup⟩,⟨hslo,hsup⟩,⟨_,hdhi⟩,horder⟩ := baseline_ranges P
  have hdfull : (q23 (1/2)).value≤P.diagonalAngle ∧
      P.diagonalAngle≤(p23 (1/4)).value := by
    simp [q23,p23,PiBound.value]
    exact ⟨hdhigh.le,hdhi⟩
  have hwfull : fullW23.1.value≤P.helperAngle 2 ∧ P.helperAngle 2≤fullW23.2.value := by
    simp [fullW23,q23,p23,PiBound.value]
    exact ⟨hwlo.le,hwup.le⟩
  have hsfull : fullS23.1.value≤P.helperAngle 4 ∧ P.helperAngle 4≤fullS23.2.value := by
    simp [fullS23,p23,PiBound.value]
    exact ⟨hslo.le,hsup.le⟩
  have excludeFull (wd ds : Fin 8)
      (hc : ExactCover.certify ⟨true,true,wd,ds⟩ 256
        (edgeBox23 fullW23.1 fullW23.2 fullS23.1 fullS23.2)=true)
      (hwd' : DWSelected P wd) (hds' : DSSelected P ds) : False := by
    exact ExactCover.excludes ⟨true,true,wd,ds⟩ 256
      (edgeBox23 fullW23.1 fullW23.2 fullS23.1 fullS23.2) hc P hW hS hwd' hds'
      (mem_edgeBox23 hwfull hsfull hdfull) horder.le
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 2 1 cover23_2_1 hwd hds)
    · exact False.elim (excludeFull 2 2 cover23_2_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS23.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS23.2.value := by
        simp [posPrimaryS23,p23,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsup.le⟩
      exact False.elim (ExactCover.excludes ⟨true,true,2,4⟩ 256
        (edgeBox23 fullW23.1 fullW23.2 posPrimaryS23.1 posPrimaryS23.2) cover23_2_4
        P hW hS hwd hds (mem_edgeBox23 hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS23.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS23.2.value := by
        simp [negPrimaryS23,p23,PiBound.value]
        exact ⟨hslo.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨true,true,2,5⟩ 256
        (edgeBox23 fullW23.1 fullW23.2 negPrimaryS23.1 negPrimaryS23.2) cover23_2_5
        P hW hS hwd hds (mem_edgeBox23 hwfull hsneg hdfull) horder.le)
    · exact ⟨hwd,hds,hdhigh⟩
  · have hwneg : P.helperAngle 2<0 := by
      by_contra! hn
      have hh := hown hW hn
      norm_num at hh
    have hwn : negW23.1.value≤P.helperAngle 2 ∧ P.helperAngle 2≤negW23.2.value := by
      simp [negW23,q23,PiBound.value]
      exact ⟨hwlo.le,hwneg.le⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (ExactCover.excludes ⟨true,true,6,1⟩ 256
        (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2) cover23_6_1
        P hW hS hwd hds (mem_edgeBox23 hwn hsfull hdfull) horder.le)
    · exact False.elim (ExactCover.excludes ⟨true,true,6,2⟩ 256
        (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2) cover23_6_2
        P hW hS hwd hds (mem_edgeBox23 hwn hsfull hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS23.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS23.2.value := by
        simp [posPrimaryS23,p23,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsup.le⟩
      exact False.elim (ExactCover.excludes ⟨true,true,6,4⟩ 256
        (edgeBox23 negW23.1 negW23.2 posPrimaryS23.1 posPrimaryS23.2) cover23_6_4
        P hW hS hwd hds (mem_edgeBox23 hwn hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS23.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS23.2.value := by
        simp [negPrimaryS23,p23,PiBound.value]
        exact ⟨hslo.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨true,true,6,5⟩ 256
        (edgeBox23 negW23.1 negW23.2 negPrimaryS23.1 negPrimaryS23.2) cover23_6_5
        P hW hS hwd hds (mem_edgeBox23 hwn hsneg hdfull) horder.le)
    · exact False.elim (ExactCover.excludes ⟨true,true,6,6⟩ 256
        (edgeBox23 negW23.1 negW23.2 fullS23.1 fullS23.2) cover23_6_6
        P hW hS hwd hds (mem_edgeBox23 hwn hsfull hdfull) horder.le)

end SquaresInCircles.Six.Classification
