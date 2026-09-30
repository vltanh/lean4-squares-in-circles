module
public import SquaresInCircles.Six.Classification.DiagonalEdges
public import SquaresInCircles.Six.Stress.ExactCover

@[expose] public section

/-!
# A2.2 diagonal-edge classification

For the W-own / S-cardinal bit pair (Patterns 12 and 13), actual pairwise
separation and the audited fixed stresses force the candidate diagonal graph:
W--D uses W-secondary and D--S uses S-secondary. Primary-source sign ranges
come from the pin chords; no numerical source preference is assumed.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

private def q (r : ℚ) : PiBound := ⟨r,0⟩
private def p (r : ℚ) : PiBound := ⟨0,r⟩

private def edgeBox (wl wu sl su : PiBound) : PiBox :=
  ![(wl,wu),(sl,su),(q (1/2),p (1/4))]

private lemma mem_edgeBox {w s d : ℝ} {wl wu sl su : PiBound}
    (hw : wl.value≤w ∧ w≤wu.value) (hs : sl.value≤s ∧ s≤su.value)
    (hd : (q (1/2)).value≤d ∧ d≤(p (1/4)).value) :
    (edgeBox wl wu sl su).Mem ![w,s,d] := by
  intro i
  fin_cases i
  · simpa [edgeBox] using hw
  · simpa [edgeBox] using hs
  · simpa [edgeBox] using hd

private abbrev fullW : PiBound × PiBound := (q (-2/3),p (1/4))
private abbrev negW : PiBound × PiBound := (q (-2/3),q 0)
private abbrev fullS : PiBound × PiBound := (q (-2/5),q (2/5))
private abbrev posPrimaryS : PiBound × PiBound := (p (-1/12),q (2/5))
private abbrev negPrimaryS : PiBound × PiBound := (q (-2/5),p (-1/12))

private theorem cover_2_1 : ExactCover.certify ⟨true,false,2,1⟩ 256
    (edgeBox fullW.1 fullW.2 fullS.1 fullS.2)=true := by decide
private theorem cover_2_2 : ExactCover.certify ⟨true,false,2,2⟩ 256
    (edgeBox fullW.1 fullW.2 fullS.1 fullS.2)=true := by decide
private theorem cover_2_4 : ExactCover.certify ⟨true,false,2,4⟩ 256
    (edgeBox fullW.1 fullW.2 posPrimaryS.1 posPrimaryS.2)=true := by decide
private theorem cover_2_5 : ExactCover.certify ⟨true,false,2,5⟩ 256
    (edgeBox fullW.1 fullW.2 negPrimaryS.1 negPrimaryS.2)=true := by decide
private theorem cover_6_1 : ExactCover.certify ⟨true,false,6,1⟩ 256
    (edgeBox negW.1 negW.2 fullS.1 fullS.2)=true := by decide
private theorem cover_6_2 : ExactCover.certify ⟨true,false,6,2⟩ 256
    (edgeBox negW.1 negW.2 fullS.1 fullS.2)=true := by decide
private theorem cover_6_4 : ExactCover.certify ⟨true,false,6,4⟩ 256
    (edgeBox negW.1 negW.2 posPrimaryS.1 posPrimaryS.2)=true := by decide
private theorem cover_6_5 : ExactCover.certify ⟨true,false,6,5⟩ 256
    (edgeBox negW.1 negW.2 negPrimaryS.1 negPrimaryS.2)=true := by decide
private theorem cover_6_6 : ExactCover.certify ⟨true,false,6,6⟩ 256
    (edgeBox negW.1 negW.2 fullS.1 fullS.2)=true := by decide

/-- The complete A2.2 D-edge classification. The hypotheses are exactly the
canonical W-own / S-cardinal bits; all angle and source restrictions are
consequences of `NormalizedPacking`. -/
theorem a22_candidate_diagonal_edges {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=false) :
    DWSelected P 2 ∧ DSSelected P 6 ∧ 1/2<P.diagonalAngle := by
  obtain ⟨i,j,hwd,hds,hi,hj,hdhigh,hown⟩ := diagonal_edges_exist P
  obtain ⟨⟨hwlo,hwup⟩,_,⟨_,hdhi⟩,horder⟩ := baseline_ranges P
  have hsabs := abs_lt.mp (P.cardinal_angle 4 hS)
  have hdfull : (q (1/2)).value≤P.diagonalAngle ∧
      P.diagonalAngle≤(p (1/4)).value := by
    simp [q,p,PiBound.value]
    exact ⟨hdhigh.le,hdhi⟩
  have hwfull : fullW.1.value≤P.helperAngle 2 ∧ P.helperAngle 2≤fullW.2.value := by
    simp [fullW,q,p,PiBound.value]
    exact ⟨hwlo.le,hwup.le⟩
  have hsfull : fullS.1.value≤P.helperAngle 4 ∧ P.helperAngle 4≤fullS.2.value := by
    simp [fullS,q,PiBound.value]
    exact ⟨hsabs.1.le,hsabs.2.le⟩
  have excludeFull (wd ds : Fin 8)
      (hc : ExactCover.certify ⟨true,false,wd,ds⟩ 256
        (edgeBox fullW.1 fullW.2 fullS.1 fullS.2)=true)
      (hwd' : DWSelected P wd) (hds' : DSSelected P ds) : False := by
    exact ExactCover.excludes ⟨true,false,wd,ds⟩ 256
      (edgeBox fullW.1 fullW.2 fullS.1 fullS.2) hc P hW hS hwd' hds'
      (mem_edgeBox hwfull hsfull hdfull) horder.le
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (excludeFull 2 1 cover_2_1 hwd hds)
    · exact False.elim (excludeFull 2 2 cover_2_2 hwd hds)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS.2.value := by
        simp [posPrimaryS,p,q,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsabs.2.le⟩
      exact False.elim (ExactCover.excludes ⟨true,false,2,4⟩ 256
        (edgeBox fullW.1 fullW.2 posPrimaryS.1 posPrimaryS.2) cover_2_4 P hW hS hwd hds
        (mem_edgeBox hwfull hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS.2.value := by
        simp [negPrimaryS,p,q,PiBound.value]
        exact ⟨hsabs.1.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨true,false,2,5⟩ 256
        (edgeBox fullW.1 fullW.2 negPrimaryS.1 negPrimaryS.2) cover_2_5 P hW hS hwd hds
        (mem_edgeBox hwfull hsneg hdfull) horder.le)
    · exact ⟨hwd,hds,hdhigh⟩
  · have hwneg : P.helperAngle 2<0 := by
      by_contra! hn
      have hh := hown hW hn
      norm_num at hh
    have hwn : negW.1.value≤P.helperAngle 2 ∧ P.helperAngle 2≤negW.2.value := by
      simp [negW,q,PiBound.value]
      exact ⟨hwlo.le,hwneg.le⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (ExactCover.excludes ⟨true,false,6,1⟩ 256
        (edgeBox negW.1 negW.2 fullS.1 fullS.2) cover_6_1 P hW hS hwd hds
        (mem_edgeBox hwn hsfull hdfull) horder.le)
    · exact False.elim (ExactCover.excludes ⟨true,false,6,2⟩ 256
        (edgeBox negW.1 negW.2 fullS.1 fullS.2) cover_6_2 P hW hS hwd hds
        (mem_edgeBox hwn hsfull hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hspos : posPrimaryS.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤posPrimaryS.2.value := by
        simp [posPrimaryS,p,q,PiBound.value]
        exact ⟨(hsign.1 rfl).le,hsabs.2.le⟩
      exact False.elim (ExactCover.excludes ⟨true,false,6,4⟩ 256
        (edgeBox negW.1 negW.2 posPrimaryS.1 posPrimaryS.2) cover_6_4 P hW hS hwd hds
        (mem_edgeBox hwn hspos hdfull) horder.le)
    · have hsign := P.DS_primary_sign hds
      have hsneg : negPrimaryS.1.value≤P.helperAngle 4 ∧
          P.helperAngle 4≤negPrimaryS.2.value := by
        simp [negPrimaryS,p,q,PiBound.value]
        exact ⟨hsabs.1.le,(hsign.2 rfl).le⟩
      exact False.elim (ExactCover.excludes ⟨true,false,6,5⟩ 256
        (edgeBox negW.1 negW.2 negPrimaryS.1 negPrimaryS.2) cover_6_5 P hW hS hwd hds
        (mem_edgeBox hwn hsneg hdfull) horder.le)
    · exact False.elim (ExactCover.excludes ⟨true,false,6,6⟩ 256
        (edgeBox negW.1 negW.2 fullS.1 fullS.2) cover_6_6 P hW hS hwd hds
        (mem_edgeBox hwn hsfull hdfull) horder.le)

end SquaresInCircles.Six.Classification
