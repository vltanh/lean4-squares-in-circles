module

public import SquaresInCircles.Eight.Words.Core.ENegativeExclusion
public import SquaresInCircles.Eight.Owners.Flat.EExclusion

/-!
# Eight squares: the T entry when E is on the flat core

When E is on the flat side of the core with nonpositive DE and EH primaries, every preprocessed
row of T is impossible (`preprocessed_flat_E_false`): a secondary owner of T is selected again
from a weak projection of the cycle, and a negative primary gives its flat T and short angle
(`negative_TD_false`, `negative_BT_aligned_false`). The witnesses and coordinates of E stay fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FlatEPreprocess
open Candidate ActualCoreEBlocks FlatEExclusion
open NegativeSecondaryEExclusion (BT_contact TD_contact)
open CoreENegativeExclusion (reselect_TD reselect_BT)

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hTs : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hTs]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hent := NegativeTEntry.negative_TD_entry (hC.sorted B) (hC.sorted T) (hC.sorted D)
    (hC.contained B) hTb (hC.contained D) (hC.core T) (hC.core D)
    hq hn.D_nonpos hs hBT hTD
  rcases hent with hsecondary | ⟨hcoreT,hTflat,hyT,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hn hflat hd he hvar hab hde heh hG
      ⟨hs.1,hshort.le⟩ hTs hTflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG (reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hBs : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hBs]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hBs] using hh))
  obtain ⟨hcoreT,hTflat,hyT,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hn hflat hd he hvar hab hde heh hG
    ⟨hs.1,hshort.le⟩ hBs hTflat hf

theorem preprocessed_flat_E_false {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG hf
  · by_cases ht : 0≤delta C.theta T
    · exact positive_TD_false hq hC hn hflat hd he hvar hab hde heh hG ht hf
    · exact negative_TD_false hq hC hn hflat hd he hvar hab hde heh hG hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact positive_BT_false hq hC hn hflat hd he hvar hab hde heh hG hb hf
    · have hb' := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hn hflat hd he hvar hab hde heh hG hTb hb'
        (halign hb') hf

end SquaresInCircles.Eight.FlatEPreprocess
