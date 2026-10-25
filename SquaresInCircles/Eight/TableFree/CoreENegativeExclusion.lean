module

public import SquaresInCircles.Eight.TableFree.CoreENegativeBlocks
public import SquaresInCircles.Eight.TableFree.CoreEPositiveExclusion
public import SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion

/-!
# Core E with nonnegative primary total, including all preprocessed T cases

Uncompiled source draft. A genuine negative T primary is classified at
its original boundary point. An available secondary is reselected at
that same point; otherwise the actual flat-coordinate and short-angle
theorems supply the secant stress. The original E point, both E owners,
and both E frame errors remain unchanged throughout this exclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CoreENegativeExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks
open NegativeSecondaryEExclusion (BT_contact TD_contact)

theorem scalar_positive {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+CoreENegativeEnvelope.lower d := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hL := hh.2.2.2.2.1
  have hE := hh.2.2.2.2.2.1
  have hET := hh.2.2.2.2.2.2
  have hz : -PositiveScalarTransfer.BN d<CoreENegativeEnvelope.zeroLower d :=
    lt_min (by linarith) (by linarith)
  have he : -PositiveScalarTransfer.BN d<CoreENegativeEnvelope.farLower d :=
    lt_min (by linarith) (by linarith)
  have hm := lt_min hz he
  dsimp [CoreENegativeEnvelope.lower]
  linarith

theorem flat_negative_TD_false {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hs : s∈Ioc 0 (3/10)) (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  have hd : delta C.theta G∈Icc 0 frameCap :=
    ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := PositiveOrdinaryParameters.familyN hd
  have hc : 0<cN (delta C.theta G) := by
    have hh := hb.B_lower
    norm_num [k] at hh
    linarith
  have hnec := CoreENegativeStress.negative_TD_necessary (k := k) (l := lN (delta C.theta G))
    (c := cN (delta C.theta G)) (η := 19/50) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hb.ell_lower]) hc (by norm_num : (0:ℝ)≤19/50)
    hG hs' hT hflat hf
  have hinc := CoreENegativeBlocks.TD_lower hC hcore hab hde heh hvar hd
    (Ioc_subset_Icc_self hs) hT he
  have hgain := PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd (show s∈Ioc 0 frameCap from ⟨hs.1,hs'.2⟩)
  have hstrict := scalar_positive hd
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN (delta C.theta G)) (cN (delta C.theta G))
    (19/50) (delta C.theta G)+CoreENegativeEnvelope.lower (delta C.theta G) at hstrict
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hs : s∈Ioc 0 (9/100)) (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  have hd : delta C.theta G∈Icc 0 frameCap :=
    ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := PositiveOrdinaryParameters.familyN hd
  have hc : 0<cN (delta C.theta G) := by
    have hh := hb.B_lower
    norm_num [k] at hh
    linarith
  have hnec := CoreENegativeStress.negative_BT_necessary (k := k) (l := lN (delta C.theta G))
    (c := cN (delta C.theta G)) (η := 19/50) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hb.ell_lower]) hc (by norm_num : (0:ℝ)≤19/50)
    hG hs' hB hflat hf
  have hinc := CoreENegativeBlocks.BT_lower hC hcore hab hde heh hvar hd
    (Ioc_subset_Icc_self hs) hB he
  have hgain := ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd hs
  have hstrict := scalar_positive hd
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN (delta C.theta G)) (cN (delta C.theta G))
    (19/50) (delta C.theta G)+CoreENegativeEnvelope.lower (delta C.theta G) at hstrict
  linarith

theorem reselect_TD {C : SignedCycle} {ab td de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 td de eh i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · have h := hf 0
    change C.Feasible 0 2 at h
    exact h
  · have h := hf 1
    change C.Feasible 1 1 at h
    exact h
  · have h := hf 2
    change C.Feasible 2 ab at h
    exact h
  · have h := hf 3
    change C.Feasible 3 2 at h
    exact h
  · exact hT
  · have h := hf 5
    change C.Feasible 5 de at h
    exact h
  · have h := hf 6
    change C.Feasible 6 eh at h
    exact h

theorem reselect_BT {C : SignedCycle} {ab bt de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt 0 de eh i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · have h := hf 0
    change C.Feasible 0 2 at h
    exact h
  · have h := hf 1
    change C.Feasible 1 1 at h
    exact h
  · have h := hf 2
    change C.Feasible 2 ab at h
    exact h
  · exact hB
  · have h := hf 4
    change C.Feasible 4 0 at h
    exact h
  · have h := hf 5
    change C.Feasible 5 de at h
    exact h
  · have h := hf 6
    change C.Feasible 6 eh at h
    exact h

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let s : ℝ := -delta C.theta T
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
  rcases hent with hsecondary | ⟨hcoreT,hflat,hyT,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh
      hG he (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hn hcore hvar hab hde heh hG he
      ⟨hs.1,hshort.le⟩ hTs hflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh
      hG he (reselect_BT hf hsecondary)
  let s : ℝ := -delta C.theta B
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
  obtain ⟨hcoreT,hflat,hyT,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hn hcore hvar hab hde heh hG he
    ⟨hs.1,hshort.le⟩ hBs hflat hf

/-- The complete preprocessed T owner union at a nonnegative signed
E-primary total. Negative BT uses only the actual TD alignment delivered
by T-pair preprocessing. -/
theorem preprocessed_core_E_false {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh hG he hf
  · by_cases ht : 0≤delta C.theta T
    · exact CoreEPositiveExclusion.positive_TD_false hq hC hn hcore hvar hab hde heh hG ht he hf
    · exact negative_TD_false hq hC hn hcore hvar hab hde heh hG he hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact CoreEPositiveExclusion.positive_BT_false hq hC hn hcore hvar hab hde heh hG hb he hf
    · have hb' : delta C.theta B<0 := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hn hcore hvar hab hde heh hG he hTb hb'
        (halign hb') hf

end SquaresInCircles.Eight.TableFree.CoreENegativeExclusion
