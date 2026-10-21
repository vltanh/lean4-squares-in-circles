module

public import SquaresInCircles.Eight.TableFree.CoreEOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.PositiveSecondaryEExclusion

/-!
# Positive GA with core E and nonnegative signed E-primary total

Uncompiled source draft. The three nonnegative-T owner regimes are
excluded directly from the original weak witnesses. Either normal owner
is permitted on both E edges, with no sign assumption on either
individual E angle. The only E-angle assumption is that the sum of the
retained primary errors is nonnegative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CoreEPositiveExclusion
open Candidate PositiveStressCoefficients SecondaryEStress PositivePrimaryBaselines
open PositiveOrdinaryParameters ActualOrdinaryBlocks ActualCoreEBlocks

theorem P_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveSplitComparison.familyPBaseline d+
      CoreEOrdinaryEnvelope.lower d (lP d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hE := hh.2.2.1
  have hmin := lt_min (by linarith : -PositiveSplitComparison.familyPBaseline d<
      OrdinaryAngleConcavity.V (Real.sqrt qCap) (lP d) k d)
    (by linarith : -PositiveSplitComparison.familyPBaseline d<
      PositiveScalarTransfer.J (frameCap-d)+lP d-87/1250)
  dsimp [CoreEOrdinaryEnvelope.lower]
  linarith

theorem N_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+CoreEOrdinaryEnvelope.lower d (lN d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hE := hh.2.2.2.2.2.1
  have hmin := lt_min (by linarith : -PositiveScalarTransfer.BN d<
      OrdinaryAngleConcavity.V (Real.sqrt qCap) (lN d) k d)
    (by linarith : -PositiveScalarTransfer.BN d<
      PositiveScalarTransfer.J (frameCap-d)+lN d-87/1250)
  dsimp [CoreEOrdinaryEnvelope.lower]
  linarith

theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core) (hy : (C.point E).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i)) : False := by
  let d : ℝ := delta C.theta G
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inl rfl)
    hde heh 0 0 0 0 0 hvar hG
    (by intro h; norm_num at h) (by intro h; norm_num at h) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d] using hb.1
  have hp := familyN hd
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hy hab (Or.inl rfl)
    (Or.inl rfl) hde heh hvar hG (by intro h; norm_num at h)
    (by intro h; norm_num at h) he
    (by simpa [removed,d] using hp) (CoreEOrdinaryEnvelope.coefficient_intervals hd).2
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.secondary_necessary hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.2.2.1])
    (by have hh := hc.2.2.2.2.1; norm_num [k] at hh; linarith)
    (by norm_num : (0:ℝ)≤19/50) hG hf
  have hstrict := N_strict hd
  have heq : PositiveScalarTransfer.BN d=
      secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d := rfl
  rw [heq] at hstrict
  simp only [removed,show (2:Fin 4)≠3 by decide,show (0:Fin 4)≠2 by decide,
    if_false,add_zero] at hinc
  dsimp [d] at hinc hstrict
  linarith

theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core) (hy : (C.point E).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta T
  let d : ℝ := x+z
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inr rfl)
    hde heh 0 0 0 0 0 hvar hG (by intro h; norm_num at h) (by intro _; exact hT) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_td hd hx hz
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hy hab (Or.inl rfl)
    (Or.inr rfl) hde heh hvar hG (by intro h; norm_num at h)
    (by intro _; exact hT) he (by simpa [removed,d,x,z] using hp)
    (CoreEOrdinaryEnvelope.coefficient_intervals hd).1
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.td_necessary hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.1])
    (by linarith [hc.2.2.2.2.2.2.1]) hG hT hf
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := P_strict hd
  have hdEq : removed C 2 2=d := by simp [removed,d,x,z]
  rw [hdEq] at hinc
  linarith

theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core) (hy : (C.point E).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta B
  let d : ℝ := x+z
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inr rfl) (Or.inl rfl)
    hde heh 0 0 0 0 0 hvar hG (by intro _; exact hB) (by intro h; norm_num at h) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_bt hd hx hz
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hy hab (Or.inr rfl)
    (Or.inl rfl) hde heh hvar hG (by intro _; exact hB)
    (by intro h; norm_num at h) he (by simpa [removed,d,x,z] using hp)
    (CoreEOrdinaryEnvelope.coefficient_intervals hd).1
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.bt_necessary hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.1])
    (by linarith [hc.2.2.2.2.2.2.1]) hG hB hf
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := P_strict hd
  have hdEq : removed C 3 0=d := by simp [removed,d,x,z]
  rw [hdEq] at hinc
  linarith

theorem nonnegative_T_false {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core) (hy : (C.point E).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2 ∧ 0≤delta C.theta T) ∨
      (bt=3 ∧ td=0 ∧ 0≤delta C.theta B))
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl,hT⟩ | ⟨rfl,rfl,hB⟩
  · exact secondary_T_false hq hC hn hcore hy hvar hab hde heh hG he hf
  · exact positive_TD_false hq hC hn hcore hy hvar hab hde heh hG hT he hf
  · exact positive_BT_false hq hC hn hcore hy hvar hab hde heh hG hB he hf

end SquaresInCircles.Eight.TableFree.CoreEPositiveExclusion
