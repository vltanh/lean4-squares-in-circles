module

public import SquaresInCircles.Eight.TableFree.FlatEAngularApplication
public import SquaresInCircles.Eight.TableFree.CoreENegativeExclusion

/-!
# Exclusion of flat E with both primary errors nonpositive

Uncompiled source. All five T stress regimes are connected to their
actual original weak witnesses. No coefficient-domain or angular-stress
conclusion is assumed by these geometric exclusion theorems.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FlatEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks
open FlatEAngularApplication

theorem P_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveSplitComparison.familyPBaseline d+
      min (V (Real.sqrt qCap) (lP d) k d) ((103/100)*d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hv := hh.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hv
  have hm : -PositiveSplitComparison.familyPBaseline d<
      min (V (Real.sqrt qCap) (lP d) k d) ((103/100)*d) :=
    lt_min (by linarith) (by linarith [hh.2.1])
  linarith

theorem N_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hv := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hv
  have hm : -PositiveScalarTransfer.BN d<
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) :=
    lt_min (by linarith) (by linarith [hh.2.2.2.2.1])
  linarith

theorem weights_nonneg {d l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t) :
    0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t := by
  have hk : 0≤k := by norm_num [k]
  exact ⟨hk.trans h.H_lower,hk,by linarith [h.ell_lower],hk.trans h.B_lower,hk.trans h.D_lower⟩

theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hpos : positiveRemoved C 2 0=d := by simp [positiveRemoved,d,positivePart,max_eq_left hG]
  have hinc := nonnegative_T_lower hab (Or.inl rfl) (Or.inl rfl) hde heh hs hvar hd he
    hG (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa [hpos] using hp) (N_lambda hd')
  rw [hpos] at hinc
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.secondary_T hab hde heh (by norm_num [k])
    (by norm_num : (0:ℝ)≤19/50) hs hd' hflat hd he] at hnec
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let x := delta C.theta G
  let z := delta C.theta T
  let d := x+z
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hb := budgets hab (Or.inl rfl) (Or.inr rfl) hde heh 0 0 0 0 0 hvar hd he
  have hpos : positiveRemoved C 2 2=d := by
    simp [positiveRemoved,d,x,z,positivePart,max_eq_left hG,max_eq_left hT]
  have hd' : d∈Icc 0 frameCap := by simpa [hpos] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := PositiveOrdinaryParameters.familyP_td hd' hx hz
  have hinc := nonnegative_T_lower hab (Or.inl rfl) (Or.inr rfl) hde heh hs hvar hd he
    hG (by intro h; norm_num at h) (fun _ => hT)
    (by simpa [hpos] using hp)
    (show (103/100 : ℝ)∈Icc (369/500) (103/100) by norm_num)
  rw [hpos] at hinc
  have hη : 0≤etaP d := by
    have hh := coefficient_bounds hd'
    linarith [hh.2.2.2.2.2.2.1]
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.positive_TD hab hde heh (by norm_num [k]) hη hs
    (show delta C.theta G∈Icc 0 frameCap from ⟨hG,(le_abs_self _).trans (hs G)⟩)
    (show delta C.theta T∈Icc 0 frameCap from ⟨hT,(le_abs_self _).trans (hs T)⟩)
    hflat hd he] at hnec
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd' hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := P_strict hd'
  dsimp [d,x,z] at *
  linarith

theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let x := delta C.theta G
  let z := delta C.theta B
  let d := x+z
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hb := budgets hab (Or.inr rfl) (Or.inl rfl) hde heh 0 0 0 0 0 hvar hd he
  have hpos : positiveRemoved C 3 0=d := by
    simp [positiveRemoved,d,x,z,positivePart,max_eq_left hG,max_eq_left hB]
  have hd' : d∈Icc 0 frameCap := by simpa [hpos] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := PositiveOrdinaryParameters.familyP_bt hd' hx hz
  have hinc := nonnegative_T_lower hab (Or.inr rfl) (Or.inl rfl) hde heh hs hvar hd he
    hG (fun _ => hB) (by intro h; norm_num at h)
    (by simpa [hpos] using hp)
    (show (103/100 : ℝ)∈Icc (369/500) (103/100) by norm_num)
  rw [hpos] at hinc
  have hη : 0≤etaP d := by
    have hh := coefficient_bounds hd'
    linarith [hh.2.2.2.2.2.2.1]
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.positive_BT hab hde heh (by norm_num [k]) hη hs
    (show delta C.theta G∈Icc 0 frameCap from ⟨hG,(le_abs_self _).trans (hs G)⟩)
    (show delta C.theta B∈Icc 0 frameCap from ⟨hB,(le_abs_self _).trans (hs B)⟩)
    hflat hd he] at hnec
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd' hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := P_strict hd'
  dsimp [d,x,z] at *
  linarith

theorem flat_negative_TD_false {C : SignedCycle} {q u : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (3/10))
    (hT : delta C.theta T= -u) (hTflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hc := NegativeOrdinaryParameters.familyTD hd' (Ioc_subset_Icc_self hu)
  have hk : 0≤k := by norm_num [k]
  have hw : 0≤tiltedWeight k (19/50) d ∧ 0≤k ∧ 0≤lN d ∧
      0≤cN d ∧ 0≤cN d/Real.cos u :=
    ⟨hk.trans hp.H_lower,hk,by linarith [hp.ell_lower],hk.trans hc.B_lower,hk.trans hc.D_lower⟩
  have hnec := FlatEStress.necessary_at_cap hq hC hn true hw hf
  rw [FlatEDecomposition.negative_TD hab hde heh hk (by norm_num : (0:ℝ)≤19/50)
    hs hd' hu' hT hTflat hflat hd he] at hnec
  have hinc := negative_TD_lower hab hde heh hs hvar hd he hG hu hT
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q u : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (9/100))
    (hB : delta C.theta B= -u) (hTflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hc := NegativeOrdinaryParameters.familyBT hd' (Ioc_subset_Icc_self hu)
  have hk : 0≤k := by norm_num [k]
  have hw : 0≤tiltedWeight k (19/50) d ∧ 0≤k ∧ 0≤lN d ∧
      0≤cN d/Real.cos u ∧ 0≤cN d :=
    ⟨hk.trans hp.H_lower,hk,by linarith [hp.ell_lower],hk.trans hc.B_lower,hk.trans hc.D_lower⟩
  have hnec := FlatEStress.necessary_at_cap hq hC hn true hw hf
  rw [FlatEDecomposition.negative_BT hab hde heh hk (by norm_num : (0:ℝ)≤19/50)
    hs hd' hu' hB hTflat hflat hd he] at hnec
  have hinc := negative_BT_lower hab hde heh hs hvar hd he hG hu hB
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

end SquaresInCircles.Eight.TableFree.FlatEExclusion
