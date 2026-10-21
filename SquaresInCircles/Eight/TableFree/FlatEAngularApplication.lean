module

public import SquaresInCircles.Eight.TableFree.FlatEDecomposition

/-!
# Applying the joint envelope to the original flat-E stress

Uncompiled source. The coefficient maps are instantiated here, and the
removed masses are evaluated in each actual T regime. Every secant gain
is the proved analytic gain of the same weighted anchor norm.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatEAngularApplication
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks
open FlatTStress GlobalGA PositiveOrdinaryEnvelope

theorem secant_lower {a e : ℝ} (ha : k≤a) (he : e∈Icc 0 frameCap) :
    (103/100)*e≤secantCharge (Real.sqrt qCap) 1 a e := by
  rw [secantCharge_eq (by norm_num : (0:ℝ)<1) he]
  simp only [div_one,one_mul]
  by_cases hz : e=0
  · simp [hz,secantGain_zero]
  · exact (PositiveSecantGain.strict_gain (q := qCap) (by norm_num [qCap]) le_rfl
      ha ⟨lt_of_le_of_ne he.1 (Ne.symm hz),he.2⟩).le

theorem pair_gain {n t a e λ : ℝ} (hn : k≤n) (ht : k≤t)
    (ha : a∈Icc 0 frameCap) (he : e∈Icc 0 frameCap) (hλ : λ≤103/100) :
    λ*(a+e)≤secantCharge (Real.sqrt qCap) 1 n e+
      secantCharge (Real.sqrt qCap) 1 t a := by
  have h1 := secant_lower hn he
  have h2 := secant_lower ht ha
  have hm := mul_le_mul_of_nonneg_right hλ (add_nonneg ha.1 he.1)
  linarith

theorem N_lambda {d : ℝ} (hd : d∈Icc 0 frameCap) :
    369/500≤lambdaN d ∧ lambdaN d≤103/100 := by
  refine ⟨?_,(ShortSecantGain.negative_family_slopes hd).1⟩
  dsimp [lambdaN]
  linarith [hd.1]

theorem positive_coefficients {d l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t)
    (C : SignedCycle) (ab bt td de eh : Fin 4) (i : Fin 4) :
    (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=ps n l t i ∧
    (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=qs b t i := by
  have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh n k l b t i
  have h2 := PositiveOrdinaryEnvelope.block_coefficients h C ab bt td i
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

theorem negative_coefficients {d u b t : ℝ}
    (h : NegativeOrdinaryParameters.Bounds d u b t)
    (C : SignedCycle) (ab bt td de eh : Fin 4) (i : Fin 4) :
    (ActualCoreEBlocks.blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t i).p=
      ps (tiltedWeight k (19/50) d) (lN d) t i ∧
    (ActualCoreEBlocks.blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t i).q=
      qs b t i := by
  have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh
    (tiltedWeight k (19/50) d) k (lN d) b t i
  have h2 := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

theorem nonnegative_removed {C : SignedCycle} {bt td de eh : Fin 4}
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T) :
    negativeRemoved C bt td de eh=deAngle C de+ehAngle C eh := by
  have hB : (if bt=3 then negativePart (delta C.theta B) else 0)=0 := by
    by_cases hb : bt=3
    · simp [hb,negativePart,max_eq_right (neg_nonpos.mpr (hBT hb))]
    · simp [hb]
  have hT : (if td=2 then negativePart (delta C.theta T) else 0)=0 := by
    by_cases ht : td=2
    · simp [ht,negativePart,max_eq_right (neg_nonpos.mpr (hTD ht))]
    · simp [ht]
  simp [negativeRemoved,hB,hT,negativePart,max_eq_right (neg_nonpos.mpr hG)]

theorem nonnegative_T_lower {C : SignedCycle} {ab bt td de eh : Fin 4}
    {n l b t λ : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T)
    (hcoeff : PositiveOrdinaryParameters.Bounds (positiveRemoved C bt td) l n b t)
    (hλ : λ∈Icc (369/500) (103/100)) :
    min (V (Real.sqrt qCap) l k (positiveRemoved C bt td)) (λ*positiveRemoved C bt td)≤
      secantCharge (Real.sqrt qCap) 1 n (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 t (deAngle C de)+
      FlatEStress.increment C ab bt td de eh n k l b t (Real.sqrt qCap) := by
  have hb := budgets hab hbt htd hde heh n k l b t hvar hd he
  have hdom := FlatPrimaryParameters.positive hcoeff hb.2.1
  have hinc := actual_lower hab hbt htd hde heh hsmall hvar hd he
    ⟨hcoeff.H_lower,by linarith [hcoeff.H_upper]⟩
    ⟨hcoeff.D_lower,fun _ => hcoeff.D_upper⟩ hdom
    (positive_coefficients hcoeff C ab bt td de eh) hλ.1
  have hr := removed_nonneg (bt := bt) (td := td) hd he
  have hgain := pair_gain hcoeff.H_lower hcoeff.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hb.2.1.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hb.2.1.2⟩) hλ.2
  rw [nonnegative_removed hG hBT hTD] at hinc
  change _≤_+_+∑ i,_
  linarith

theorem negative_TD_lower {C : SignedCycle} {ab de eh : Fin 4} {u : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (3/10)) (hT : delta C.theta T= -u) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤
      secantCharge (Real.sqrt qCap) (cN (delta C.theta G)) 1 u+
      secantCharge (Real.sqrt qCap) 1 (tiltedWeight k (19/50) (delta C.theta G)) (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 (cN (delta C.theta G)/Real.cos u) (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k (19/50) (delta C.theta G)) k
        (lN (delta C.theta G)) (cN (delta C.theta G)) (cN (delta C.theta G)/Real.cos u)
        (Real.sqrt qCap) := by
  let d := delta C.theta G
  let s := negativeRemoved C 2 2 de eh
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hpos : positiveRemoved C 2 2=d := by
    simp [positiveRemoved,d,hT,positivePart,max_eq_left hG,max_eq_right (neg_nonpos.mpr hu.1.le)]
  have hneg : s=u+deAngle C de+ehAngle C eh := by
    simp [s,negativeRemoved,hT,negativePart,max_eq_right (neg_nonpos.mpr hG),max_eq_left hu.1.le]
  have hb := budgets hab (Or.inl rfl) (Or.inr rfl) hde heh
    (tiltedWeight k (19/50) d) k (lN d) (cN d) (cN d/Real.cos u) hvar hd he
  have hs : s∈Icc 0 frameCap := hb.2.1
  have hr := removed_nonneg (bt := 2) (td := 2) hd he
  have hus : u≤s := by rw [hneg]; linarith [hr.2.2.1.1,hr.2.2.2.1]
  have hc := NegativeOrdinaryParameters.familyTD hd' (Ioc_subset_Icc_self hu)
  have hdom := FlatPrimaryParameters.negativeTD hd' (Ioc_subset_Icc_self hu) hs hus
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hn : k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤2069/2000 :=
    ⟨hp.H_lower,by linarith [hp.H_upper]⟩
  have hinc := actual_lower hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hvar hd he hn
    ⟨hc.D_lower,by intro h; norm_num at h⟩
    (by simpa [hpos,s] using hdom)
    (negative_coefficients hc C ab 2 2 de eh) (N_lambda hd').1
  rw [hpos] at hinc
  have hegain := pair_gain hp.H_lower hc.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hs.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hs.2⟩) (N_lambda hd').2
  have hc0 : 0<cN d := (by norm_num [k] : (0:ℝ)<k).trans_le hp.B_lower
  have htGain := (PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd' ⟨hu.1,hu'.2⟩).le
  rw [← secantCharge_eq hc0 hu' 1] at htGain
  change _≤_+_+_+∑ i,_
  dsimp [d] at *
  rw [hneg] at hinc
  linarith

theorem negative_BT_lower {C : SignedCycle} {ab de eh : Fin 4} {u : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (9/100)) (hB : delta C.theta B= -u) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤
      secantCharge (Real.sqrt qCap) (cN (delta C.theta G)) (lN (delta C.theta G)) u+
      secantCharge (Real.sqrt qCap) 1 (tiltedWeight k (19/50) (delta C.theta G)) (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 (cN (delta C.theta G)) (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k (19/50) (delta C.theta G)) k
        (lN (delta C.theta G)) (cN (delta C.theta G)/Real.cos u) (cN (delta C.theta G))
        (Real.sqrt qCap) := by
  let d := delta C.theta G
  let s := negativeRemoved C 3 0 de eh
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hpos : positiveRemoved C 3 0=d := by
    simp [positiveRemoved,d,hB,positivePart,max_eq_left hG,max_eq_right (neg_nonpos.mpr hu.1.le)]
  have hneg : s=u+deAngle C de+ehAngle C eh := by
    simp [s,negativeRemoved,hB,negativePart,max_eq_right (neg_nonpos.mpr hG),max_eq_left hu.1.le]
  have hb := budgets hab (Or.inr rfl) (Or.inl rfl) hde heh
    (tiltedWeight k (19/50) d) k (lN d) (cN d/Real.cos u) (cN d) hvar hd he
  have hs : s∈Icc 0 frameCap := hb.2.1
  have hr := removed_nonneg (bt := 3) (td := 0) hd he
  have hus : u≤s := by rw [hneg]; linarith [hr.2.2.1.1,hr.2.2.2.1]
  have hc := NegativeOrdinaryParameters.familyBT hd' (Ioc_subset_Icc_self hu)
  have hdom := FlatPrimaryParameters.negativeBT hd' (Ioc_subset_Icc_self hu) hs hus
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hn : k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤2069/2000 :=
    ⟨hp.H_lower,by linarith [hp.H_upper]⟩
  have hinc := actual_lower hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hvar hd he hn
    ⟨hp.D_lower,fun _ => hp.D_upper⟩
    (by simpa [hpos,s] using hdom)
    (negative_coefficients hc C ab 3 0 de eh) (N_lambda hd').1
  rw [hpos] at hinc
  have hegain := pair_gain hp.H_lower hp.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hs.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hs.2⟩) (N_lambda hd').2
  have hc0 : 0<cN d := (by norm_num [k] : (0:ℝ)<k).trans_le hp.B_lower
  have htGain := (ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd' hu).le
  rw [← secantCharge_eq hc0 hu' (lN d)] at htGain
  change _≤_+_+_+∑ i,_
  dsimp [d] at *
  rw [hneg] at hinc
  linarith

end SquaresInCircles.Eight.TableFree.FlatEAngularApplication
