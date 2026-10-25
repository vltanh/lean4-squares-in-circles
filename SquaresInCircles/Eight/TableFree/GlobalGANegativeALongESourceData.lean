module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEScalar
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsSource

/-!
# Original signed budgets after deleting one negative A primary

Uncompiled transcription of equations (3) and (20). The original
seven angles and points are unchanged. Deletion only constructs the
four analytic ordinary blocks; no virtual argument is called a witness.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError
abbrev eTotal := PairedE.cycleTotal
def effective (C : SignedCycle) (de eh : Bool) (s : ℝ) : ℝ :=
  delta C.theta T+eTotal C de eh-s
def blocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → Block :=
  NonnegativeTotals.Source.blocks C hg atG (!atG) de eh k l c
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → ℝ :=
  NonnegativeTotals.Source.actualBlocks C hg atG (!atG) de eh k l c
def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : ℝ :=
  NonnegativeTotals.Source.actualStress C hg atG (!atG) de eh k l c
def eParts (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ) : ℝ :=
  f (PairedE.selected de (delta C.theta D))+f (PairedE.selected eh (delta C.theta E))

theorem eParts_nonnegative (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ)
    (hf : ∀u,0≤f u) : 0≤eParts C de eh f := by
  exact add_nonneg (hf _) (hf _)

theorem eParts_signed (C : SignedCycle) (de eh : Bool) :
    eParts C de eh positivePart-eParts C de eh negativePart=eTotal C de eh := by
  have hD := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hE := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  dsimp [eParts,eTotal,PairedE.cycleTotal,PairedE.total]
  linarith

theorem selected_parts {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    NonnegativeTotals.Source.selectedSum C atG (!atG) de eh f=f (-s)+eParts C de eh f := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha <;>
    simp [NonnegativeTotals.Source.selectedSum,PairedE.selected,eParts,ha,hf] <;> ring

theorem block_parts {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l c : ℝ) (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG de eh k l c i).u+f (blocks C hg atG de eh k l c i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-f (-s)-eParts C de eh f := by
  have hh := NonnegativeTotals.Source.sum_parts C hg atG (!atG) de eh k l c f hf
  rw [selected_parts atG de eh ha f hf] at hh
  dsimp [blocks]
  linarith

structure Budget (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c s : ℝ) : Prop where
  td_domain : delta C.theta T∈Icc 0 frameCap
  e_domain : eTotal C de eh∈Icc 0 frameCap
  total_upper : delta C.theta T+eTotal C de eh≤frameCap
  residual_domain : effective C de eh s∈Icc 0 frameCap
  positive_original : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta T-eTotal C de eh
  positive_bound : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-effective C de eh s
  negative_original : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s
  negative_bound : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap
  balance : (∑i,(blocks C hg atG de eh k l c i).N)=
    effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P

theorem budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh) :
    Budget C hg atG de eh k l c s := by
  have hp := block_parts hg atG de eh k l c ha positivePart positivePart_zero
  have hn := block_parts hg atG de eh k l c ha negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hps : positivePart (-s)=0 := max_eq_right (by linarith)
  have hns : negativePart (-s)=s := by simp [negativePart,hs]
  have hP : (∑i,(blocks C hg atG de eh k l c i).P)=
      positiveVariation C.theta-delta C.theta T-eParts C de eh positivePart := by
    simpa only [Block.P,hpz,hps,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg atG de eh k l c i).N)=
      negativeVariation C.theta-s-eParts C de eh negativePart := by
    simpa only [Block.N,hnz,hns,sub_zero,negativeVariation] using hn
  have heq := eParts_signed C de eh
  have hEneg := eParts_nonnegative C de eh negativePart negativePart_nonneg
  have hP0 : 0≤∑i,(blocks C hg atG de eh k l c i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).P_nonneg)
  have hN0 : 0≤∑i,(blocks C hg atG de eh k l c i).N :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).N_nonneg)
  have hPcap : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta T-eTotal C de eh := by
    linarith
  have hNcap : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s := by
    linarith [variations_equal C.theta]
  have hbalance : (∑i,(blocks C hg atG de eh k l c i).N)=
      effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P := by
    dsimp [effective]
    linarith [variations_equal C.theta]
  have htotal : delta C.theta T+eTotal C de eh≤frameCap := by linarith
  refine ⟨⟨hz,by linarith⟩,⟨by linarith,by linarith⟩,htotal,
    ?_,hPcap,?_,hNcap,by linarith,hbalance⟩
  · dsimp [effective]; constructor <;> linarith
  · dsimp [effective]; linarith

theorem block_budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh) (i : Fin 4) :
    (blocks C hg atG de eh k l c i).P≤frameCap ∧ (blocks C hg atG de eh k l c i).N≤frameCap := by
  have hb := budgets hg atG de eh k l c hvar hs ha hz he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.residual_domain.1],hN.trans hb.negative_bound⟩

theorem actual_gain_identity {C : SignedCycle} {s : ℝ} (atG : Bool)
    (ha : aError C atG= -s) (hflat : (C.point A).a=7/12) (hs : s∈Icc 0 frameCap) :
    PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)=
      ShortE.gain (if atG then (C.point A).y+1/2 else 1/2-(C.point A).y) s := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,if_false,if_true] at ha <;>
    simp [PairedE.primaryGain,ha,Real.sin_neg,Real.cos_neg,edgeWidth_negative_formula hs,
      hflat,ShortE.gain] <;> ring

theorem gain_lower {q s : ℝ} {C : SignedCycle} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hGy : (C.point G).y≤0) (hBy : (C.point B).y≤0)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : aError C atG= -s) (hnot : atG=true → ¬C.Feasible G 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) :
    gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A) := by
  have hsframe := (NegativeAPositiveTD.Explicit.angle_domain atG hs).2
  rw [actual_gain_identity atG ha hflat hsframe]
  by_cases hzero : s=0
  · subst s; simp [gain,ShortE.gain]
  have hpos : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
  cases atG
  · have hAB' : zeroFeasible (C.point A) (C.point B) (-s) 2 := by
      change delta C.theta A= -s at ha
      have h : 0≤zeroProjection (C.point A) (C.point B) (delta C.theta A) 2-
          edgeWidth (delta C.theta A) := hAB
      rw [ha] at h
      exact sub_nonneg.mp h
    have hb := ShortE.AB_tangent_lower (hsorted B) (hcontained B) hq hBy hAy hflat hsframe hAB'
    exact gain_le_AB hb.le (by simpa [NegativeAPositiveTD.Explicit.angleCut] using hs.2)
  · have hga : quarterFeasible (C.point G) (C.point A) (-s) 3 := by
      change delta C.theta G= -s at ha
      have h : 0≤quarterProjection (C.point G) (C.point A) (delta C.theta G) 3-
          edgeWidth (delta C.theta G) := hGA
      rw [ha] at h
      exact sub_nonneg.mp h
    have hga2 : ¬quarterFeasible (C.point G) (C.point A) (-s) 2 := by
      intro hh
      apply hnot rfl
      change delta C.theta G= -s at ha
      show 0≤quarterProjection (C.point G) (C.point A) (delta C.theta G) 2-
          edgeWidth (delta C.theta G)
      rw [ha]
      exact sub_nonneg.mpr hh
    have hcut := GA_sharp_cut (hsorted G) (hcontained G) (hsorted A) hq hGy hAy hflat
      ⟨hpos,by simpa [NegativeAPositiveTD.Explicit.angleCut] using hs.2⟩ hga hga2
    exact gain_le_GA hcut.1.le

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Source
