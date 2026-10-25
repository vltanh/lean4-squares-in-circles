module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeASourceData

/-!
# The original large-A negative-E/nonpositive-TD2 contradiction

Uncompiled final source application of the fixed-family hand proof. The
actual D circle supplies the M secant correction, the genuine EH entry
supplies its small tangent, and the actual signed T state supplies the
TD secant gain. Each term is compared before the original inequalities
are summed. No support or gain reserve is assumed by the source theorem.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE

theorem de_gain_lower {Q : ℝ} {C : SignedCycle} (de : Bool)
    (hs : (C.point D).Sorted) (hc : (C.point D).Contained Q)
    (hq : Q≤qCap) (hy : (C.point D).y≤0)
    (hsmall : |delta C.theta D|≤frameCap) (hde : de=true→delta C.theta D≤0) :
    M*magnitude C D de≤deGain C de := by
  cases hd : de
  · simp [magnitude,NegativeELowA.magnitude,selected,deGain]
  · have hn : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans hsmall⟩
    have hcos := NegativeESecant.cos_pos hn
    have hh := actual_correction_lower (D:=(C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hy)
      (by simpa using hc) hq hn
    have hwidth := edgeWidth_negative_formula hn
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have he : deGain C true=(secant (-delta C.theta D)-1)/2+K*Real.tan (-delta C.theta D)-
        (secant (-delta C.theta D)*(C.point D).a+c*(-(C.point D).y)-clippedSupport 1 c) := by
      dsimp [deGain,secant,K]
      simp only [if_true,Real.cos_neg,Real.sin_neg,Real.tan_eq_sin_div_cos]
      rw [hwidth]
      simp only [Real.cos_neg] at hcos
      field_simp [hcos.ne']
      ring
    simpa [magnitude,NegativeELowA.magnitude,selected,he,SignedPoint.reflect] using hh

theorem eh_gain_lower {C : SignedCycle} (eh : Bool)
    (hflat : (C.point E).a=7/12)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) :
    g (magnitude C E eh)≤ehGain C eh := by
  cases he : eh
  · simp [magnitude,NegativeELowA.magnitude,selected,ehGain]
  · obtain ⟨hs,hEy⟩ := heh he
    have hsf : -delta C.theta E∈Icc 0 frameCap :=
      ⟨hs.1,hs.2.trans (by norm_num [u,frameCap])⟩
    have hwidth := edgeWidth_negative_formula hsf
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have hcos : 0≤1-Real.cos (delta C.theta E) := sub_nonneg.mpr (Real.cos_le_one _)
    have hres := mul_le_mul_of_nonneg_right
      (show 1/2-(C.point E).y≤beta by dsimp [beta]; linarith) hcos
    dsimp [magnitude,NegativeELowA.magnitude,selected,ehGain,g,K,beta]
    simp only [if_true,Real.cos_neg,Real.sin_neg,hflat,hwidth]
    dsimp [beta] at hres
    nlinarith

theorem t_gain_lower {Q : ℝ} {C : SignedCycle}
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcore : (C.point T).AvoidsCore) (hq : Q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (ht : delta C.theta T≤0) :
    M*(-delta C.theta T)≤tGain C := by
  have hz : -delta C.theta T∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr ht,(neg_le_abs _).trans hsmall⟩
  have hg := PositiveANegativeTD.actual_gain_lower (hs T) hcore (hc T)
    (hs D) hDy (hc D) hq (show 0≤c by norm_num [c]) hz
  have hw := edgeWidth_negative_formula hz
  simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hw
  have he : tGain C=PositiveANegativeTD.gain c (-delta C.theta T)
      (C.point T).a (-(C.point D).y) := by
    dsimp [tGain,PositiveANegativeTD.gain]
    simp only [Real.cos_neg,Real.sin_neg]
    rw [hw]
    ring
  rw [he]
  dsimp [M,c] at *
  nlinarith [hz.1]

theorem negative_magnitudes {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta T≤0) (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u) :
    0≤ magnitude C D de ∧ magnitude C E eh∈Icc 0 u ∧ 0≤-delta C.theta T := by
  have hD : 0≤ magnitude C D de := by
    cases hd : de
    · simp [magnitude,NegativeELowA.magnitude,selected]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using neg_nonneg.mpr (hde hd)
  have hE : magnitude C E eh∈Icc 0 u := by
    cases he : eh
    · norm_num [magnitude,NegativeELowA.magnitude,selected,u]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using heh he
  exact ⟨hD,hE,neg_nonneg.mpr ht⟩

/-- Simultaneous negative E primaries are allowed. All scalar quantities
are extracted from the actual original weak separating inequalities. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc L frameCap) (ht : delta C.theta T≤0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have ha0 : 0≤aTotal C ga ab := by dsimp [L] at ha; linarith [ha.1]
  have hEsgn : eh=true→delta C.theta E≤0 := fun he => by linarith [(heh he).1.1]
  have hb := budgets hg ga ab de eh hvar ha0 ht hde hEsgn
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hweights (i : Vertex) : 0≤weights C de i := by
    cases de <;> fin_cases i <;> simp [weights,k,l,c]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hupper : stress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have h := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at h
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hblocks := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha0 ht hde hEsgn i)
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hb.1
  have hAmul := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l])
  have hDEgain := de_gain_lower de (hs D) (hc D) hq hDy (hsmall D) hde
  have hEHgain := eh_gain_lower eh hflat heh
  have hTgain := t_gain_lower hs hc hcoreT hq hDy (hsmall T) ht
  have hmags := negative_magnitudes de eh ht hde (fun he => (heh he).1)
  have hcombined := combined_gain_lower (s:=magnitude C E eh)
    (r:=magnitude C D de-delta C.theta T) hmags.2.1 (by linarith [hmags.1,hmags.2.2])
    (by dsimp [negativeTotal] at hb; linarith [hb.2.1.2])
  have hsumangle : magnitude C E eh+(magnitude C D de-delta C.theta T)=negativeTotal C de eh := by
    dsimp [negativeTotal]
    ring
  rw [hsumangle] at hcombined
  have hgain : min (M*negativeTotal C de eh) (jointGain (negativeTotal C de eh))≤
      deGain C de+ehGain C eh+tGain C := by linarith
  have hscalar := sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh i).P) (fun i => (blocks C hg ga ab de eh i).N)
    ha hb.2.1 (fun i => (blocks C hg ga ab de eh i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh i).N_nonneg)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hgain
  rw [decomposition C hg ga ab de eh hflat (hcos T).ne' (hcos D).ne'] at hupper
  change l*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAmul
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA.Source
