module

public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAStress
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TLargeEData

/-!
# Eight squares: large nonnegative A and negative E at the BT3 alignment

The BT3 state gives the flat-core linear gain (`t_gain_lower`), and its short magnitude follows
from the two T projections. The DE and EH gains are the secant and short tangent gains, and the
scalar bound of the fixed family uses their combined magnitude with the negative T magnitude
(`actual_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE NegativeELargeA

theorem t_gain_lower {C : SignedCycle} (hflat : (C.point T).a=7/12)
    (hy : (C.point T).y≤39/250) (hs : -delta C.theta B∈Icc 0 Paired.M) :
    M*(-delta C.theta B)≤tGain C := by
  have hg := Paired.genuine_linear hflat hy hs
  simp only [neg_neg] at hg
  have hm := mul_le_mul_of_nonneg_left hg (show 0≤c by norm_num [c])
  dsimp [tGain,M,c]
  norm_num [c] at hm
  nlinarith [hs.1]

theorem negative_magnitudes {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta B≤0) (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u) :
    0≤ magnitude C D de ∧ magnitude C E eh∈Icc 0 u ∧ 0≤-delta C.theta B := by
  have hD : 0≤ magnitude C D de := by
    cases hd : de
    · simp [magnitude,NegativeELowA.magnitude,selected]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using neg_nonneg.mpr (hde hd)
  have hE : magnitude C E eh∈Icc 0 u := by
    cases he : eh
    · norm_num [magnitude,NegativeELowA.magnitude,selected,u]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using heh he
  exact ⟨hD,hE,neg_nonneg.mpr ht⟩

/-- Simultaneous negative E primaries are allowed. All scalar quantities come from the weak
separating inequalities of the cycle. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc L frameCap) (ht : delta C.theta B≤0)
    (htd : delta C.theta T=0) (hTflat : (C.point T).a=7/12) (hTy : (C.point T).y≤39/250)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have ha0 : 0≤aTotal C ga ab := by dsimp [L] at ha; linarith [ha.1]
  have hEsgn : eh=true→delta C.theta E≤0 := fun he => by linarith [(heh he).1.1]
  have hb := budgets hg ga ab de eh hvar ha0 ht htd hde hEsgn
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hweights (i : Vertex) : 0≤weights C de i := by
    cases de <;> fin_cases i <;> simp [weights,NegativeELargeA.k,NegativeELargeA.l,c]
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
    actual_blocks_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha0 ht htd hde hEsgn i)
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hb.1
  have hAmul := mul_le_mul_of_nonneg_left hA (show 0≤NegativeELargeA.l by norm_num [NegativeELargeA.l])
  have hDEgain := NegativeELargeA.Source.de_gain_lower de (hs D) (hc D) hq hDy (hsmall D) hde
  have hEHgain := NegativeELargeA.Source.eh_gain_lower eh hflat heh
  have hBt : -delta C.theta B∈Icc 0 frameCap := ⟨neg_nonneg.mpr ht,(neg_le_abs _).trans (hsmall B)⟩
  have hshort := Paired.aligned_short hs hcoreT hc hq hDy hBt hBT hTD (by simp) htd
  have hTgain := t_gain_lower hTflat hTy ⟨hBt.1,hshort.le⟩
  have hmags := negative_magnitudes de eh ht hde (fun he => (heh he).1)
  have hcombined := combined_gain_lower (s:=magnitude C E eh)
    (r:=magnitude C D de-delta C.theta B) hmags.2.1 (by linarith [hmags.1,hmags.2.2])
    (by dsimp [negativeTotal] at hb; linarith [hb.2.1.2])
  have hsumangle : magnitude C E eh+(magnitude C D de-delta C.theta B)=negativeTotal C de eh := by
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
  rw [decomposition C hg ga ab de eh hflat htd (hcos D).ne'] at hupper
  change NegativeELargeA.l*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAmul
  linarith


end SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
