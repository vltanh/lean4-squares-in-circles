module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEStress

/-!
# The actual single-negative-A / longer-E exclusion

Uncompiled source closure of the longer-E hand proof. The two A-owner
choices and all four E-owner choices are retained. The only inputs are
the original geometric conditions, actual weak contacts, and the local
flat-A entry bounds; the weights and every strict scalar reserve are
constructed in the proof.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Source

theorem original_concentration {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    ∃i j : Fin 4,concentrationScalar k l c (delta C.theta T) (eTotal C de eh) s i j≤0 := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.td_domain hratio
  obtain ⟨i,j,hendpoint⟩ := PositiveTD.Hybrid.concentrate R (diagonal-1/2)
    (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (fun i => (blocks C hg atG de eh k l c i).P)
    (fun i => (blocks C hg atG de eh k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg atG de eh k l c i).P_nonneg)
    (fun i => (blocks C hg atG de eh k l c i).N_nonneg)
    hb.residual_domain hb.positive_bound hb.balance
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by linarith [hk.1]) (show 0≤l by linarith [hk.1,hl.1])
    (show 0<c by linarith [hk.1,hcoef.1]) hb.td_domain hHG hGA hAB hBT hTD hDE hEH
  have hlower := stress_lower atG de eh hs hc hq hHy hGy hBy hDy
    hvar hs0 ha hz he hgain hhg hk hl hcoef hratio
  change TwoPositive.endpoint k l (PositiveTD.tilted c (delta C.theta T))
    (effective C de eh s) i j≤_ at hendpoint
  refine ⟨i,j,?_⟩
  dsimp [concentrationScalar,effective] at ⊢ hendpoint
  linarith

end Source

/-- The unchanged necessary cycle is contradictory when its selected
nonnegative E total is at least the single negative A magnitude. -/
theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (he : s≤PairedE.cycleTotal C de eh) (hz : 0≤delta C.theta T)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have he0 : 0≤PairedE.cycleTotal C de eh := hs.1.trans he
  by_cases hsecondary : atG=true ∧ C.Feasible G 2
  · rcases hsecondary with ⟨rfl,hGA2⟩
    have hHG' : C.Feasible H 0∨C.Feasible H 2 := by
      rcases hhg with rfl|rfl
      · exact Or.inl hHG
      · exact Or.inr hHG
    exact NonnegativeTotals.Source.actual_false false false de eh hsorted hcontained hq
      hHy hGy hBy hDy hvar (by simp [NonnegativeTotals.Source.aTotal,PairedE.total,PairedE.selected])
      hz he0 hHG' hGA2 (by simpa using hAB) hBT hTD hDE hEH
  have hnot : atG=true → ¬C.Feasible G 2 := by
    intro hh hf
    exact hsecondary ⟨hh,hf⟩
  have hgain := Source.gain_lower atG hsorted hcontained hq hGy hBy hflat hAy hs ha hnot hGA hAB
  have hb := Source.budgets hg atG de eh 1 1 1 hvar hs.1 ha hz he
  have hs' : s∈Icc 0 (19/50:ℝ) := by
    refine ⟨hs.1,?_⟩
    cases atG <;> simp only [NegativeAPositiveTD.Explicit.angleCut,if_true,if_false,
      Bool.false_eq_true] at hs <;> linarith [hs.2]
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ := explicit_positive hz he0 hs' he hb.total_upper
  obtain ⟨i,j,hnonpositive⟩ := Source.original_concentration atG de eh hsorted hcontained hq
    hHy hGy hBy hDy hvar hs.1 ha hz he hgain hhg hHG hGA hAB hBT hTD hDE hEH
    hk hl hcoef hratio
  exact (not_le_of_gt (hpositive i j)) hnonpositive

/-- Physical-axis adapter retaining the original local A entry data. -/
theorem frame_flat_false {q s : ℝ} {C : BoundaryCycle q} {hg : Fin 4}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG de eh : Bool) (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : Source.aError (SignedCycle.atFrame F) atG= -s)
    (hflat : ((SignedCycle.atFrame F).point A).a=7/12)
    (hAy : 0≤((SignedCycle.atFrame F).point A).y)
    (he : s≤PairedE.cycleTotal (SignedCycle.atFrame F) de eh)
    (hz : 0≤delta F.theta T) (hhg : hg=0∨hg=2)
    (hHG : (forwardAxis hg).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis (if de then 3 else 2)).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis (if eh then 1 else 0)).Feasible (C.square E) (C.square H)) : False := by
  let S := SignedCycle.atFrame F
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hq
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2∨(if atG then (3:Fin 4) else 2)=3 := by
    cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hGy : (S.point G).y≤0 := ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  apply original atG de eh hn.sorted hn.contained hq.2 hHy.le hGy hBy.le hDy.le
    hv.1.le hs ha hflat hAy he hz hhg
  · exact (SignedCycle.atFrame_feasible F H hg).2 (by simpa [H,G,next] using hHG)
  · exact (SignedCycle.atFrame_feasible F G (if atG then 3 else 2)).2
      (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if atG then 0 else 2)).2
      (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D (if de then 3 else 2)).2
      (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E (if eh then 1 else 0)).2
      (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
