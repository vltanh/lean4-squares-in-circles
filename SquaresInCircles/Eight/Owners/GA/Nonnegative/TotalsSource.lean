module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsScalar
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsStress

/-!
# Eight squares: nonnegative A/E totals with the original nonnegative TD2 error

Every scalar and every coefficient domain is supplied by a constructed
continuous family. The final theorem has only original geometric
hypotheses, weak owner witnesses, and the three stated signed totals.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem original_concentration {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hhg : hg=0∨hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    ∃i j : Fin 4,NonnegativeTotals.scalar k l c
      (aTotal C ga ab) (delta C.theta T) (eTotal C de eh) i j≤0 := by
  have hb := budgets hg ga ab de eh k l c hvar ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.2.2.1 hratio
  obtain ⟨i,j,hendpoint⟩ := PositiveTD.Hybrid.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (fun i => (blocks C hg ga ab de eh k l c i).P)
    (fun i => (blocks C hg ga ab de eh k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg ga ab de eh k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh k l c i).N_nonneg)
    hb.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hupper := stress_nonpositive ga ab de eh
    (show 0≤k by linarith [hk.1]) (show 0≤l by linarith [hk.1,hl.1])
    (show 0<c by linarith [hk.1,hcoef.1]) hb.2.2.1 hHG hGA hAB hBT hTD hDE hEH
  have hlower := stress_lower ga ab de eh hs hc hq hHy hGy hBy hDy
    hvar ha hz he hhg hk hl hcoef hratio
  change TwoPositive.endpoint k l (PositiveTD.tilted c (delta C.theta T))
    (total C ga ab de eh) i j≤_ at hendpoint
  refine ⟨i,j,?_⟩
  dsimp [NonnegativeTotals.scalar,total] at ⊢ hendpoint
  linarith

/-- All sixteen choices of A and E primary flags, with no sign
restriction on either constituent of the two nonnegative totals. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hb := budgets 0 ga ab de eh 1 1 1 hvar ha hz he
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ :=
    NonnegativeTotals.explicit_positive ha hz he hb.1.2
  have finish (hg : Fin 4) (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg) : False := by
    obtain ⟨i,j,hh⟩ := original_concentration ga ab de eh hs hc hq hHy hGy hBy hDy
      hvar ha hz he hhg hHG hGA hAB hBT hTD hDE hEH hk hl hcoef hratio
    exact (not_le_of_gt (hpositive i j)) hh
  rcases hHG with hh|hh
  · exact finish 0 (Or.inl rfl) hh
  · exact finish 2 (Or.inr rfl) hh

end Source

open Candidate Secondary

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals
