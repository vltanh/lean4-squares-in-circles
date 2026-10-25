module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeSource
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSplit
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowStress

/-!
# Eight squares: positive BT3 with arbitrary TD0 and nonnegative A/E totals

The low
total uses the complete signed sorted-D envelope; the large total
uses its native triangle or rectangle family.  Every coefficient,
split endpoint, and angular concentration bound is supplied internally.
The original TD0 error and both constituents of each A/E pair remain
unchanged, including mixed signs and weak owner ties.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem low_actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (ht : total C ga ab de eh∈Icc 0 (1/6:ℝ))
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible Candidate.D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  let t := total C ga ab de eh
  let k := lowK t
  let m := lowM t
  have hbud := budgets hg ga ab de eh k 1 m hvar ha hu he
  have henv := LowEnvelope.lower ht
    (fun i => (blocks C hg ga ab de eh k 1 m i).P)
    (fun i => (blocks C hg ga ab de eh k 1 m i).N)
    (fun i => (blocks C hg ga ab de eh k 1 m i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh k 1 m i).N_nonneg)
    hbud.2.2.2.2.2 hbud.2.2.2.2.1
  have hminor := low_stress_lower ga ab de eh hs hc hq hHy hGy hBy hDy
    hvar ha hu he hhg ht
  have hsplit : aTotal C ga ab+eTotal C de eh∈Icc 0 t := by
    dsimp [t,total]
    constructor <;> linarith
  have hangle : t-(aTotal C ga ab+eTotal C de eh)=delta C.theta B := by
    dsimp [t,total]
    ring
  have hpositive := Analytic.low_scalar_positive ht hsplit
  change 0<Analytic.lowBaseline k m (t-(aTotal C ga ab+eTotal C de eh))+
    TwoPositive.ASupport.charge (aTotal C ga ab+eTotal C de eh)+V R k 1 t at hpositive
  rw [hangle] at hpositive
  have henv' : V R k 1 t≤∑i,lowBlock t i
      (blocks C hg ga ab de eh k 1 m i).P
      (blocks C hg ga ab de eh k 1 m i).N := by
    simpa only [LowEnvelope.block,LowEnvelope.p,LowEnvelope.q,lowBlock] using henv
  have hr := Analytic.low_ranges ht
  have hupper := stress_nonpositive ga ab de eh
    (show 0≤k by dsimp [k,t]; linarith [hr.1.1]) (by norm_num : (0:ℝ)≤1)
    (show 0< m by dsimp [m,t]; linarith [hr.2.1]) hbud.2.2.1
    hHG hGA hAB hBT hTD hDE hEH
  linarith

/-- Source exclusion with only the original geometric conditions and
the three nonnegative selected totals. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible Candidate.D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hlow : total C ga ab de eh≤1/6
  · exact low_actual_false ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha hu he
      ⟨by dsimp [total]; linarith,hlow⟩ hHG hGA hAB hBT hTD hDE hEH
  · exact large_actual_false ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha hu he
      (lt_of_not_ge hlow).le hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.Source

namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3
open Candidate Secondary

end SquaresInCircles.Eight.GlobalGA.PositiveBT3
