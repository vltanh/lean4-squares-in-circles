module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Low
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSource

/-!
# Eight squares: the complete original negative-DE3 / positive-TD2 source exclusion

The low and high total ranges meet at the exact intrinsic value 1/6.
Both HG owners, all four original A-owner choices, arbitrary individual
A signs with nonnegative selected total, and all weak contacts remain
in the statement. No scalar positivity hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem low_original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12) (hsmall : total C ga ab≤1/6)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  let k := Explicit.k .low (total C ga ab)
  let l := Explicit.l .low (total C ga ab)
  let c := Explicit.c .low (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hθ : total C ga ab∈Icc (0:ℝ) (1/6) := ⟨hb.total_domain.1,hsmall⟩
  have hn := scalar_nonpositive hg ga ab .low hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := Low.scalar_positive
    (a:=aTotal C ga ab) (z:=delta C.theta T) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  change 0<Explicit.baseline .low (aTotal C ga ab) (delta C.theta T) (magnitude C)+
    ∑i,mixedBlock R (Explicit.p .low (total C ga ab) (delta C.theta T) i)
      (Explicit.q .low (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N at hp
  exact (not_le_of_gt hp) hn

theorem original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  by_cases hsmall : total C ga ab≤1/6
  · exact low_original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hflat hsmall hfeasible
  · exact high_original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hflat (lt_of_not_ge hsmall).le hfeasible

/-- The seven original witnesses suffice; neither the size of the total
nor a reduced scalar endpoint is an additional premise. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs hflat
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
