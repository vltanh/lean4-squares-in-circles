module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Low
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSource

/-!
# The complete original negative-DE3 / positive-TD2 source exclusion

Uncompiled conclusion of the complete scalar and angle companions.
The low and high total ranges meet at the exact intrinsic value 1/6.
Both HG owners, all four original A-owner choices, arbitrary individual
A signs with nonnegative selected total, and all weak contacts remain
in the statement. No scalar positivity hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
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

/-- Physical-axis adapter retaining the original selected A total and
the actual negative-DE and nonnegative-TD angles. -/
theorem frame_flat_false {Q : ℝ} {C : BoundaryCycle Q}
    (F : Candidate.Frame C) (hQ : Q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab : Bool)
    (ha : 0≤aTotal (SignedCycle.atFrame F) ga ab)
    (hz : 0≤delta F.theta T) (hs : delta F.theta D≤0)
    (hflat : ((SignedCycle.atFrame F).point E).a=7/12)
    (hHG : (forwardAxis 0).Feasible (C.square H) (C.square G)∨
      (forwardAxis 2).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 3).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H)) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hQ
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hQ hE
  have hhigh : (if ga then (3:Fin 4) else 2)=2∨(if ga then (3:Fin 4) else 2)=3 := by
    cases ga <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hQ G (by norm_num [word,G])
    (if ga then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hGy : ((SignedCycle.atFrame F).point G).y≤0 :=
    ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  apply actual_false ga ab hn.sorted hn.contained hQ.2 hHy.le hGy hBy.le hDy.le
    hv.1.le ha hz hs hflat
  · rcases hHG with hh|hh
    · exact Or.inl ((SignedCycle.atFrame_feasible F H 0).2 (by simpa [H,G,next] using hh))
    · exact Or.inr ((SignedCycle.atFrame_feasible F H 2).2 (by simpa [H,G,next] using hh))
  · exact (SignedCycle.atFrame_feasible F G (if ga then 3 else 2)).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if ab then 2 else 0)).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 3).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
