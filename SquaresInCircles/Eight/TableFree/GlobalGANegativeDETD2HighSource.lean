module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2High
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2OriginalStress

/-!
# Original-source contradiction for the complete high-total negative-DE branch

Uncompiled source conclusion for the high half of the negative-DE TD2
companion. The seven actual separator witnesses give a nonpositive
weighted stress, whereas the just-proved scalar theorem is positive
for their original signed budgets. Both HG owners, all four A owner
choices, arbitrary individual A signs, and weak contacts are retained.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

theorem high_original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12) (hlarge : (1/6:ℝ)≤total C ga ab)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  let k := Explicit.k .high (total C ga ab)
  let l := Explicit.l .high (total C ga ab)
  let c := Explicit.c .high (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hθ : total C ga ab∈Icc (1/6:ℝ) (7/10) := ⟨hlarge,hb.total_domain.2⟩
  have hn := scalar_nonpositive hg ga ab .high hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := High.scalar_positive
    (a:=aTotal C ga ab) (z:=delta C.theta T) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  have hbase := fullBaseline_le .high (aTotal C ga ab) (delta C.theta T) (magnitude C)
  change 0<Explicit.fullBaseline .high (aTotal C ga ab) (delta C.theta T) (magnitude C)+
    ∑i,mixedBlock R (Explicit.p .high (total C ga ab) (delta C.theta T) i)
      (Explicit.q .high (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N at hp
  linarith

/-- Adapter with the seven original witnesses written individually. -/
theorem high_actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12) (hlarge : (1/6:ℝ)≤total C ga ab)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply high_original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs hflat hlarge
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
