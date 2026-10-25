module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2High
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress

/-!
# Eight squares: the contradiction in the high-total negative-DE branch

The seven separator witnesses of the cycle give a nonpositive weighted stress, whereas the scalar
theorem `High.scalar_positive` is positive for their signed budgets (`high_original`). Both HG
owners, all four A owner choices, every sign of the single A errors and weak contacts are covered.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
