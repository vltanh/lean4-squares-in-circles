module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Scalar
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3OriginalStress
public import SquaresInCircles.Eight.TableFree.NegativeCoreEEntry
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Source

/-!
# Complete original negative-DE3 / nonnegative-BT3 exclusion

Uncompiled original-source conclusion. The scalar family is selected
from the actual A/BT total. Both HG owners, all four A selections and
arbitrary individual selected A signs remain. The original TD0 angle
and the original EH0 angle are unrestricted in sign. Core E flatness
is derived from that same original EH0 separator, without moving E or
replacing a physical witness. The source radius is unchanged throughout.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem original_flat_false {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hb0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨f,hθ⟩ := Scalar.family_cover hb0.total_domain
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hn := scalar_nonpositive hg ga ab f hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := Scalar.scalar_positive f
    (a:=aTotal C ga ab) (z:=delta C.theta B) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  exact (not_le_of_gt hp) hn

/-- The initial physical EH0 itself forces the original core E flat. -/
lemma original_flat {Q : ℝ} {C : SignedCycle}
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hEH : C.Feasible E 0) : (C.point E).a=7/12 := by
  have hh : quarterFeasible (C.point E) (C.point H) (delta C.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  exact (NegativeCoreE.secondary_flat (hsorted E) hEy hEc
    (hsorted H) (hcontained H) hQ hh).1

theorem original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 0 := by simpa [owners,E] using hfeasible E
  exact original_flat_false hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs (original_flat hsorted hcontained hQ hEy hEc hEH) hfeasible

/-- No chosen HG representative and no sign restriction on TD0 or EH0. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
    hvar ha hz hs
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

/-- Original frame, original radius, and original weak physical separators. -/
theorem frame_false {Q : ℝ} {C : BoundaryCycle Q}
    (F : Candidate.Frame C) (hQ : Q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab : Bool) (hEc : ((SignedCycle.atFrame F).point E).Core)
    (ha : 0≤aTotal (SignedCycle.atFrame F) ga ab)
    (hz : 0≤delta F.theta B) (hs : delta F.theta D≤0)
    (hHG : (forwardAxis 0).Feasible (C.square H) (C.square G)∨
      (forwardAxis 2).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
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
  have hEy : ((SignedCycle.atFrame F).point E).y≤0 :=
    (SignedCycle.atFrame_y_nonpos_iff F E).2 hE
  apply actual_false ga ab hn.sorted hn.contained hQ.2 hHy.le hGy hBy.le hDy.le
    hEy hEc hv.1.le ha hz hs
  · rcases hHG with hh|hh
    · exact Or.inl ((SignedCycle.atFrame_feasible F H 0).2 (by simpa [H,G,next] using hh))
    · exact Or.inr ((SignedCycle.atFrame_feasible F H 2).2 (by simpa [H,G,next] using hh))
  · exact (SignedCycle.atFrame_feasible F G (if ga then 3 else 2)).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if ab then 2 else 0)).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 3).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 3).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Source
