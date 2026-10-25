module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3ScalarSource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Source

/-!
# Complete original genuine-negative-EH1 / nonnegative-BT3 exclusion

Uncompiled original-cycle and physical-frame conclusion. All four
analytic families are supplied internally from the unchanged errors.
The original TD0 and DE2 errors keep both signs; HG has either weak
owner, and the four selected A-owner choices retain mixed individual
signs. The genuine EH1 entry supplies flatness and its short magnitude
from the original E and H points. No endpoint or scalar premise remains.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem original_flat_false {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hcap : magnitude C≤1/4)
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hb0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨f,hθ,he⟩ := Scalar.family_cover hb0.total_domain ⟨hb0.eh_domain.1,hcap⟩
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  have hn := scalar_nonpositive f (hg:=hg) ga ab hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hb hθ he hhg hfeasible
  have hp := Scalar.scalar_positive f
    (a:=aTotal C ga ab) (z:=delta C.theta B) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N) hθ ha hz he
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    hbud.positive_bound hbud.negative_bound hbud.balance
  exact (not_le_of_gt hp) hn

/-- Genuine EH1 is tested on the original cycle, before any transport. -/
theorem original {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 1 := by simpa [owners,PositiveBT3.Source.owners,E] using hfeasible E
  obtain ⟨hf,hb,hu⟩ := NegativeEHPositiveTD.Source.genuine_domain
    hsorted hcontained hQ hHy hEy hEc hvar hs hEH hnot
  exact original_flat_false hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs.le hf hb hu hhg hfeasible

/-- All seven original witnesses, including either HG representative. -/

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 1) : False := by
  obtain ⟨hg,hhg,hHG'⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
    hvar ha hz hs hnot hhg
  intro i
  fin_cases i
  · simpa [owners,PositiveBT3.Source.owners,H] using hHG'
  · simpa [owners,PositiveBT3.Source.owners,G] using hGA
  · simpa [owners,PositiveBT3.Source.owners,A] using hAB
  · simpa [owners,PositiveBT3.Source.owners,B] using hBT
  · simpa [owners,PositiveBT3.Source.owners,T] using hTD
  · simpa [owners,PositiveBT3.Source.owners,D] using hDE
  · simpa [owners,PositiveBT3.Source.owners,E] using hEH

/-- Physical weak axes are the initially supplied source axes. -/

theorem frame_false {Q : ℝ} {C : BoundaryCycle Q}
    (F : Candidate.Frame C) (hQ : Q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab : Bool) (hEc : ((SignedCycle.atFrame F).point E).Core)
    (ha : 0≤aTotal (SignedCycle.atFrame F) ga ab)
    (hz : 0≤delta F.theta B) (hs : delta F.theta E<0)
    (hnot : ¬(forwardAxis 0).Feasible (C.square E) (C.square H))
    (hHG : (forwardAxis 0).Feasible (C.square H) (C.square G)∨
      (forwardAxis 2).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 1).Feasible (C.square E) (C.square H)) : False := by
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
  · intro h
    apply hnot
    simpa [E,H,next] using (SignedCycle.atFrame_feasible F E 0).1 h
  · rcases hHG with hh|hh
    · exact Or.inl ((SignedCycle.atFrame_feasible F H 0).2 (by simpa [H,G,next] using hh))
    · exact Or.inr ((SignedCycle.atFrame_feasible F H 2).2 (by simpa [H,G,next] using hh))
  · exact (SignedCycle.atFrame_feasible F G (if ga then 3 else 2)).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if ab then 2 else 0)).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 3).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 1).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
