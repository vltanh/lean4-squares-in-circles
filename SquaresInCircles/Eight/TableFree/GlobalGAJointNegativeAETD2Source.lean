module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Concentrated

/-!
# Joint negative A and core E in the actual positive-TD2 system

Uncompiled transcription of the four one-primary exclusions in the
joint-negative hand proof. The original seven physical inequalities
give a nonpositive stress. Its common baseline and original signed
budgets imply a nonpositive concentrated scalar, contradicting the
explicit coefficient family. No feasible concentrated configuration or
replacement support point is asserted.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

namespace Source

theorem concentrated_nonpositive {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    ∃i j : Fin 4,Concentrated.scalar f atG atH r s (delta C.theta T) i j≤0 := by
  let k := Explicit.k f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hz' := Explicit.frame_domain f hz
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩
  have hb := budgets hg atG atH k c hr.1 hs.1 ha he hvar hz'.1
  have hp := pair_domain f atG atH hz hr hs hH
  obtain ⟨i,j,hendpoint⟩ := NegativeAPositiveTD.Concentration.concentrate
    R (diagonal-1/2)
    (Concentrated.p f atG atH r s (delta C.theta T))
    (Concentrated.q f atG atH r s (delta C.theta T))
    (fun i => (blocks C hg atG atH k c r s i).P)
    (fun i => (blocks C hg atG atH k c r s i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => show _≤2*_ by have hh := hp i; linarith [hh.1,hh.2.2])
    (fun i => (blocks C hg atG atH k c r s i).P_nonneg)
    (fun i => (blocks C hg atG atH k c r s i).N_nonneg)
    hb.total_domain hz' hb.positive_bound hb.negative_bound hb.balance
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have hbase := common_baseline_lower (k:=k) (c:=c) atG atH
    (show 0<k by dsimp [k]; linarith [hk.1])
    (show k≤1 by dsimp [k]; linarith [hk.2]) hkc hkm hr' hs hz'
  have hlower := original_stress_lower f atG atH hsorted hcontained hq
    hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hz
  have hupper := stress_nonpositive (k:=k) (c:=c) atG atH
    (show 0≤k by dsimp [k]; linarith [hk.1])
    (show 0≤c by dsimp [k,c] at *; linarith [hk.1,hkc]) hr' hs hz'
    hHG hGA hAB hBT hTD hDE hEH
  refine ⟨i,j,?_⟩
  change min (Concentrated.pure f atG atH r s (delta C.theta T) i j)
    (Concentrated.saturated f atG atH r s (delta C.theta T) i j)≤_ at hendpoint
  dsimp only [Concentrated.p,Concentrated.q] at hendpoint
  dsimp only [Concentrated.scalar,Concentrated.base]
  change baseline k c (delta C.theta T)+F k r+F k s+_≤0
  linarith

end Source

theorem row_cover {z : ℝ} (hz : z∈Icc 0 frameCap) :
    ∃f : Row,z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ) := by
  by_cases hl : z≤3/20
  · exact ⟨.low,by simpa [Certificate.left,Certificate.right] using And.intro hz.1 hl⟩
  by_cases hm : z≤19/100
  · exact ⟨.transition,by simp [Certificate.left,Certificate.right]; constructor <;> linarith⟩
  · exact ⟨.full,by simp [Certificate.left,Certificate.right,frameCap] at *; constructor <;> linarith⟩

/-- All four original flat-core systems are impossible. Zero endpoints
are allowed; the actual entry theorems supply the strict interior cuts. -/
theorem original {q r s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : Source.aError C atG= -r) (he : Source.eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) : False := by
  have hb := Source.budgets hg atG atH 1 1 hr.1 hs.1 ha he hvar hz
  obtain ⟨f,hf⟩ := row_cover hb.td_domain
  obtain ⟨i,j,hij⟩ := Source.concentrated_nonpositive f atG atH
    hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hf
    hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (Concentrated.all_positive f atG atH hf hr hs hH hb.total_domain.2 i j)) hij

/-- Physical-axis adapter retaining the selected negative primary
errors and flat-core equalities on the original candidate frame. -/
theorem frame_flat_false {q r s : ℝ} {C : BoundaryCycle q} {hg : Fin 4}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG atH : Bool) (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4)
    (ha : Source.aError (SignedCycle.atFrame F) atG= -r)
    (he : Source.eError (SignedCycle.atFrame F) atH= -s)
    (hAflat : ((SignedCycle.atFrame F).point A).a=7/12)
    (hEflat : ((SignedCycle.atFrame F).point E).a=7/12)
    (hz : 0≤delta F.theta T) (hhg : hg=0∨hg=2)
    (hHG : (forwardAxis hg).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis (if atH then 2 else 3)).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis (if atH then 1 else 0)).Feasible (C.square E) (C.square H)) : False := by
  let S := SignedCycle.atFrame F
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hq
  obtain ⟨hHouter,hHy,hBouter,hBy,hDouter,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2∨(if atG then (3:Fin 4) else 2)=3 := by
    cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hGy : (S.point G).y≤0 := ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  apply original atG atH hn.sorted hn.contained hq.2 hHy.le hGy hBy.le hDy.le
    hv.1.le hr hs hH ha he hAflat hEflat hz hhg
  · exact (SignedCycle.atFrame_feasible F H hg).2 (by simpa [H,G,next] using hHG)
  · exact (SignedCycle.atFrame_feasible F G (if atG then 3 else 2)).2
      (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if atG then 0 else 2)).2
      (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D (if atH then 2 else 3)).2
      (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E (if atH then 1 else 0)).2
      (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2
