module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Concentrated
public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Minorant

/-!
# Joint negative A and core E with original positive BT3 and actual TD0

Uncompiled completion of the four one-primary exclusions in the
joint-negative BT3 hand proof. The actual seven separator inequalities
give a nonpositive stress. Their unchanged signed angle budgets force
one of the positive concentrated alternatives, which is impossible.
The independent TD0 error and the original T radial state are retained.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3
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
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    ∃i j : Fin 5,Concentrated.scalar f atG atH r s (delta C.theta B) i j≤0 := by
  let k := Explicit.k f (delta C.theta B)
  let m := Explicit.m f (delta C.theta B)
  let c := Explicit.c f (delta C.theta B)
  let eta := Explicit.eta f (delta C.theta B)
  have hz' := Explicit.frame_domain f hz
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩
  have hb := budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz'.1
  have hp := pair_domain f atG atH hz hr hs hH
  obtain ⟨i,j,hendpoint⟩ := NegativeAPositiveTD.Concentration.concentrate
    R (Penalty.cost c (r+s))
    (Concentrated.p f atG atH r s (delta C.theta B))
    (Concentrated.q f atG atH r s (delta C.theta B))
    (fun i => (blocks C hg atG atH k m c r s i).P)
    (fun i => (blocks C hg atG atH k m c r s i).N) (distinguished atH c)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => show _≤2*_ by have hh := hp i; linarith [hh.1,hh.2.2])
    (fun i => (blocks C hg atG atH k m c r s i).P_nonneg)
    (fun i => (blocks C hg atG atH k m c r s i).N_nonneg)
    hb.total_domain hz' hb.positive_bound hb.negative_bound hb.balance
  have hc := Explicit.ranges f hz
  have hf : tilt eta (delta C.theta B)≠0 :=
    (show 0<Explicit.f f (delta C.theta B) by linarith [hc.f_domain.1]).ne'
  have hbase := common_baseline_lower (k:=k) (m:=m) (c:=c) (eta:=eta) atG atH
    (show 0<k by dsimp [k]; linarith [hc.k_domain.1])
    (show k≤1 by dsimp [k]; linarith [hc.k_domain.2])
    (hc.k_le_m.trans hc.m_le_c) hc.k_le_m hr' hs hz' hf (family_rotation f hz)
  have hlower := original_stress_lower f atG atH hsorted hcontained hq
    hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hz
  have hupper := stress_nonpositive (k:=k) (m:=m) (c:=c) atG atH
    (show 0≤k by dsimp [k]; linarith [hc.k_domain.1])
    (show 0≤m by dsimp [m]; linarith [hc.k_domain.1,hc.k_le_m])
    (show 0≤c by dsimp [c]; linarith [hc.c_domain.1]) hr' hs
    hHG hGA hAB hBT hTD hDE hEH
  refine ⟨i,j,?_⟩
  change min (Concentrated.pure f atG atH r s (delta C.theta B) i j)
    (Concentrated.saturated f atG atH r s (delta C.theta B) i j)≤_ at hendpoint
  dsimp only [Concentrated.p,Concentrated.q,Concentrated.cost,Concentrated.selected] at hendpoint
  dsimp only [Concentrated.scalar,Concentrated.base]
  change baseline k c eta (delta C.theta B)+F k r+F k s+_≤0
  linarith

end Source

theorem row_cover {z : ℝ} (hz : z∈Icc 0 frameCap) :
    ∃f : Row,z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ) := by
  by_cases hl : z≤3/20
  · exact ⟨.low,by simpa [Certificate.left,Certificate.right] using And.intro hz.1 hl⟩
  by_cases hm : z≤1/4
  · exact ⟨.middle,by simp [Certificate.left,Certificate.right]; constructor <;> linarith⟩
  · exact ⟨.high,by simp [Certificate.left,Certificate.right,frameCap] at *; constructor <;> linarith⟩

/-- All four original one-negative-A, one-negative-E systems are
excluded with positive BT3 and an arbitrary signed TD0 companion. -/
theorem original {q r s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : Source.aError C atG= -r) (he : Source.eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hz : 0≤delta C.theta B) (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) : False := by
  have hb := Source.budgets hg atG atH 1 1 1 hr.1 hs.1 ha he hvar hz
  obtain ⟨f,hf⟩ := row_cover hb.bt_domain
  obtain ⟨i,j,hij⟩ := Source.concentrated_nonpositive f atG atH
    hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hf
    hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (Concentrated.all_positive f atG atH hf hr hs hH hb.total_domain.2 i j)) hij

theorem frame_flat_false {q r s : ℝ} {C : BoundaryCycle q} {hg : Fin 4}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG atH : Bool) (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4)
    (ha : Source.aError (SignedCycle.atFrame F) atG= -r)
    (he : Source.eError (SignedCycle.atFrame F) atH= -s)
    (hAflat : ((SignedCycle.atFrame F).point A).a=7/12)
    (hEflat : ((SignedCycle.atFrame F).point E).a=7/12)
    (hz : 0≤delta F.theta B) (hhg : hg=0∨hg=2)
    (hHG : (forwardAxis hg).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
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
  · exact (SignedCycle.atFrame_feasible F B 3).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D (if atH then 2 else 3)).2
      (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E (if atH then 1 else 0)).2
      (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3
