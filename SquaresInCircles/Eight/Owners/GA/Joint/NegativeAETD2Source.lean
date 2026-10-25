module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Concentrated
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2GainComparison

/-!
# Eight squares: negative A and core E with positive TD2

The seven separation inequalities of the cycle give a nonpositive stress
(`concentrated_nonpositive`). Its common baseline and the signed budgets imply a nonpositive
concentrated scalar, against the coefficient family. The concentrated alternatives are bounds on
the scalar, not configurations, and no support point is moved.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
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
    R (GlobalGA.Secondary.diagonal-1/2)
    (Concentrated.p f atG atH r s (delta C.theta T))
    (Concentrated.q f atG atH r s (delta C.theta T))
    (fun i => (blocks C hg atG atH k c r s i).P)
    (fun i => (blocks C hg atG atH k c r s i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => show _≤2*_ by
      have hh := hp i; dsimp only [Concentrated.p,Concentrated.q]; linarith [hh.1,hh.2.2])
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

/-- The four flat-core systems are impossible. Zero endpoints are allowed; the entry theorems give
the strict interior cuts. -/
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

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
