module

public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter

/-!
# Eight squares: both signs of both canceling outer errors in an ordered common middle

Once D ≤ A = B ≤ H, the actual canceling HG2
and TD0 pairs align at the same radius.  The larger middle tangent is
treated first only to prove that the opposite original tangent exceeds
one fifth.  Both concrete outputs are then constructed from the separate
original anchor circles.  No descendant circle equality is substituted
for a source circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter PositiveCancelingOuter
namespace SignedCycle

theorem HardInput.ordered_canceling_HG_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hAy : 1/5≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 2) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-|I.cycle.theta G-I.cycle.theta H|/3)) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread H A
    refine ⟨sub_nonneg.mpr hAH,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta G-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread G A
    refine ⟨sub_nonneg.mpr hAG,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 2 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hh := ordered_G_alignment hqL hq (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A) (I.necessary.contained H)
    (I.necessary.contained A) I.anchors_normal.H_nonneg hAy hΘ ht hHG' hGA'
  simpa [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
    I.cycle.theta G-I.cycle.theta H by ring] using hh

theorem HardInput.ordered_canceling_TD_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hBy : (I.cycle.point B).y≤ -(1/5 : ℝ))
    (hTD : I.cycle.Feasible T 0) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-|I.cycle.theta T-I.cycle.theta D|/3)) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B D
    refine ⟨sub_nonneg.mpr hDB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta B-I.cycle.theta T∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B T
    refine ⟨sub_nonneg.mpr hTB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  have hh := ordered_T_alignment hqL hq (I.necessary.sorted B) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D) (I.necessary.contained B)
    (I.necessary.contained D) hBy I.anchors_normal.D_nonpos hΘ ht hBT' hTD'
  rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
    I.cycle.theta D-I.cycle.theta T by ring,abs_sub_comm] at hh
  exact hh

end SignedCycle
end SquaresInCircles.Eight
