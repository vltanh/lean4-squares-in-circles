module

public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Positive.NoncancelingOuter

/-!
# Eight squares: positive HG0/TD2 alignment retains the original large-side circle

These actual hard-cycle constructors invoke the
unlifted same-circle reserve.  The source large middle primary decreases
by one sixtieth of the original outer error.  Every other anchor, every
original mixed E witness, and the opposite intermediate are unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG0_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hlarge : 1/2≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 0) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-(2/9)*(I.cycle.theta G-I.cycle.theta H))) := by
  have hspan : (I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread G A)
    dsimp [frameCap] at hh
    linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta G-I.cycle.theta H) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))) 0 := by
    rw [show -((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))=
      I.cycle.theta A-I.cycle.theta G by ring]
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  exact PositiveNoncancelingOuter.actual_G_alignment hqL hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained G) (I.necessary.contained A)
    I.anchors_normal.H_nonneg hGy hlarge (sub_nonneg.mpr hAH)
    (sub_nonneg.mpr hHGorder) hspan hHG' hGA'

theorem HardInput.positive_TD2_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T≤I.cycle.theta D)
    (hTy : 0≤(I.cycle.point T).y) (hlarge : 1/2≤ -(I.cycle.point B).y)
    (hTD : I.cycle.Feasible T 2) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-(2/9)*(I.cycle.theta D-I.cycle.theta T))) := by
  have hspan : (I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread B T)
    dsimp [frameCap] at hh
    linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta T) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))) 2 := by
    rw [show -((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))=
      I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact PositiveNoncancelingOuter.actual_T_alignment hqL hq
    (I.necessary.sorted B) (I.necessary.sorted T) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D)
    (I.necessary.contained B) (I.necessary.contained T) (I.necessary.contained D)
    hlarge hTy I.anchors_normal.D_nonpos (sub_nonneg.mpr hDB)
    (sub_nonneg.mpr hTDorder) hspan hBT' hTD'

end SignedCycle
end SquaresInCircles.Eight
