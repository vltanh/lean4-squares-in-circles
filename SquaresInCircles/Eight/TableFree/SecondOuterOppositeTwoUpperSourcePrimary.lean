module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoPrimaryAxis
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoUpperTargetPrimary

/-!
# The original upper source-primary owner of opposite outer edge two

The weak separator is compared with its exact inverse angle at the
original source primary height.  The target ratio makes its contact
cost monotone along the whole target circle.  The two possible initial
points are the actual aligned contact and the completed zero-target
boundary.  All original states and weak ties are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hz : a-1/2∈PrimaryInverse.shifts := by
    constructor <;> linarith [(outer_bounds hs).1,(outer_bounds hs).2.1,
      fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hdiag : TargetRatio.z≤a-1/2 := by
    dsimp [TargetRatio.z]
    linarith [(outer_bounds hs).1]
  have hcut : upperPrimary A B x≤(a-1/2)+1/2 := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperPrimary]
    linarith
  have hX := PrimaryInverse.weak_angle ht hx hz hcut
  have hmono := PrimaryInverse.targetCost_monotone hz hdiag
  by_cases ha : 1≤a
  · have hbase : a-1∈Icc 0 outerDiagonal := by
      refine ⟨by linarith,?_⟩
      linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    by_cases hBbase : B≤a-1
    · have halign := aligned_right_original hs ht (by linarith)
      dsimp [value] at *
      linarith
    · have hstep := hmono hbase hB (by linarith)
      have hzero := PrimaryInverse.aligned hbase
        (show a-1/2=W (a-1) by dsimp [W]; ring)
      dsimp [PrimaryInverse.targetCost] at hstep
      rw [hzero] at hstep
      have halign := aligned_right_original hs (ShortOuterOne.SameContact.arc_state hbase)
        (show 1+(a-1)≤a by linarith)
      dsimp [value] at *
      linarith
  · have hA : a∈PrimaryAxis.interval := ⟨(outer_bounds hs).1,by linarith⟩
    have hbase := PrimaryAxis.cost_lower hA
    have hstep := hmono outer_zero_mem hB hB.1
    have hsource : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    dsimp [PrimaryAxis.cost,PrimaryInverse.targetCost,value] at *
    rw [hsource] at hbase
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
