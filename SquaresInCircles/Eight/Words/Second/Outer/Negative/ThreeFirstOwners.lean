module

public import SquaresInCircles.Eight.Words.Second.Outer.KBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners

/-!
# Eight squares: the first two original weak owners for negative edge three

A global chord for `K` and a global increment bound for `T` turn the
source-secondary projection directly into one positive quadratic.
The other three halves use the original geometric implication and
original angle order.  No auxiliary contact interval is needed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo (source_mem primary_mem)

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have hb := source_mem hs
  have hB := source_mem ht
  have htr := positive_trig hx
  have hreserve := positive_taylor_reserves hx
  have hcut := lower_first_cut hx hm
  have hcos := mul_le_mul_of_nonneg_right
    (show A-1/2≤183/200 by linarith [(primary_mem ht).2,outer_endpoint_bounds.2.1])
    (show 0≤Real.cos x by linarith [htr.1])
  have hT := T_increment_upper outer_zero_mem hb hb.1
  rw [T_zero] at hT
  have hK := K_chord hB
  have hBs := mul_le_mul_of_nonneg_left htr.2.2.2.1.le hB.1
  have hquadratic : (93/100:ℝ)<Real.pi/2-x-167/10000-
      (1069/1000)*(183/200)*(1-(47/100)*x^2)+
        (1069/2000)*((9/10)*x)+1069/2000+K 0 := by
    nlinarith [pi_hand_enclosure.1,K_zero_bounds.1,sq_nonneg (x-113/200),hx.1]
  dsimp [value]
  nlinarith [hreserve.1,hreserve.2.1]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hh := original_lower_source_secondary hs ht hx (upper_first_implies_lower ht hx hm)
  dsimp [value] at *
  linarith [hx.1]

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have ht0 : OuterState outerAxial 0 := by
    simpa only [ShortOuterOne.SameContact.arc_zero] using
      ShortOuterOne.SameContact.arc_state outer_zero_mem
  have hh := original_lower_source_secondary hs ht0 hx
    (NegativeTwo.lower_second_implies_axial_first hs ht hx hm)
  have hK := K_lower (source_mem ht)
  dsimp [value] at *
  linarith

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hK := K_lower (source_mem ht)
  by_cases hsmall : x≤11/100
  · have hb := NegativeTwo.upper_second_small_source hs ht ⟨hx.1,hsmall⟩ hm
    have hT := T_monotone (source_mem hs) T_six_mem hb.le
    dsimp [value]
    linarith [pi_hand_enclosure.1,T_six_value,K_zero_bounds.1,hx.1]
  · have hT := T_upper (source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,K_zero_bounds.1]

end SquaresInCircles.Eight.SecondWord.NegativeThree
