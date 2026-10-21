module

public import SquaresInCircles.Eight.TableFree.GlobalBTOnePositiveScalar

/-!
# Pointwise positive-BT1 removal on the original states

The global quarter-owner theorem already makes the actual T outer.
Its original primary is therefore at least the diagonal coordinate,
which pays the primary loss directly.  The B increment uses its
unchanged signed circle.  No maximizing point is introduced.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OnePositive

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem B_increment (b : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤kappa*Real.sin x*(R-(Real.cos x+Real.sin x)/2-
      (Real.cos x*b.a-Real.sin x*transverse b)) := by
  have tr := transport_trig hx
  have hs := state_support b (Real.cos x) (Real.sin x)
  have hunit : (Real.cos x)^2+(Real.sin x)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq x]
  rw [hunit,Real.sqrt_one,mul_one] at hs
  have hy := mul_nonneg tr.2.2.1
    (show 0≤b.b+transverse b by linarith [(transverse_bounds b).1])
  have hinner : 0≤R-(Real.cos x+Real.sin x)/2-
      (Real.cos x*b.a-Real.sin x*transverse b) := by
    change Real.cos x*b.a+Real.sin x*b.b≤R-(Real.cos x+Real.sin x)/2 at hs
    linarith only [hs,hy]
  exact mul_nonneg (mul_nonneg (by norm_num [kappa]) tr.2.2.1) hinner

theorem difference_identity (b t : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    quarterDual b t 1 x (kappa*Real.cos x)-quarterDual b t 0 0 kappa=
      gain x+kappa*Real.sin x*(R-(Real.cos x+Real.sin x)/2-
        (Real.cos x*b.a-Real.sin x*transverse b))+
          kappa*(1-Real.cos x)*(t.a-c0) := by
  dsimp [quarterDual]
  rw [width_positive hx]
  simp only [projection,Bool.true_eq_true,if_true,Matrix.cons_val_one,Matrix.cons_val_zero,
    width,Real.cos_zero,Real.sin_zero,abs_zero,mul_one,mul_zero,add_zero,zero_add]
  dsimp [gain]
  linear_combination kappa*(1/2-transverse b)*(Real.sin_sq_add_cos_sq x)

theorem delete (b t : State) (hT : c0≤t.a) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    quarterDual b t 0 0 kappa≤quarterDual b t 1 x (kappa*Real.cos x) := by
  have hB := B_increment b hx
  have hTgain := mul_nonneg
    (mul_nonneg (by norm_num [kappa] : 0≤kappa)
      (sub_nonneg.mpr (Real.cos_le_one x))) (sub_nonneg.mpr hT)
  have hG := gain_nonnegative hx
  have hid := difference_identity b t hx
  linarith

theorem delete_outer (b t : State) (hT : t.branch.type≠0) {x : ℝ}
    (hx : x∈Icc 0 frameCap) :
    quarterDual b t 0 0 kappa≤quarterDual b t 1 x (kappa*Real.cos x) := by
  have ht := state_outer_chart t hT
  have ha := (A_bounds ht.2).1
  rw [← ht.1] at ha
  exact delete b t ha hx

theorem actual_aligned_charge (b t : State) (hT : t.branch.type≠0) {x : ℝ}
    (hx : x∈Icc 0 frameCap) (hBT : width x≤projection true b t x 1) :
    quarterDual b t 0 0 kappa≤x := by
  have hl : 0≤kappa*Real.cos x :=
    mul_nonneg (by norm_num [kappa]) (by linarith [(transport_trig hx).1])
  exact (delete_outer b t hT hx).trans (quarterDual_le_error b t 1 hl hBT)

end SquaresInCircles.Eight.TableFree.GlobalBT.OnePositive
