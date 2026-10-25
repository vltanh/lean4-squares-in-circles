module

public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.SpanNormBounds

/-!
# Eight squares: signed middle-block compression, including cancellation

The two same-sign inequalities use the proved
whole-interval concavity. Opposite signs use the actual finite derivative
bounds and the ordinary chord bounds. Thus cancellation preserves the
original signed error and does not require the original errors to share
a sign.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleAngularStress
open PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open OrdinaryNegativeEnvelope OrdinaryPositiveEnvelope

def B (lambda s : ℝ) : ℝ :=
  if 0≤ s then U (Real.sqrt qCap) lambda 1 s
  else V (Real.sqrt qCap) lambda 1 (-s)

theorem B_of_nonneg {lambda s : ℝ} (hs : 0≤ s) :
    B lambda s=U (Real.sqrt qCap) lambda 1 s := by simp [B,hs]

theorem B_of_nonpos {lambda s : ℝ} (hs : s≤0) :
    B lambda s=V (Real.sqrt qCap) lambda 1 (-s) := by
  by_cases hz : s=0
  · simp [B,hz]
  · have hnot : ¬0 ≤ s := not_le.mpr (lt_of_le_of_ne hs hz)
    simp [B,hnot]

@[simp] theorem B_zero (lambda : ℝ) : B lambda 0=0 := by simp [B]

theorem opposite_subadditive {lambda x s : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hx : x∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    B lambda (x-s)≤U (Real.sqrt qCap) lambda 1 x+V (Real.sqrt qCap) lambda 1 s := by
  have hl0 : 0<lambda := by linarith [hl.1]
  have hl1 : lambda≤1 := by linarith [hl.2]
  have hl2 : (1:ℝ)≤2*lambda := by linarith [hl.1]
  by_cases hsx : s≤x
  · have hdiff : x-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hx.2,hs.1]⟩
    rw [B_of_nonneg hdiff.1]
    have hg := SpanNormBounds.U_growth hl hdiff hx (by linarith [hs.1])
    have hV := V_chord_lower hl0 hl1 hl2 hs
    have hmul := mul_le_mul_of_nonneg_right hl.1 hs.1
    dsimp [SpanNormBounds.U,SpanNormBounds.R] at hg
    linarith [hs.1]
  · have hxs : x ≤ s := (lt_of_not_ge hsx).le
    have hdiff : s-x∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hx.1]⟩
    rw [B_of_nonpos (show x-s≤0 by linarith),show -(x-s)=s-x by ring]
    have hg := SpanNormBounds.V_growth hl hdiff hs (by linarith [hx.1])
    have hU := U_lower (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hl0 hl1 hl2 hx
    dsimp [SpanNormBounds.V,SpanNormBounds.R] at hg
    linarith [hx.1]

theorem subadditive {lambda d v : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hsum : |d+v|≤frameCap) :
    B lambda (d+v)≤B lambda d+B lambda v := by
  have hl0 : 0<lambda := by linarith [hl.1]
  have hl1 : lambda≤1 := by linarith [hl.2]
  have hl2 : (1:ℝ)≤2*lambda := by linarith [hl.1]
  have hR := Real.sqrt_nonneg qCap
  have hQ := (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    by_cases hv0 : 0≤v
    · rw [B_of_nonneg (add_nonneg hd0 hv0),B_of_nonneg hd0,B_of_nonneg hv0]
      exact concave_zero_subadditive (U_concave hR hQ hl0 hl1 hl2) (by simp)
        hd0 hv0 ((le_abs_self (d+v)).trans hsum)
    · have hv0' : v≤0 := (lt_of_not_ge hv0).le
      have hv' : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
      rw [B_of_nonneg hd0,B_of_nonpos hv0']
      simpa only [sub_neg_eq_add] using opposite_subadditive hl hd' hv'
  · have hd0' : d≤0 := (lt_of_not_ge hd0).le
    have hd' : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    by_cases hv0 : 0≤v
    · have hv' : v∈Icc 0 frameCap := ⟨hv0,(le_abs_self v).trans hv⟩
      rw [B_of_nonpos hd0',B_of_nonneg hv0]
      have h := opposite_subadditive hl hv' hd'
      simpa only [sub_neg_eq_add,add_comm] using h
    · have hv0' : v≤0 := (lt_of_not_ge hv0).le
      rw [B_of_nonpos (add_nonpos hd0' hv0'),B_of_nonpos hd0',B_of_nonpos hv0']
      have hn : -d+-v≤frameCap := by
        have h := (neg_le_abs (d+v)).trans hsum
        linarith
      simpa only [neg_add_rev,add_comm] using concave_zero_subadditive
        (V_concave hR hQ hl0 hl1 hl2) (by simp)
        (show 0≤-d by linarith) (show 0≤-v by linarith) hn

end SquaresInCircles.Eight.MiddleAngularStress
