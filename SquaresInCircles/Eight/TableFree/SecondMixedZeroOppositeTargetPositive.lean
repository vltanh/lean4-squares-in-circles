module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeAligned

/-!
# The full nonnegative-angle target-secondary half

Uncompiled source draft.  The original weak target projection gives a
single transverse-sum loss, using only the primary core bound.  J and L
use their aligned reserves.  P uses its aligned minimum for angles at
least `.06`; below that angle, the same owner forces its actual outer
coordinate above `.435` and yields the stronger aligned reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.TargetPositive
open CommonQuarter CorePairGeometry Arithmetic

lemma transverse_sum {a b B x : ℝ} (hs : CoreState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤a*Real.sin x+b*Real.cos x+B) :
    1-x/12-x^2/4≤b+B ∧ 1-(31/120)*x≤b+B := by
  have tr := positive_trig hx
  have hc := CoreAngleEndpoint.state_bounds hs
  have ha := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hb := mul_nonneg hc.2.2.1 (sub_nonneg.mpr tr.2.1)
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_le hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  constructor <;> linarith

theorem original_projection (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤a*Real.sin x+b*Real.cos x+B) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hsum := transverse_sum hs hx hm
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hslope : 0<1-(31/120)*g r := by
    have hg := slope_bounds r
    linarith [hg.2]
  have hpay := mul_le_mul_of_nonneg_left hsum.2 (slope_bounds r).1.le
  have hbound : aligned r B+(1-(31/120)*g r)*x≤
      x+c r+g r*b+(F r).outer B := by
    dsimp [aligned]
    nlinarith only [hpay]
  by_cases hP : r=1
  · subst r
    by_cases hlarge : (3/50:ℝ)≤x
    · have hxpay := mul_le_mul_of_nonneg_left hlarge hslope.le
      have hl := P_aligned hB
      have hg : g 1=63132/100000 := rfl
      rw [hg] at hbound hxpay ⊢
      linarith
    · have hb : b<(559/1000:ℝ) := by
        linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
      have hsquare := pow_le_pow_left₀ hx.1 (le_of_not_ge hlarge) 2
      have htarget : (87/200:ℝ)≤B := by linarith [hsum.1]
      have hl := P_aligned_late hB htarget
      have hnon := mul_nonneg hslope.le hx.1
      linarith
  · have hl := high_aligned r hP hB
    have hnon := mul_nonneg hslope.le hx.1
    linarith

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hangle : |x|≤7/10 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hangle,abs_of_nonneg (positive_trig hx).2.2.1]
    ring
  apply original_projection r hs ht hx
  norm_num [Eight.forwardMargin] at hm
  rw [hw] at hm
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.TargetPositive
