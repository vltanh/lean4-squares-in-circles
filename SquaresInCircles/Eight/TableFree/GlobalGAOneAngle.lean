module

public import SquaresInCircles.Eight.TableFree.GlobalGAOneAngleEndpoints

/-!
# Full-variation one-angle support at the original H and G points

Uncompiled source.  These are the concrete one-angle invocations used by
the secondary-owner four-circle stress.  Positive errors use the full
circle; negative errors use short-arc concavity followed by the proved
axial-support transition.  The point and its original radius are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary

theorem actual_H_one {r x : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hx : |x|≤frameCap) :
    0≤oneIncrement k 1 x P := by
  by_cases hxp : 0≤x
  · apply positive_one_nonneg (by norm_num [k]) (by norm_num [k])
      (by norm_num [k]) hy hc hr
      ⟨hxp,by simpa [abs_of_nonneg hxp] using hx⟩
    linarith [H_corners.1]
  · let w := -x
    have hw : w∈Icc 0 frameCap := by
      dsimp [w]
      constructor
      · linarith
      · simpa [abs_of_neg (lt_of_not_ge hxp)] using hx
    have hxw : x = -w := by dsimp [w]; ring
    by_cases hshort : w≤3/5
    · have hnonneg := negative_full_short_nonneg (p:=k) (q:=1)
        (by norm_num [k]) (by norm_num [k]) (by norm_num [k])
        (show (3/5:ℝ)≤frameCap by norm_num [frameCap]) ⟨hw.1,hshort⟩
        (by linarith [H_short_endpoint])
      have hsupport := one_full_lower (p:=k) (q:=1) hy hc hr hx
      rw [hxw,negative_full_identity hw] at hsupport
      exact hnonneg.trans hsupport
    · have hstart : (3/5:ℝ)≤w := le_of_lt (lt_of_not_ge hshort)
      have htest := axialTest_monotone (p:=k) (q:=1) (by norm_num)
        (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hw hstart
      have haxis := one_axial_lower (p:=k) (q:=1) (by norm_num) hy hc hr hw
        (H_axial_start.le.trans htest)
      have hend := H_axial_antitone hw
        (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hw.2
      have hnonneg : 0≤axialOne k 1 w := by
        linarith [H_axial_endpoint]
      rw [hxw]
      exact hnonneg.trans haxis

theorem actual_G_one {r x : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hx : |x|≤frameCap) :
    0≤oneIncrement k l x P := by
  by_cases hxp : 0≤x
  · apply positive_one_nonneg (by norm_num [k]) (by norm_num [k,l])
      (by norm_num [k,l]) hy hc hr
      ⟨hxp,by simpa [abs_of_nonneg hxp] using hx⟩
    linarith [G_corners.1]
  · let w := -x
    have hw : w∈Icc 0 frameCap := by
      dsimp [w]
      constructor
      · linarith
      · simpa [abs_of_neg (lt_of_not_ge hxp)] using hx
    have hxw : x = -w := by dsimp [w]; ring
    by_cases hshort : w≤3/10
    · have hnonneg := negative_full_short_nonneg (p:=k) (q:=l)
        (by norm_num [k]) (by norm_num [k,l]) (by norm_num [k,l])
        (show (3/10:ℝ)≤frameCap by norm_num [frameCap]) ⟨hw.1,hshort⟩
        (by linarith [G_short_endpoint])
      have hsupport := one_full_lower (p:=k) (q:=l) hy hc hr hx
      rw [hxw,negative_full_identity hw] at hsupport
      exact hnonneg.trans hsupport
    · have hstart : (3/10:ℝ)≤w := le_of_lt (lt_of_not_ge hshort)
      have htest := axialTest_monotone (p:=k) (q:=l) (by norm_num [l])
        (show (3/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hw hstart
      have haxis := one_axial_lower (p:=k) (q:=l) (by norm_num [l]) hy hc hr hw
        (G_axial_start.le.trans htest)
      have hinc := G_axial_monotone
        (show (3/10:ℝ)∈Icc (3/10) frameCap by norm_num [frameCap])
        ⟨hstart,hw.2⟩ hstart
      have hnonneg : 0≤axialOne k l w := by linarith [G_axial_endpoint]
      rw [hxw]
      exact hnonneg.trans haxis

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
