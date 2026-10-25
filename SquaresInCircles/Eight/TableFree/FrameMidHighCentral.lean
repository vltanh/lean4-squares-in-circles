module

public import SquaresInCircles.Eight.TableFree.FrameMidHighSupportForms
public import SquaresInCircles.Eight.TableFree.FrameMidHighQuarterStrip
public import SquaresInCircles.Eight.TableFree.FrameDiagonalTails

/-!
# All actual middle/high central witnesses

The source and target are the original circle points.  The initial
barriers, exact supports, quarter-strip contact, and complete angular
tails cover every nonnegative folded angle and every tangent sign.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighCentral
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport FrameMidHighSupportForms FrameMidHighSupports
open FrameDiagonalTrigonometry

theorem positive {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (7/10:ℝ) (93/100))
    (hm : 0≤central true true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤7/20) hm (positive_source hb)
    (target_circle_lower false true (7/20) x hB)
  rw [high_target_first true true (Or.inl rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.positive_lower hx).trans_le hs

theorem plus_minus {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (1/10:ℝ) (61/100))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤11/20) hm
    (source_circle_lower true true (11/20) hb)
    (high_target_early hB ⟨by linarith [hx.1],hx.2⟩)
  rw [FrameMidHighFixedCalculus.first_formula true false true false (11/20)
    (sourceCircle true true (11/20)) b1 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_plus_minus_lower hx).trans_le hs

theorem negative_first {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (9/10:ℝ) (6/5))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (high_target_negative hB hx)
  rw [FrameMidHighFixedCalculus.first_formula true false false false (2/5)
    (source true false (2/5) b1) b1 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_negative_lower hx.1).trans_le hs

theorem negative_last {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (6/5:ℝ) (71/50))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false false b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false false (2/5) x hB)
  rw [high_target_first false false (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.negative_lower hx).trans_le hs

theorem opposite_first {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (6/5:ℝ) (13/10))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (high_target_opposite hB ⟨by linarith [hx.1],hx.2⟩)
  rw [FrameMidHighFixedCalculus.first_formula true false false true (2/5)
    (source true false (2/5) b1) 0 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_opposite_lower hx).trans_le hs

theorem opposite_before {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false true (2/5) x hB)
  rw [high_target_first false true (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.opposite_before_lower hx).trans_le hs

theorem opposite_after {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (Real.pi/2+1/50) (171/100:ℝ))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false true (2/5) x hB)
  rw [high_target_second false true (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.opposite_after_lower hx).trans_le hs

theorem central_lower (i j : Bool) {b B x : ℝ}
    (hb : b∈arc true) (hB : B∈arc false) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  by_cases ht : FrameDiagonalTails.mhTail true i j≤x
  · exact FrameDiagonalTails.middle_high i j hb hB ht
  have hc := FrameDiagonalCuts.central_cut true false i j (Or.inr rfl) hb hB hx hm
  cases i <;> cases j
  · change ¬(71/50:ℝ)≤x at ht
    change (9/10:ℝ)<x at hc
    by_cases h : x≤6/5
    · exact negative_first hb hB ⟨hc.le,h⟩ hm
    · exact negative_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(171/100:ℝ)≤x at ht
    change (6/5:ℝ)<x at hc
    by_cases h1 : x≤13/10
    · exact opposite_first hb hB ⟨hc.le,h1⟩ hm
    by_cases h2 : x≤Real.pi/2-1/50
    · exact opposite_before hb hB ⟨(lt_of_not_ge h1).le,h2⟩ hm
    by_cases h3 : x≤Real.pi/2+1/50
    · exact FrameMidHighQuarterStrip.middle_high hb hB ⟨(lt_of_not_ge h2).le,h3⟩ hm
    · exact opposite_after hb hB ⟨(lt_of_not_ge h3).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(61/100:ℝ)≤x at ht
    change (1/10:ℝ)<x at hc
    exact plus_minus hb hB ⟨hc.le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(93/100:ℝ)≤x at ht
    change (7/10:ℝ)<x at hc
    exact positive hb hB ⟨hc.le,(lt_of_not_ge ht).le⟩ hm

end SquaresInCircles.Eight.TableFree.FrameMidHighCentral
