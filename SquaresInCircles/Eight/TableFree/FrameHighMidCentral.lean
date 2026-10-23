module

public import SquaresInCircles.Eight.TableFree.FrameMidHighCentral
public import SquaresInCircles.Eight.TableFree.FrameMidHighVaryingScalars

/-!
# All actual high/middle central witnesses

The two moving multipliers are applied to the actual target arc.  The
opposite-sign family retains both target endpoint supports before and
after the complete quarter-strip contact estimate.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighMidCentral
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport FrameMidHighSupportForms FrameMidHighSupports
open FrameHighMidSupports FrameDiagonalTrigonometry

theorem positive {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (11/10:ℝ) (71/50))
    (hm : 0≤central true true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true true true b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := support (by norm_num : (0:ℝ)≤1/2) hm
    (source_circle_lower false true (1/2) hb) (middle_target_positive hB hx)
  rw [FrameMidHighFixedCalculus.first_formula false true true true (1/2)
    (sourceCircle false true (1/2)) b1 hxq] at hs
  exact (FrameMidHighFixedScalars.hm_positive_lower hx).trans_le hs

theorem varying (i : Bool) {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈FrameMidHighVaryingCalculus.domain i)
    (hm : 0≤central i false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true i false b B x := by
  have hl := FrameMidHighVaryingCalculus.multiplier_bounds hx
  have hs := support
    (show 0≤FrameMidHighVaryingCalculus.lam i x by linarith [hl.1]) hm
    (source_circle_lower false i (FrameMidHighVaryingCalculus.lam i x) hb)
    (varying_target hB hx)
  rw [varying_form i hx] at hs
  exact (FrameMidHighVaryingScalars.lower hx).trans_le hs

theorem plus_minus_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (21/50:ℝ) (61/100))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true true false b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤43/100) hm
    (positive_high_source hb (show (43/100:ℝ)∈Icc (17/50) (43/100) by norm_num))
    (target_circle_lower true false (43/100) x hB)
  rw [positive_constant hxq] at hs
  exact (FrameMidHighConstantScalars.positive_lower hx).trans_le hs

theorem negative_middle {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (3/5:ℝ) (7/10))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false false b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := both_circle hb hB (by norm_num : (0:ℝ)≤21/50) hm
  rw [negative_constant (by norm_num : (0:ℝ)≤21/50) hxq] at hs
  exact (FrameMidHighConstantScalars.negative_middle_lower hx).trans_le hs

theorem negative_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (7/10:ℝ) (93/100))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false false b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := both_circle hb hB (by norm_num : (0:ℝ)≤2/5) hm
  rw [negative_constant (by norm_num : (0:ℝ)≤2/5) hxq] at hs
  exact (FrameMidHighConstantScalars.negative_last_lower hx).trans_le hs

theorem opposite_before {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm
    (source_circle_lower false false (2/5) hb) (middle_target_opposite_endpoints hB)
  by_cases he : target true true (2/5) x b1≤target true true (2/5) x b2
  · rw [min_eq_left he,FrameMidHighFixedCalculus.first_formula false true false true (2/5)
      (sourceCircle false false (2/5)) b1 hxq] at hs
    exact (FrameMidHighFixedScalars.hm_opposite_before_lower false hx).trans_le hs
  · rw [min_eq_right (lt_of_not_ge he).le,
      FrameMidHighFixedCalculus.first_formula false true false true (2/5)
      (sourceCircle false false (2/5)) b2 hxq] at hs
    exact (FrameMidHighFixedScalars.hm_opposite_before_lower true hx).trans_le hs

theorem opposite_after {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc true)
    (hx : x∈Icc (Real.pi/2+1/50) (171/100:ℝ))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false true b B x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := support (by norm_num : (0:ℝ)≤2/5) hm
    (source_circle_lower false false (2/5) hb) (middle_target_opposite_endpoints hB)
  by_cases he : target true true (2/5) x b1≤target true true (2/5) x b2
  · rw [min_eq_left he,FrameMidHighFixedCalculus.second_formula false true false true (2/5)
      (sourceCircle false false (2/5)) b1 hxq] at hs
    exact (FrameMidHighFixedScalars.hm_opposite_after_lower false hx.1).trans_le hs
  · rw [min_eq_right (lt_of_not_ge he).le,
      FrameMidHighFixedCalculus.second_formula false true false true (2/5)
      (sourceCircle false false (2/5)) b2 hxq] at hs
    exact (FrameMidHighFixedScalars.hm_opposite_after_lower true hx.1).trans_le hs

theorem central_lower (i j : Bool) {b B x : ℝ}
    (hb : b∈arc false) (hB : B∈arc true) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true i j b B x := by
  by_cases ht : FrameDiagonalTails.mhTail false i j≤x
  · exact FrameDiagonalTails.high_middle i j hb hB ht
  have hc := FrameDiagonalCuts.central_cut false true i j (Or.inl rfl) hb hB hx hm
  cases i <;> cases j
  · change ¬(93/100:ℝ)≤x at ht
    change (2/5:ℝ)<x at hc
    by_cases h1 : x≤3/5
    · exact varying false hb hB ⟨hc.le,h1⟩ hm
    by_cases h2 : x≤7/10
    · exact negative_middle hb hB ⟨(lt_of_not_ge h1).le,h2⟩ hm
    · exact negative_last hb hB ⟨(lt_of_not_ge h2).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(171/100:ℝ)≤x at ht
    change (13/10:ℝ)<x at hc
    by_cases h1 : x≤Real.pi/2-1/50
    · exact opposite_before hb hB ⟨hc.le,h1⟩ hm
    by_cases h2 : x≤Real.pi/2+1/50
    · exact FrameMidHighQuarterStrip.high_middle hb hB ⟨(lt_of_not_ge h1).le,h2⟩ hm
    · exact opposite_after hb hB ⟨(lt_of_not_ge h2).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(61/100:ℝ)≤x at ht
    change (1/10:ℝ)<x at hc
    by_cases h : x≤21/50
    · exact varying true hb hB ⟨hc.le,h⟩ hm
    · exact plus_minus_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(71/50:ℝ)≤x at ht
    change (11/10:ℝ)<x at hc
    exact positive hb hB ⟨hc.le,(lt_of_not_ge ht).le⟩ hm

end SquaresInCircles.Eight.TableFree.FrameHighMidCentral
