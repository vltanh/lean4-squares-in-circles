module

public import SquaresInCircles.Eight.TableFree.SecondOuterLabelCalculus

/-!
# Adjacent Taylor supports at the physical angle cap

The degree-eleven and degree-twelve bounds follow by integration from
the existing degree-ten support.  The single cap reference is then a
rational substitution in these whole-half-line inequalities.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.ReferenceTrig

open Arithmetic

def sin11 (x : ℝ) : ℝ := sin9 x-x^11/39916800
def cos12 (x : ℝ) : ℝ := cos10 x+x^12/479001600

lemma sin11_le_sin {x : ℝ} (hx : 0≤x) : sin11 x≤Real.sin x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.sin t-sin11 t)
    (by dsimp [sin11,sin9,sin7]; fun_prop)
    (by norm_num [sin11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [sin11,sin9,sin7]
      have hc := cos10_le_cos ht
      dsimp [cos10,cos8] at hc
      linarith) hx
  linarith

lemma cos_le_cos12 {x : ℝ} (hx : 0≤x) : Real.cos x≤cos12 x := by
  have hh := nonneg_of_deriv_nonneg (fun t => cos12 t-Real.cos t)
    (by dsimp [cos12,cos10,cos8]; fun_prop)
    (by norm_num [cos12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [cos12,cos10,cos8]
      have hs := sin11_le_sin ht
      dsimp [sin11,sin9,sin7] at hs
      linarith) hx
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.ReferenceTrig

namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.FiveSame

open Arithmetic SecondWord.ReferenceTrig

lemma cap_fine :
    (1610544218/2500000000:ℝ)<Real.sin (7/10) ∧
      Real.sin (7/10)<644217688/1000000000 ∧
      (956052734/1250000000:ℝ)<Real.cos (7/10) ∧
      Real.cos (7/10)<7648421873/10000000000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.TableFree.ShortOuterOne.FiveSame
