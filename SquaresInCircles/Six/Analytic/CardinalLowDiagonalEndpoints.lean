import SquaresInCircles.Six.Analytic.CardinalLowDiagonalConcavity

/-!
# The six sign/order vertices, with visible rational endpoint bounds

The only positive arguments are 1/10,2/5,1/2,9/10: the differences at the
actual rectangle/order vertices. Negative 2/5 is handled by sine/cosine parity.
Every radical bound is obtained by squaring an explicit nonnegative fraction.
No generated box certificate or sampled derivative enters these proofs.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma cardLow_two_fifths_bracket :
    (921:ℝ)/1000≤Real.cos (2/5) ∧ (3894:ℝ)/10000≤Real.sin (2/5) ∧
      Real.sin (2/5)≤3895/10000 := by
  have hc := Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)
  have hl := Seven.sin_lower_seven (x := (2:ℝ)/5) (by norm_num)
  have hu := Seven.sin_upper_five (x := (2:ℝ)/5) (by norm_num)
  norm_num at hc hl hu
  exact ⟨by linarith,by linarith,by linarith⟩

lemma cardLow_nine_tenths_bracket :
    (6215:ℝ)/10000≤Real.cos (9/10) ∧ (7833:ℝ)/10000≤Real.sin (9/10) ∧
      Real.sin (9/10)≤7835/10000 := by
  have hc := Seven.cos_lower_six (x := (9:ℝ)/10) (by norm_num)
  have hl := Seven.sin_lower_seven (x := (9:ℝ)/10) (by norm_num)
  have hu := Seven.sin_upper_five (x := (9:ℝ)/10) (by norm_num)
  norm_num at hc hl hu
  exact ⟨by linarith,by linarith,by linarith⟩

lemma cardLow_tenth_bracket :
    (995:ℝ)/1000≤Real.cos (1/10) ∧ (998:ℝ)/10000≤Real.sin (1/10) ∧
      Real.sin (1/10)≤999/10000 := by
  have hc := Seven.cos_lower_six (x := (1:ℝ)/10) (by norm_num)
  have hl := Seven.sin_lower_seven (x := (1:ℝ)/10) (by norm_num)
  have hu := Seven.sin_upper_five (x := (1:ℝ)/10) (by norm_num)
  norm_num at hc hl hu
  exact ⟨by linarith,by linarith,by linarith⟩

private lemma cardLow_Ws_root_minus :
    -(1689/1000)*(3804/10000)≤sineRoot (1689/1000) (40/100) (25/100) (-2/5) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.sin_neg]
  nlinarith [cardLow_two_fifths_bracket.2.1]

private lemma cardLow_Ws_root_zero :
    -(1689/1000)*(4718/10000)≤sineRoot (1689/1000) (40/100) (25/100) 0 := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num

private lemma cardLow_Ws_root_plus :
    -(1689/1000)*(5482/10000)≤sineRoot (1689/1000) (40/100) (25/100) (2/5) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [cardLow_two_fifths_bracket.2.2]

private lemma cardLow_Ds_root_zero :
    -(1689/1000)*(4037/10000)≤sineRoot (1689/1000) (30/100) (27/100) 0 := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num

private lemma cardLow_Ds_root_half :
    -(1689/1000)*(4906/10000)≤sineRoot (1689/1000) (30/100) (27/100) (1/2) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [low_half_bracket.2.2.2]

private lemma cardLow_Ds_root_two_fifths :
    -(1689/1000)*(4755/10000)≤sineRoot (1689/1000) (30/100) (27/100) (2/5) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [cardLow_two_fifths_bracket.2.2]

private lemma cardLow_relative_root_zero :
    -(1689/1000)*(4302/10000)≤sineRoot (1689/1000) (35/100) (25/100) 0 := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num

private lemma cardLow_relative_root_two_fifths :
    -(1689/1000)*(5033/10000)≤sineRoot (1689/1000) (35/100) (25/100) (2/5) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [cardLow_two_fifths_bracket.2.2]

private lemma cardLow_relative_root_half :
    -(1689/1000)*(5187/10000)≤sineRoot (1689/1000) (35/100) (25/100) (1/2) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [low_half_bracket.2.2.2]

private lemma cardLow_relative_root_nine_tenths :
    -(1689/1000)*(5677/10000)≤sineRoot (1689/1000) (35/100) (25/100) (9/10) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [cardLow_nine_tenths_bracket.2.2]

private lemma cardLow_relative_root_tenth :
    -(1689/1000)*(4501/10000)≤sineRoot (1689/1000) (35/100) (25/100) (1/10) := by
  apply sineRoot_lower_of_squared (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith [cardLow_tenth_bracket.2.2]

/-- The six distinct vertices dictated by w=0 and d=w, for both actual sources. -/
theorem cardLow_vertices (ds : Bool) :
    0<cardLowSmooth ds false (-2/5) 0 ∧
    0<cardLowSmooth ds false (-2/5) (1/2) ∧
    0<cardLowSmooth ds false 0 0 ∧
    0<cardLowSmooth ds false 0 (1/2) ∧
    0<cardLowSmooth ds true (2/5) (2/5) ∧
    0<cardLowSmooth ds true (2/5) (1/2) := by
  obtain ⟨hc4,hs4,hs4u⟩ := cardLow_two_fifths_bracket
  obtain ⟨hc9,hs9,hs9u⟩ := cardLow_nine_tenths_bracket
  obtain ⟨hc1,hs1,hs1u⟩ := cardLow_tenth_bracket
  obtain ⟨hc5,hc5u,hs5,hs5u⟩ := low_half_bracket
  have hwm := cardLow_Ws_root_minus
  have hw0 := cardLow_Ws_root_zero
  have hwp := cardLow_Ws_root_plus
  have hd0 := cardLow_Ds_root_zero
  have hd5 := cardLow_Ds_root_half
  have hd4 := cardLow_Ds_root_two_fifths
  have hr0 := cardLow_relative_root_zero
  have hr4 := cardLow_relative_root_two_fifths
  have hr5 := cardLow_relative_root_half
  have hr9 := cardLow_relative_root_nine_tenths
  have hr1 := cardLow_relative_root_tenth
  cases ds
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals norm_num [cardLowSmooth,cardLowF,cardLowG,cardLowH,cardLowC,
    cardLowAlpha,cardLowBeta,cardLowMu,Real.cos_neg,Real.sin_neg]
  all_goals linarith

/-- Whole-domain positivity, with the geometric order condition retained. -/
theorem cardinal_low_diagonal_positive (ds : Bool) {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d) :
    0<cardLowGap ds w d := by
  obtain ⟨hL0,hLD,h00,h0D,hUU,hUD⟩ := cardLow_vertices ds
  exact cardLow_positive_of_vertices ds hw hd hwd hL0 hLD h00 h0D hUU hUD

end SquaresInCircles.Six.Analytic
