module

public import SquaresInCircles.Eight.TableFree.WrongWordCircleSupport
public import SquaresInCircles.Eight.TableFree.WrongWordCore

/-!
# Six opposite-sign mixed zero-quarter families, positive angles

These are the six exact role functions in section 3 of
`HAND_SHORT_WORD_MIXED_ZERO_COMPLETE_WITHOUT_TABLES`. Each family uses
one constant separating multiplier on its entire positive angle half.
Four families use intrinsic circle-support events; the other two use
the actual arc endpoints directly. Every source lies on its original
complete core side or corner. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry
open WrongWordCircleSupport

abbrev Row := Fin 6

def c : Row → ℝ := ![14041/100000,-21286/100000,-5550/100000,
  28271/100000,-72700/100000,27632/100000]
def p : Row → ℝ := ![0,-13422/100000,0,9133/100000,-51554/100000,19335/100000]
def q : Row → ℝ := ![94766/100000,103828/100000,99940/100000,
  88074/100000,119909/100000,76744/100000]
def g : Row → ℝ := ![62095/100000,108816/100000,113855/100000,
  62095/100000,104073/100000,104729/100000]
def multiplier (r : Row) : ℝ := if r=0 then q r else if r=3 then 93/100 else g r
def intercept (r : Row) : ℝ := c r+(g r-multiplier r)*CoreAngleEndpoint.diagonal
def axialLoss (r : Row) : ℝ := if r=0 ∨ r=3 then 0 else 19/100

lemma coefficient_bounds (r : Row) :
    0<g r ∧ 0< multiplier r ∧ g r≤ multiplier r ∧
      multiplier r≤1139/1000 ∧ 0<q r := by
  fin_cases r <;> norm_num [c,p,q,g,multiplier]

lemma norm_rows (r : Row) (h0 : r≠0) (h4 : r≠4) :
    (p r)^2+(q r)^2<(multiplier r)^2 := by
  fin_cases r
  · exact absurd rfl h0
  · norm_num [p,q,g,multiplier]
  · norm_num [p,q,g,multiplier]
  · norm_num [p,q,g,multiplier]
  · exact absurd rfl h4
  · norm_num [p,q,g,multiplier]

lemma fine_diagonal_bounds :
    (449607/500000:ℝ)<outerDiagonal ∧ outerDiagonal<8992141/10000000 := by
  have he := diagonal_circle
  have hn : 0<outerDiagonal := by linarith [outer_endpoint_bounds.2.2.1]
  norm_num [Q0] at he
  constructor <;> nlinarith

def axialD (r : Row) (x : ℝ) : ℝ :=
  1-multiplier r*(Real.sin x/2+(outerAxial-1/2)*Real.cos x)
def diagonalD (r : Row) (x : ℝ) : ℝ :=
  1-multiplier r*(outerDiagonal-1/2)*(Real.cos x-Real.sin x)

lemma axial_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (axial (intercept r) (p r) (q r) (multiplier r)) (axialD r x) x := by
  have h1 := ((hasDerivAt_const x (1:ℝ)).fun_add (Real.hasDerivAt_sin x)).fun_add
    (Real.hasDerivAt_cos x)
  have hb := ((hasDerivAt_id' (x := x)).add_const (intercept r)).fun_add
    ((h1.const_mul (multiplier r)).div_const 2)
  have hX := ((Real.hasDerivAt_sin x).const_mul (multiplier r)).const_sub (-p r)
  refine (hb.fun_add (hX.mul_const outerAxial)).congr_deriv ?_
  simp only [axialD]
  ring

lemma diagonal_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (diagonal (intercept r) (p r) (q r) (multiplier r)) (diagonalD r x) x := by
  have h1 := ((hasDerivAt_const x (1:ℝ)).fun_add (Real.hasDerivAt_sin x)).fun_add
    (Real.hasDerivAt_cos x)
  have hb := ((hasDerivAt_id' (x := x)).add_const (intercept r)).fun_add
    ((h1.const_mul (multiplier r)).div_const 2)
  have hX := ((Real.hasDerivAt_sin x).const_mul (multiplier r)).const_sub (-p r)
  have hY := ((Real.hasDerivAt_cos x).const_mul (multiplier r)).const_sub (q r)
  refine (hb.fun_add ((hX.fun_add hY).mul_const outerDiagonal)).congr_deriv ?_
  simp only [diagonalD]
  ring

lemma axial_projection_bound (x : ℝ) :
    Real.sin x/2+(outerAxial-1/2)*Real.cos x<(1043/1000:ℝ) := by
  let v := Real.sin x/2+(outerAxial-1/2)*Real.cos x
  have he : v^2+(Real.cos x/2-(outerAxial-1/2)*Real.sin x)^2=
      1/4+(outerAxial-1/2)^2 := by
    dsimp [v]
    linear_combination ((1/4:ℝ)+(outerAxial-1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hs := sq_nonneg (Real.cos x/2-(outerAxial-1/2)*Real.sin x)
  have ha := outer_endpoint_bounds
  change v<(1043/1000:ℝ)
  nlinarith [ha.1,ha.2.1]

lemma axial_derivative_lower (r : Row) (x : ℝ) : 0≤axialD r x+axialLoss r := by
  have hl := (coefficient_bounds r).2.1
  have hh := mul_lt_mul_of_pos_left (axial_projection_bound x) hl
  by_cases he : r=0 ∨ r=3
  · have hsmall : multiplier r≤237/250 := by
      rcases he with rfl | rfl <;> norm_num [multiplier,q,g]
    simp only [axialD,axialLoss,if_pos he]
    nlinarith
  · have hlarge := (coefficient_bounds r).2.2.2.1
    simp only [axialD,axialLoss,if_neg he]
    nlinarith

lemma axial_initial (r : Row) :
    (449/500:ℝ)+(7/10)*axialLoss r<
      axial (intercept r) (p r) (q r) (multiplier r) 0 := by
  have ha := outer_endpoint_bounds
  have hd := CoreAngleEndpoint.diagonal_bounds
  fin_cases r <;>
    norm_num [axial,base,X,intercept,c,p,q,g,multiplier,axialLoss] <;>
    nlinarith [ha.1,ha.2.1,hd.1,hd.2]

lemma axial_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (449/500:ℝ)<axial (intercept r) (p r) (q r) (multiplier r) x := by
  have hd (z : ℝ) : HasDerivAt
      (fun z => axial (intercept r) (p r) (q r) (multiplier r) z+axialLoss r*z)
      (axialD r z+axialLoss r) z :=
    ((axial_hasDerivAt r z).fun_add
      ((hasDerivAt_id' (x := z)).const_mul (axialLoss r))).congr_deriv (by ring)
  have hm : MonotoneOn
      (fun z => axial (intercept r) (p r) (q r) (multiplier r) z+axialLoss r*z)
      (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z _ => hd z) (fun z _ => axial_derivative_lower r z)
  have hh := hm (by norm_num) hx hx.1
  have hl : 0≤axialLoss r := by unfold axialLoss; split_ifs <;> norm_num
  have hp := mul_le_mul_of_nonneg_left hx.2 hl
  dsimp only at hh
  linarith [axial_initial r]

lemma diagonal_derivative_pos (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<diagonalD r x := by
  have ht := positive_trig hx
  have hb := coefficient_bounds r
  have hd := outer_endpoint_bounds
  have hm : 0≤ multiplier r*(outerDiagonal-1/2) := by
    exact mul_nonneg hb.2.1.le (by linarith [hd.2.2.1])
  have hp := mul_le_mul_of_nonneg_left
    (show Real.cos x-Real.sin x≤1 by linarith [ht.2.1,ht.2.2.1]) hm
  have hU := mul_lt_mul_of_pos_left (show outerDiagonal-1/2<(2/5:ℝ) by
    linarith [hd.2.2.2]) hb.2.1
  dsimp [diagonalD]
  nlinarith [hb.2.2.2.1]

lemma diagonal_initial (r : Row) :
    (449/500:ℝ)<diagonal (intercept r) (p r) (q r) (multiplier r) 0 := by
  have hd := fine_diagonal_bounds
  have hc := CoreAngleEndpoint.diagonal_bounds
  fin_cases r <;>
    norm_num [WrongWordCircleSupport.diagonal,base,X,Y,intercept,c,p,q,g,multiplier] <;>
    linarith [hd.1,hd.2,hc.1,hc.2]

lemma diagonal_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (449/500:ℝ)<diagonal (intercept r) (p r) (q r) (multiplier r) x := by
  have hm : MonotoneOn (diagonal (intercept r) (p r) (q r) (multiplier r))
      (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (diagonal_hasDerivAt r z).continuousAt.continuousWithinAt
    · exact fun z _ => diagonal_hasDerivAt r z
    · exact fun z hz => (diagonal_derivative_pos r (Ioo_subset_Icc_self hz)).le
  exact (diagonal_initial r).trans_le (hm (by norm_num) hx hx.1)

lemma right_axial_slope (r : Row) : 0≤axialSlope (p r) (q r) (multiplier r) (7/10) := by
  have ha := outer_endpoint_bounds
  have hb := coefficient_bounds r
  have ht := cap_trig
  have hu : 0<outerAxial+1/2 := by linarith [ha.1]
  have huL : (1914/1000:ℝ)<outerAxial+1/2 := by
    have h : (1914/1000:ℝ)<Real.sqrt (Q0-1/4) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num [Q0]
    unfold outerAxial
    linarith
  have huU : outerAxial+1/2<(1915/1000:ℝ) := by linarith [ha.2.1]
  have hcos : (outerAxial+1/2)*Real.cos (7/10:ℝ)<
      (1915/1000)*(191211/250000) := by
    exact (mul_lt_mul_of_pos_left ht.2.2.2 hu).trans
      (mul_lt_mul_of_pos_right huU (by norm_num))
  have hq := mul_lt_mul_of_pos_right huL hb.2.2.2.2
  have hc := mul_lt_mul_of_pos_left hcos hb.2.1
  have hs := mul_lt_mul_of_pos_left ht.1 hb.2.1
  have hlo : (1914/1000)*q r-(1915/1000)*(191211/250000)*multiplier r+
      p r/2+(3221/5000)*multiplier r/2<
        axialSlope (p r) (q r) (multiplier r) (7/10) := by
    dsimp [axialSlope,X,Y]
    linarith
  refine le_trans ?_ hlo.le
  fin_cases r <;> norm_num [p,q,g,multiplier]

lemma third_full_initial :
    (449/500:ℝ)<full (intercept 3) (p 3) (q 3) (multiplier 3) 0 := by
  have hl := (coefficient_bounds 3).2.1
  have hpq := norm_rows 3 (by decide) (by decide)
  have hn := N_sq (x := (0:ℝ)) hl hpq
  have hnU : N (p 3) (q 3) (multiplier 3) 0<(13/125:ℝ) := by
    have h2 : (N (p 3) (q 3) (multiplier 3) 0)^2<(13/125)^2 := by
      rw [hn]
      norm_num [X,Y,p,q,g,multiplier]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h2
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hRN := (mul_lt_mul_of_pos_left hnU hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<13/125))
  rw [full_expression]
  have hd := CoreAngleEndpoint.diagonal_bounds
  norm_num [intercept,c,p,q,g,multiplier] at hRN ⊢
  linarith [hd.1,hd.2]

lemma left_support_event (r : Row) (h0 : r≠0) (h4 : r≠4) :
    diagonalSlope (p r) (q r) (multiplier r) 0≤0 ∨
      (449/500:ℝ)<full (intercept r) (p r) (q r) (multiplier r) 0 := by
  fin_cases r
  · exact (h0 rfl).elim
  · left; norm_num [diagonalSlope,X,Y,p,q,g,multiplier]
  · left; norm_num [diagonalSlope,X,Y,p,q,g,multiplier]
  · exact Or.inr third_full_initial
  · exact (h4 rfl).elim
  · left; norm_num [diagonalSlope,X,Y,p,q,g,multiplier]

lemma positive_support (r : Row) {A B x : ℝ} (hc : OuterState A B)
    (hx : x∈Icc 0 (7/10)) :
    (449/500:ℝ)<base (intercept r) (multiplier r) x+
      X (p r) (multiplier r) x*A+Y (q r) (multiplier r) x*B := by
  by_cases he : r=0 ∨ r=4
  · have hY : 0≤Y (q r) (multiplier r) x := by
      have hm0 := (coefficient_bounds r).2.1.le
      have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hm0
      have hqm : multiplier r≤q r := by
        rcases he with rfl | rfl <;> norm_num [q,g,multiplier]
      unfold Y
      linarith
    have hs := outer_endpoints_lower (X := X (p r) (multiplier r) x)
      (Y := Y (q r) (multiplier r) x)
      (m := min (X (p r) (multiplier r) x*outerAxial)
        ((X (p r) (multiplier r) x+Y (q r) (multiplier r) x)*outerDiagonal))
      hc hY (min_le_left _ _) (min_le_right _ _)
    have hm : (449/500:ℝ)<base (intercept r) (multiplier r) x+
        min (X (p r) (multiplier r) x*outerAxial)
          ((X (p r) (multiplier r) x+Y (q r) (multiplier r) x)*outerDiagonal) := by
      rw [add_min]
      exact lt_min (axial_lower r hx) (diagonal_lower r hx)
    linarith
  · have h0 : r≠0 := fun h => he (Or.inl h)
    have h4 : r≠4 := fun h => he (Or.inr h)
    exact actual_arc_lower hc (coefficient_bounds r).2.1 (norm_rows r h0 h4) hx
      (fun z hz => axial_lower r hz) (fun z hz => diagonal_lower r hz)
      (left_support_event r h0 h4) (right_axial_slope r)

/-- All six original core-source opposite-sign secondary families on
their complete nonnegative angle half. The labels stay on both original
states; the core coordinate is only bounded in the separating estimate. -/
theorem opposite_core_positive (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r+g r*b-p r*A+q r*B := by
  have hh := positive_support r ht hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have hc := coefficient_bounds r
  have hcore := mul_nonneg_of_nonpos_of_nonpos
    (show g r-multiplier r≤0 by linarith [hc.2.2.1])
    (show b-CoreAngleEndpoint.diagonal≤0 by linarith)
  have hsep := mul_nonneg hc.2.1.le (sub_nonneg.mpr hm)
  dsimp [base,intercept,X,Y] at hh
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortMixedZero
