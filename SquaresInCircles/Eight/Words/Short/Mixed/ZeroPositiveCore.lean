module

public import SquaresInCircles.Eight.Words.Wrong.WordCircleSupport

/-!
# Eight squares: positive core source and positive outer target on a zero edge

The original owner forces the angle above `.4`. For three role families
an exact rotating-vector norm has a uniform speed bound, so the original
circle support loses less than `.081` after its initial value above `.98`.
The last family uses the actual axial support and its derivative bound.
-/

section
/-!
## Six opposite-sign mixed zero-quarter families, positive angles

The six exact role functions have the coefficients `c`, `p`, `q` and `g`. Each family uses one
constant separating multiplier (`multiplier`) on its whole positive angle half. Four families use
intrinsic circle-support events (`left_support_event`, `positive_support`); the other two use the
arc endpoints directly. Every source lies on its original core side or corner
(`opposite_core_positive`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

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
    simp only [axialD,axialLoss,ite_eq_left he]
    nlinarith
  · have hlarge := (coefficient_bounds r).2.2.2.1
    simp only [axialD,axialLoss,ite_eq_right he]
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
their whole nonnegative angle half. The labels stay on both original
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

end SquaresInCircles.Eight.ShortMixedZero
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.PositiveCore

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-2953/100000,12783/100000,46969/100000,-2145/100000]
def p : Row → ℝ := ![0,13422/100000,33147/100000,0]
def q : Row → ℝ := ![99940/100000,103828/100000,113360/100000,71553/100000]
def g : Row → ℝ := ![108816/100000,113855/100000,104073/100000,104729/100000]
def rate : Row → ℝ := ![1,1047/1000,104073/100000,104729/100000]
def ceiling : Row → ℝ := ![53/125,289/500,379/500,1]

lemma coefficients (r : Row) : 0≤p r ∧ 0<q r ∧ 0<g r ∧ 0<rate r ∧
    (rate r=g r ∨ (p r)^2+(q r)^2≤(rate r)^2) := by
  fin_cases r <;> norm_num [p,q,g,rate]

lemma initial_trig : (194709/500000:ℝ)<Real.sin (2/5:ℝ) ∧
    Real.sin (2/5:ℝ)<389419/1000000 ∧ (46053/50000:ℝ)<Real.cos (2/5:ℝ) := by
  have hs := sin_lower_seven (x := (2/5:ℝ)) (by norm_num)
  have hu := sin_upper_five (x := (2/5:ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (2/5:ℝ)) (by norm_num)
  norm_num at hs hu hc
  exact ⟨by linarith,by linarith,by linarith⟩

lemma angle_trig {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (389/1000:ℝ)<Real.sin x ∧ (191/250:ℝ)<Real.cos x := by
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
    ⟨by linarith [hx.1],hx.2⟩ hx.1
  exact ⟨by linarith [initial_trig.1],by
    linarith [(positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)).1]⟩

/-- The positivity half of `CommonQuarter.zero_positive_secondary_angle` (not imported here):
the original weak separator forces a positive angle. -/
private lemma zero_positive_angle_pos {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : 0<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  by_contra! hn
  have hsin : Real.sin φ≤0 := by
    have hp := positive_trig (x := -φ) ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht'.1]) hsin
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  norm_num [forwardMargin] at hm
  nlinarith [hs'.2.2.2.2]

lemma original_angle {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : (2/5:ℝ)<φ := by
  have hs' : State .coreSide a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_angle_pos hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have hA := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have hB := mul_nonneg ht.1 (by linarith [tr.1] : 0≤Real.cos φ)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  by_contra! hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hsine := Real.sin_le hx.1
  have hs2 := pow_le_pow_left₀ hx.1 hn 2
  have hprim := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  nlinarith [CoreAngleEndpoint.diagonal_bounds.2]

def N (r : Row) (x : ℝ) : ℝ := WrongWordCircleSupport.N (p r) (q r) (g r) x
def Nd (r : Row) (x : ℝ) : ℝ := g r*(p r*Real.cos x+q r*Real.sin x)/N r x
def F (r : Row) (x : ℝ) : ℝ := x+c r+(g r+p r+q r)/2+g r*Real.sin x-CommonQuarter.radius*N r x
def Fd (r : Row) (x : ℝ) : ℝ := 1+g r*Real.cos x-CommonQuarter.radius*Nd r x

lemma norm_energy_pos (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    0<CircularNorm.energy (WrongWordCircleSupport.mass (p r) (q r) (g r))
      (-2*g r*q r) (2*g r*p r) x := by
  rw [WrongWordCircleSupport.energy_eq]
  have hc := coefficients r
  have hs := mul_pos hc.2.2.1 (show 0<Real.sin x by linarith [(angle_trig hx).1])
  have hX : WrongWordCircleSupport.X (p r) (g r) x<0 := by
    dsimp [WrongWordCircleSupport.X]
    linarith [hc.1]
  nlinarith [sq_nonneg (WrongWordCircleSupport.Y (q r) (g r) x)]

lemma N_pos (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : 0<N r x :=
  CircularNorm.norm_pos (norm_energy_pos r hx)

lemma N_sq (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (N r x)^2=(p r)^2+(q r)^2+(g r)^2+
      2*g r*(p r*Real.sin x-q r*Real.cos x) := by
  have hh := CircularNorm.norm_sq (norm_energy_pos r hx).le
  change (N r x)^2=_ at hh
  dsimp [CircularNorm.energy,WrongWordCircleSupport.mass] at hh
  nlinarith only [hh]

lemma N_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    HasDerivAt (N r) (Nd r x) x := by
  have hh := CircularNorm.norm_hasDerivAt (norm_energy_pos r hx)
  convert hh using 1
  · rfl
  · dsimp [Nd,CircularNorm.d1,CircularNorm.slope,N,WrongWordCircleSupport.N]
    ring

/-- The two squared identities give both rotating-vector speed bounds.
The exact role chooses the smaller useful bound without approximation
of the norm or division by a merely assumed positive quantity. -/
lemma Nd_le_rate (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : Nd r x≤rate r := by
  let s := p r*Real.sin x-q r*Real.cos x
  let t := p r*Real.cos x+q r*Real.sin x
  have hpj : t^2+s^2=(p r)^2+(q r)^2 := by
    dsimp [s,t]
    linear_combination ((p r)^2+(q r)^2)*(Real.sin_sq_add_cos_sq x)
  have hn := N_sq r hx
  change (N r x)^2=(p r)^2+(q r)^2+(g r)^2+2*g r*s at hn
  have hsq : (g r*t)^2≤(rate r*N r x)^2 := by
    rcases (coefficients r).2.2.2.2 with he | he
    · rw [he]
      have hid : (g r*t)^2+(g r*(g r+s))^2=(g r*N r x)^2 := by
        linear_combination (g r)^2*hpj-(g r)^2*hn
      nlinarith only [hid,sq_nonneg (g r*(g r+s))]
    · have hid : (g r*t)^2+((p r)^2+(q r)^2+g r*s)^2=
          ((p r)^2+(q r)^2)*(N r x)^2 := by
        linear_combination (g r)^2*hpj-((p r)^2+(q r)^2)*hn
      have hcoef := mul_le_mul_of_nonneg_right he (sq_nonneg (N r x))
      nlinarith only [hid,hcoef,sq_nonneg ((p r)^2+(q r)^2+g r*s)]
  have hprod := mul_pos (coefficients r).2.2.2.1 (N_pos r hx)
  have hle : g r*t≤rate r*N r x := by
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad)
      (show 0<g r*t+rate r*N r x by linarith)
    nlinarith only [hsq,hh]
  exact (div_le_iff₀ (N_pos r hx)).2 hle

lemma F_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    HasDerivAt (F r) (Fd r x) x :=
  ((((hasDerivAt_id' x).add_const (c r)).add_const ((g r+p r+q r)/2)).add
    ((Real.hasDerivAt_sin x).const_mul (g r))).sub ((N_hasDerivAt r hx).const_mul CommonQuarter.radius)

lemma Fd_lower (r : Row) (h3 : r≠3) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -(27/100:ℝ)<Fd r x := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hn := mul_le_mul_of_nonneg_left (Nd_le_rate r hx) hR.le
  have hRu := mul_lt_mul_of_pos_right radius_bounds.2 (coefficients r).2.2.2.1
  have hc := mul_lt_mul_of_pos_left (angle_trig hx).2 (coefficients r).2.2.1
  dsimp [Fd]
  fin_cases r
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · norm_num [g,rate] at hn hRu hc ⊢; linarith
  · exact absurd rfl h3

lemma N_initial_upper (r : Row) : N r (2/5)<ceiling r := by
  have hx : (2/5:ℝ)∈Icc (2/5) (7/10) := by norm_num
  have hn := N_sq r hx
  have hp := N_pos r hx
  have hc := coefficients r
  have hs := mul_le_mul_of_nonneg_left initial_trig.2.1.le
    (mul_nonneg (by linarith [hc.2.2.1] : 0≤2*g r) hc.1)
  have hk := mul_le_mul_of_nonneg_left initial_trig.2.2.le
    (mul_nonneg (by linarith [hc.2.2.1] : 0≤2*g r) hc.2.1.le)
  fin_cases r <;> norm_num [p,q,g,ceiling] at hn hs hk ⊢ <;> nlinarith

lemma F_initial (r : Row) (h3 : r≠3) : (49/50:ℝ)<F r (2/5) := by
  have hn := mul_lt_mul_of_pos_left (N_initial_upper r)
    (show 0<CommonQuarter.radius by linarith [radius_bounds.1])
  have hceiling : 0<ceiling r := by fin_cases r <;> norm_num [ceiling]
  have hR := mul_lt_mul_of_pos_right radius_bounds.2 hceiling
  have hs := mul_lt_mul_of_pos_left initial_trig.1 (coefficients r).2.2.1
  dsimp [F]
  fin_cases r
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · norm_num [c,p,q,g,ceiling] at hn hR hs ⊢; linarith
  · exact absurd rfl h3

lemma F_lower (r : Row) (h3 : r≠3) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (449/500:ℝ)<F r x := by
  let f : ℝ → ℝ := fun z => F r z+(27/100)*z
  have hd {z : ℝ} (hz : z∈Icc (2/5) (7/10)) :
      HasDerivAt f (Fd r z+27/100) z := by
    have h : HasDerivAt (fun y => F r y+(27/100)*y) (Fd r z+27/100*1) z :=
      (F_hasDerivAt r hz).add ((hasDerivAt_id' z).const_mul (27/100))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn f (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z hz => (hd hz).continuousAt.continuousWithinAt)
      (fun z hz => hd (Ioo_subset_Icc_self hz))
      (fun z hz => by linarith [Fd_lower r h3 (Ioo_subset_Icc_self hz)])
  have hh := hm (by norm_num) hx hx.1
  dsimp [f] at hh
  linarith [F_initial r h3,hx.2]

def axial (x : ℝ) : ℝ := x+c 3+g 3/2+(g 3/2)*Real.cos x-
  g 3*(outerAxial-1/2)*Real.sin x
def axialD (x : ℝ) : ℝ := 1-g 3*(Real.sin x/2+(outerAxial-1/2)*Real.cos x)

lemma axial_hasDerivAt (x : ℝ) : HasDerivAt axial (axialD x) x := by
  have hh : HasDerivAt (fun y => y+c 3+g 3/2+(g 3/2)*Real.cos y-
      g 3*(outerAxial-1/2)*Real.sin y)
      (1+(g 3/2)*(-Real.sin x)-g 3*(outerAxial-1/2)*Real.cos x) x :=
    ((((hasDerivAt_id' x).add_const (c 3)).add_const (g 3/2)).add
      ((Real.hasDerivAt_cos x).const_mul (g 3/2))).sub
        ((Real.hasDerivAt_sin x).const_mul (g 3*(outerAxial-1/2)))
  exact hh.congr_deriv (by dsimp [axialD]; ring)

lemma axialD_lower (x : ℝ) : -(1/10:ℝ)<axialD x := by
  have hp := mul_lt_mul_of_pos_left (axial_projection_bound x) (coefficients 3).2.2.1
  norm_num [axialD,g] at hp ⊢
  linarith

lemma axial_initial : (101/100:ℝ)<axial (2/5) := by
  have hs := mul_le_mul_of_nonneg_left initial_trig.2.1.le
    (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1])
  have hu := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le
    (show (0:ℝ)≤389419/1000000 by norm_num)
  norm_num [axial,c,g]
  nlinarith [initial_trig.2.2]

lemma axial_lower {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : (449/500:ℝ)<axial x := by
  let f : ℝ → ℝ := fun z => axial z+z/10
  have hd (z : ℝ) : HasDerivAt f (axialD z+1/10) z :=
    (axial_hasDerivAt z).add ((hasDerivAt_id z).div_const 10)
  have hm : MonotoneOn f (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z _ => hd z) (fun z _ => by linarith [axialD_lower z])
  have hh := hm (by norm_num) hx hx.1
  dsimp [f] at hh
  linarith [axial_initial,hx.2]

theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r+g r*b-p r*A-q r*B := by
  have hx : φ∈Icc (2/5) (7/10) :=
    ⟨(original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hmargin := mul_nonneg (coefficients r).2.2.1.le hm
  norm_num [forwardMargin] at hmargin
  rw [hw] at hmargin
  by_cases h3 : r=3
  · subst r
    have hX : -p 3-g 3*Real.sin φ≤0 := by norm_num [p,g]; nlinarith [tr.2.2.1]
    have hY : 0≤g 3*Real.cos φ-q 3 := by norm_num [g,q]; linarith [(angle_trig hx).2]
    have hd := mul_nonneg
      (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hY
    have hsupp := WrongWordCircleSupport.outer_axial_lower ht hX
      (show 0≤(outerAxial+1/2)*(g 3*Real.cos φ-q 3)-(-p 3-g 3*Real.sin φ)/2 by linarith)
    have hlow := axial_lower hx
    norm_num [p] at hsupp ⊢
    dsimp [axial] at hlow
    nlinarith only [hmargin,hsupp,hlow]
  · have hsupp := outer_circle_lower (X := -p r-g r*Real.sin φ)
      (Y := g r*Real.cos φ-q r) ht
    have he := WrongWordCircleSupport.energy_eq (p r) (q r) (g r) φ
    have hn : N r φ=Real.sqrt ((-p r-g r*Real.sin φ)^2+(g r*Real.cos φ-q r)^2) := by
      unfold N WrongWordCircleSupport.N CircularNorm.norm
      rw [he]
      congr 1
      dsimp [WrongWordCircleSupport.X,WrongWordCircleSupport.Y]
      ring
    rw [← hn] at hsupp
    have hf := F_lower r h3 hx
    dsimp [F] at hf
    nlinarith only [hmargin,hsupp,hf]

end SquaresInCircles.Eight.ShortMixedZero.PositiveCore
end
end
end
