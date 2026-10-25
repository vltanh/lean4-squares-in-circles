module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroReferences

/-!
# Eight squares: the positive-angle source-diagonal exit

The rotated circle gives a strictly decreasing, strictly concave target coordinate `height`
(`speed_negative`, `acceleration_upper`). Its speed and acceleration are bounded on the whole
interval (`data`), and both possible target labels give concave costs (`J_curvature`,
`P_curvature`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def offset : ℝ := 1/2-outerDiagonal
def Z (x : ℝ) : ℝ := offset+Real.sin x+Real.cos x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.sin x+Y x*Real.cos x
def vertical (x : ℝ) : ℝ := Z x*Real.cos x-Y x*Real.sin x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-(Real.cos x-Real.sin x)/Y x
def factorD (x : ℝ) : ℝ :=
  ((Real.sin x+Real.cos x)*(Q0-2-offset^2)-offset*(Real.sin x+Real.cos x)^2-2*offset)/(Y x)^3
def speed (x : ℝ) : ℝ := -horizontal x*factor x
def acceleration (x : ℝ) : ℝ := -vertical x*(factor x)^2-horizontal x*factorD x
def Domain (x : ℝ) : Prop := x∈Icc 0 (27/250) ∧ 0≤height x
def cost (F G : RoleLabel) (x : ℝ) : ℝ := x+F.outer outerDiagonal+G.outer (height x)
def first (G : RoleLabel) (x : ℝ) : ℝ := 1+G.d1 (height x)*speed x
def second (G : RoleLabel) (x : ℝ) : ℝ :=
  G.d2 (height x)*(speed x)^2+G.d1 (height x)*acceleration x

lemma data {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    (3/5:ℝ)<Z x ∧ Z x<71/100 ∧ (46/25:ℝ)<Y x ∧ Y x<2 ∧
      (Y x)^2+(Z x)^2=Q0 ∧ (9/5:ℝ)<horizontal x ∧ horizontal x<2 ∧
        0<vertical x ∧ 0<factor x ∧ factor x<14/25 ∧ (9/25:ℝ)<factorD x := by
  have hxi : x∈Icc 0 (7/10) := ⟨hx.1,by linarith only [hx.2]⟩
  have ht := positive_trig hxi
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have ho : -(2/5:ℝ)<offset ∧ offset< -(399/1000) := by
    have hd := diagonal_fine
    dsimp only [offset]; constructor <;> linarith only [hd.1,hd.2]
  have hz : (3/5:ℝ)<Z x ∧ Z x<71/100 := by
    dsimp only [Z]; constructor <;> linarith only [ht.2.2.2.2.2,ht.2.1,hx.2,hs,ho.1,ho.2]
  have hQ : Q0=9789/2500 := by norm_num [Q0]
  have hz2 : Z x^2<(71/100)^2 := pow_lt_pow_left₀ hz.2 (by linarith only [hz.1]) (by norm_num)
  have hz2' : (3/5)^2<Z x^2 := pow_lt_pow_left₀ hz.1 (by norm_num) (by norm_num)
  have hr : 0<Q0-(Z x)^2 := by rw [hQ]; linarith only [hz2]
  have hy : 0<Y x := Real.sqrt_pos.mpr hr
  have hy2 : (Y x)^2=Q0-(Z x)^2 := Real.sq_sqrt hr.le
  have hyl : (46/25:ℝ)<Y x :=
    lt_of_pow_lt_pow_left₀ 2 hy.le (by rw [hy2,hQ]; linarith only [hz2])
  have hyu : Y x<(2:ℝ) :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hy2,hQ]; linarith only [hz2'])
  have hx2 : x^2≤(27/250)*x := by rw [sq]; exact mul_le_mul_of_nonneg_right hx.2 hx.1
  have hcos : (497/500:ℝ)≤Real.cos x := by linarith only [hc,hx2,hx.2]
  have hprod := mul_le_mul hyl.le hcos (by norm_num) hy.le
  have hpositive := mul_nonneg (by linarith only [hz.1] : 0≤Z x) ht.2.2.1
  have hhorizontal : (9/5:ℝ)<horizontal x := by
    dsimp only [horizontal]; linarith only [hprod,hpositive]
  have hcircle : (horizontal x)^2+(vertical x)^2=Q0 := by
    dsimp only [horizontal,vertical]
    linear_combination hy2+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)
  have hhorizontalU : horizontal x<2 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      (by have := sq_nonneg (vertical x); linarith only [this,hcircle,hQ])
  have hv1 := mul_le_mul hz.1.le hcos (by norm_num) (by linarith only [hz.1] : 0≤Z x)
  have hv2 := mul_le_mul hyu.le hs ht.2.2.1 (by norm_num)
  have hv : 0<vertical x := by dsimp only [vertical]; linarith only [hx.2,hv1,hv2]
  have hflo : (Real.cos x-Real.sin x)/Y x<1 := by
    apply (div_lt_one hy).2
    linarith only [ht.2.1,ht.2.2.1,hyl]
  have hfhi : (11/25:ℝ)<(Real.cos x-Real.sin x)/Y x := by
    apply (lt_div_iff₀ hy).2
    linarith only [hx.2,hyu,hcos,hs]
  have hsum := ht.2.2.2.2.2
  have hn : (72/25:ℝ)<(Real.sin x+Real.cos x)*(Q0-2-offset^2)-
      offset*(Real.sin x+Real.cos x)^2-2*offset := by
    have ho2 : offset^2<4/25 := by
      have h := pow_lt_pow_left₀ (show -offset<2/5 by linarith only [ho.1])
        (by linarith only [ho.2]) (n := 2) (by norm_num)
      rw [neg_sq] at h
      linarith only [h]
    have h1 := mul_le_mul_of_nonneg_right hsum
      (show 0≤Q0-2-offset^2 by rw [hQ]; linarith only [ho2])
    have h2 := mul_le_mul_of_nonneg_left
      (one_le_pow₀ hsum : (1:ℝ)≤(Real.sin x+Real.cos x)^2)
      (by linarith only [ho.2] : 0≤-offset)
    rw [hQ] at h1 ⊢
    linarith only [ho.2,h1,h2,ho2]
  have hfd : (9/25:ℝ)<factorD x := by
    apply (lt_div_iff₀ (pow_pos hy 3)).2
    have hpow := pow_lt_pow_left₀ hyu hy.le (n := 3) (by norm_num)
    linarith only [hpow,hn]
  exact ⟨hz.1,hz.2,hyl,hyu,by linarith only [hy2],hhorizontal,
    hhorizontalU,hv,by dsimp only [factor]; linarith only [hflo],
    by dsimp only [factor]; linarith only [hfhi],hfd⟩

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt Y (-Z x*(Real.cos x-Real.sin x)/Y x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  have hr : Q0-(Z x)^2≠0 := by nlinarith [(data hx).2.2.2.2.1]
  refine (((hz.fun_pow 2).const_sub Q0).sqrt hr).congr_deriv ?_
  rw [show Real.sqrt (Q0-Z x^2)=Y x from rfl]
  field_simp
  ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt horizontal (vertical x*factor x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  refine ((hz.fun_mul (Real.hasDerivAt_sin x)).fun_add ((Y_hasDerivAt hx).fun_mul
    (Real.hasDerivAt_cos x))).congr_deriv ?_
  simp only [vertical,factor]
  field_simp
  ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt height (speed x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  refine (((hz.fun_mul (Real.hasDerivAt_cos x)).fun_sub ((Y_hasDerivAt hx).fun_mul
    (Real.hasDerivAt_sin x))).sub_const (1/2)).congr_deriv ?_
  simp only [speed,horizontal,factor]
  field_simp
  ring

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt factor (factorD x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hr := (data hx).2.2.2.2.1
  have key : (Real.sin x+Real.cos x)*(Y x)^2-Z x*(Real.cos x-Real.sin x)^2=
      (Real.sin x+Real.cos x)*(Q0-2-offset^2)-offset*(Real.sin x+Real.cos x)^2-2*offset := by
    simp only [Z] at hr ⊢
    linear_combination (Real.sin x+Real.cos x)*hr-
      2*(offset+Real.sin x+Real.cos x)*(Real.sin_sq_add_cos_sq x)
  refine ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).fun_div
    (Y_hasDerivAt hx) hy.ne').const_sub 1).congr_deriv ?_
  simp only [factorD]
  rw [←key]
  field_simp
  ring
lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt speed (acceleration x) x := by
  refine ((horizontal_hasDerivAt hx).fun_neg.fun_mul (factor_hasDerivAt hx)).congr_deriv ?_
  simp only [acceleration]
  ring

lemma speed_negative {x : ℝ} (hx : x∈Icc 0 (27/250)) : speed x<0 := by
  have h := data hx
  have hp := mul_pos (by linarith [h.2.2.2.2.2.1] : 0<horizontal x) h.2.2.2.2.2.2.2.2.1
  simp only [speed]
  linarith
lemma acceleration_upper {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    acceleration x< -(81/125:ℝ) ∧ (speed x)^2<(784/625:ℝ) := by
  have h := data hx
  have hV := h.2.2.2.2.2.2.2.1
  have hU := h.2.2.2.2.2.1
  have hUu := h.2.2.2.2.2.2.1
  have hf := h.2.2.2.2.2.2.2.2.1
  have hfu := h.2.2.2.2.2.2.2.2.2.1
  have hfd := h.2.2.2.2.2.2.2.2.2.2
  have h1 := mul_lt_mul hU hfd.le (by norm_num) (by linarith : 0≤horizontal x)
  have h2 := mul_lt_mul hUu hfu.le hf (by norm_num)
  have h3 := mul_nonneg hV.le (sq_nonneg (factor x))
  constructor
  · dsimp only [acceleration]
    linarith
  · rw [show (speed x)^2=(horizontal x*factor x)^2 by simp only [speed]; ring]
    have h4 := pow_lt_pow_left₀ h2 (mul_pos (by linarith) hf).le (n := 2) (by norm_num)
    linarith

lemma height_zero : height 0=1-outerDiagonal := by norm_num [height,vertical,Z,offset]; ring
lemma height_antitone : AntitoneOn height (Icc 0 (27/250)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => (speed_negative (Ioo_subset_Icc_self hx)).le)
lemma target_bounds {x : ℝ} (hx : Domain x) : height x∈Icc 0 (101/1000) := by
  have hh := height_antitone (by norm_num) hx.1 hx.1.1
  rw [height_zero] at hh
  exact ⟨hx.2,by linarith [diagonal_fine.1]⟩

lemma cost_hasDerivAt (F G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (cost F G) (first G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  refine (((hasDerivAt_id' x).add_const (F.outer outerDiagonal)).fun_add
    ((G.outer_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1))).congr_deriv ?_
  simp only [first]
lemma first_hasDerivAt (G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (first G) (second G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  refine ((((G.d1_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1)).fun_mul
    (speed_hasDerivAt hx.1)).const_add 1).congr_deriv ?_
  simp only [second,Function.comp_apply]
  ring

lemma J_curvature {x : ℝ} (hx : Domain x) : second JLabel x<0 := by
  have ht : height x∈Icc 0 outerDiagonal := ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  have h1 := mul_nonpos_of_nonpos_of_nonneg (by linarith [J_second_upper ht] : JLabel.d2 (height x)≤0)
    (sq_nonneg (speed x))
  have h2 := mul_neg_of_pos_of_neg (by linarith [(J_first_bounds ht).1] : 0<JLabel.d1 (height x))
    (by linarith [(acceleration_upper hx.1).1] : acceleration x<0)
  dsimp [second]
  linarith
lemma P_curvature {x : ℝ} (hx : Domain x) : second PLabel x<0 := by
  have ht : height x∈Icc 0 outerDiagonal := ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  have hP2 := (P_second_monotone ht (Asymmetric.rational_outer_mem (by norm_num)) (target_bounds hx).2).trans_lt Reference.P_101_second
  have hspeed := acceleration_upper hx.1
  have h1 := mul_le_mul hP2.le hspeed.2.le (sq_nonneg _) (by norm_num)
  have h2 := mul_lt_mul_of_pos_left hspeed.1 (by linarith [(P_first_bounds ht).1] : 0<PLabel.d1 (height x))
  have h3 := mul_lt_mul_of_pos_right (P_first_bounds ht).1 (by norm_num : (0:ℝ)<81/125)
  dsimp [second]
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
