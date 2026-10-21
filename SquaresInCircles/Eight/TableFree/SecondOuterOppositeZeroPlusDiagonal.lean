module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPositiveJ

/-!
# The positive-angle source-diagonal exit

Uncompiled source draft of Section 7.  The rotated circle gives a
strictly decreasing, strictly concave target coordinate.  The bounds
on its speed and acceleration are the whole-interval bounds displayed
in the hand proof, and both possible target labels give concave costs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PlusDiagonal
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
  have hxi : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have ht := positive_trig hxi
  have hs := Real.sin_le_self hx.1
  have hc := cos_lower_two hx.1
  have ho : -(2/5:ℝ)<offset ∧ offset< -(399/1000) := by
    dsimp [offset]; constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have hz : (3/5:ℝ)<Z x ∧ Z x<71/100 := by
    dsimp [Z]; constructor <;> linarith [ht.2.2.2.2.2,ht.2.1,hx.2]
  have hr : 0<Q0-(Z x)^2 := by norm_num [Q0]; nlinarith
  have hy := Real.sqrt_pos.mpr hr
  have hy2 := Real.sq_sqrt hr.le
  have hyl : (46/25:ℝ)<Y x := by dsimp [Y]; norm_num [Q0] at hy2; nlinarith
  have hyu : Y x<(2:ℝ) := by dsimp [Y]; norm_num [Q0] at hy2; nlinarith [sq_nonneg (Z x)]
  have hprod := mul_le_mul hyl.le (show (497/500:ℝ)≤Real.cos x by nlinarith)
    (by norm_num) (by linarith : 0≤Y x)
  have hpositive := mul_nonneg hz.1.le ht.2.2.1
  have hhorizontal : (9/5:ℝ)<horizontal x := by dsimp [horizontal]; linarith
  have hcircle : (horizontal x)^2+(vertical x)^2=Q0 := by
    dsimp [horizontal,vertical]
    linear_combination hy2+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)
  have hhorizontalU : horizontal x<2 := by norm_num [Q0] at hcircle; nlinarith [sq_nonneg (vertical x)]
  have hv1 := mul_le_mul hz.1.le (show (497/500:ℝ)≤Real.cos x by nlinarith)
    (by norm_num) (by linarith [hz.1] : 0≤Z x)
  have hv2 := mul_le_mul hyu.le hs ht.2.2.1 (by norm_num)
  have hv : 0<vertical x := by dsimp [vertical]; nlinarith [hx.2]
  have hflo : (Real.cos x-Real.sin x)/Y x<1 := by
    apply (div_lt_one (by linarith : 0<Y x)).2
    linarith [ht.2.1,ht.2.2.1]
  have hfhi : (11/25:ℝ)<(Real.cos x-Real.sin x)/Y x := by
    apply (lt_div_iff₀ (by linarith : 0<Y x)).2
    nlinarith [hx.2]
  have hsum := ht.2.2.2.2.2
  have hn : (72/25:ℝ)<(Real.sin x+Real.cos x)*(Q0-2-offset^2)-
      offset*(Real.sin x+Real.cos x)^2-2*offset := by
    have h1 := mul_le_mul_of_nonneg_right hsum
      (show 0≤Q0-2-offset^2 by norm_num [Q0]; nlinarith)
    have h2 := mul_le_mul_of_nonneg_left
      (show (1:ℝ)≤(Real.sin x+Real.cos x)^2 by nlinarith) (by linarith [ho.2] : 0≤-offset)
    norm_num [Q0] at h1
    nlinarith
  have hfd : (9/25:ℝ)<factorD x := by
    apply (lt_div_iff₀ (pow_pos (by linarith : 0<Y x) 3)).2
    have hpow := pow_lt_pow_left₀ (by linarith : 0≤Y x) hyu 3
    nlinarith
  exact ⟨hz.1,hz.2,hyl,hyu,by dsimp [Y]; linarith,hhorizontal,
    hhorizontalU,hv,by dsimp [factor]; linarith,by dsimp [factor]; linarith,hfd⟩

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt Y (-Z x*(Real.cos x-Real.sin x)/Y x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x) using 1 <;> dsimp [Z] <;> ring
  have hr : Q0-(Z x)^2≠0 := by nlinarith [(data hx).2.2.2.2.1]
  convert ((hz.pow 2).const_sub Q0).sqrt hr using 1 <;> dsimp [Y] <;> field_simp [hy.ne'] <;> ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt horizontal (vertical x*factor x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x) using 1 <;> dsimp [Z] <;> ring
  convert ((hz.mul (Real.hasDerivAt_sin x)).add ((Y_hasDerivAt hx).mul
    (Real.hasDerivAt_cos x))) using 1 <;> dsimp [horizontal,vertical,factor] <;> field_simp [hy.ne'] <;> ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt height (speed x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x) using 1 <;> dsimp [Z] <;> ring
  convert (((hz.mul (Real.hasDerivAt_cos x)).sub ((Y_hasDerivAt hx).mul
    (Real.hasDerivAt_sin x))).sub_const (1/2)) using 1 <;>
      dsimp [height,vertical,speed,horizontal,factor] <;> field_simp [hy.ne'] <;> ring

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt factor (factorD x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hr := (data hx).2.2.2.2.1
  convert (((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).div
    (Y_hasDerivAt hx) hy.ne').const_sub 1 using 1
  · rfl
  · dsimp [factorD]
    field_simp [hy.ne']
    dsimp [Z] at hr
    nlinarith [Real.sin_sq_add_cos_sq x]
lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt speed (acceleration x) x := by
  convert ((horizontal_hasDerivAt hx).mul (factor_hasDerivAt hx)).neg using 1 <;>
    dsimp [speed,acceleration] <;> ring

lemma speed_negative {x : ℝ} (hx : x∈Icc 0 (27/250)) : speed x<0 := by
  have h := data hx
  exact neg_lt_zero.mpr (mul_pos (by linarith [h.2.2.2.2.2.1]) h.2.2.2.2.2.2.2.2.1)
lemma acceleration_upper {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    acceleration x< -(81/125:ℝ) ∧ (speed x)^2<(784/625:ℝ) := by
  have h := data hx
  have hV := h.2.2.2.2.2.2.2.1
  have hU := h.2.2.2.2.2.1
  have hUu := h.2.2.2.2.2.2.1
  have hf := h.2.2.2.2.2.2.2.2.1
  have hfu := h.2.2.2.2.2.2.2.2.2.1
  have hfd := h.2.2.2.2.2.2.2.2.2.2
  have h1 := mul_lt_mul hU hfd (by norm_num) (by linarith : 0≤horizontal x)
  have h2 := mul_lt_mul hUu hfu hf (by norm_num)
  have h3 := mul_nonneg hV.le (sq_nonneg (factor x))
  dsimp [acceleration,speed]
  constructor <;> nlinarith

lemma height_zero : height 0=1-outerDiagonal := by norm_num [height,vertical,Z,offset]; ring
lemma height_antitone : AntitoneOn height (Icc 0 (27/250)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => (speed_negative (Ioo_subset_Icc_self hx)).le)
lemma target_bounds {x : ℝ} (hx : Domain x) : height x∈Icc 0 (101/1000) := by
  have hh := height_antitone (by norm_num) hx.1 hx.1.1
  rw [height_zero] at hh
  exact ⟨hx.2,by linarith [diagonal_fine.1]⟩

lemma cost_hasDerivAt (F G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (cost F G) (first G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  convert ((hasDerivAt_id x).add_const (F.outer outerDiagonal)).add
    ((G.outer_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1)) using 1 <;>
      dsimp [cost,first] <;> ring
lemma first_hasDerivAt (G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (first G) (second G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  convert ((((G.d1_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1)).mul
    (speed_hasDerivAt hx.1)).const_add 1) using 1 <;> dsimp [first,second] <;> ring

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
  have hP2 := (P_second_monotone ht (Asymmetric.rational_outer_mem (by norm_num)) (target_bounds hx).2).
    trans_lt Reference.P_101_second
  have hspeed := acceleration_upper hx.1
  have h1 := mul_le_mul hP2.le hspeed.2.le (sq_nonneg _) (by norm_num)
  have h2 := mul_lt_mul_of_pos_left hspeed.1 (by linarith [(P_first_bounds ht).1] : 0<PLabel.d1 (height x))
  have h3 := mul_lt_mul_of_pos_right (P_first_bounds ht).1 (by norm_num : (0:ℝ)<81/125)
  dsimp [second]
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PlusDiagonal
