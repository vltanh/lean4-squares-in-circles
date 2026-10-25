module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLabels

/-!
# Eight squares: the physical source-diagonal P/J branch

The
circle is rotated explicitly; no inverse function is chosen implicitly.
The lower angle .10726 lies just before the physical target-zero point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic

def start : ℝ := 5363/50000
def z₀ : ℝ := outerDiagonal-1/2
def Z (x : ℝ) : ℝ := z₀-Real.sin x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Y x*Real.cos x-Z x*Real.sin x
def vertical (x : ℝ) : ℝ := Y x*Real.sin x+Z x*Real.cos x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-Real.cos x/Y x
def factorD (x : ℝ) : ℝ :=
  (Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))/(Y x)^3
def speed (x : ℝ) : ℝ := horizontal x*factor x
def acceleration (x : ℝ) : ℝ := -vertical x*(factor x)^2+horizontal x*factorD x
def Domain (x : ℝ) : Prop := x∈Icc start (7/10) ∧ 0≤height x
def cost (x : ℝ) : ℝ := x+PLabel.outer outerDiagonal-JLabel.outer (height x)
def first (x : ℝ) : ℝ := 1-JLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  -JLabel.d2 (height x)*(speed x)^2-JLabel.d1 (height x)*acceleration x

lemma angle_mem {x : ℝ} (hx : x∈Icc start (7/10)) : x∈Icc 0 (7/10) :=
  ⟨by linarith [hx.1,show (0:ℝ)<start by norm_num [start]],hx.2⟩

lemma radical_data {x : ℝ} (hx : x∈Icc start (7/10)) :
    -(123/500:ℝ)<Z x ∧ Z x<293/1000 ∧ (39/20:ℝ)<Y x ∧ Y x<2 ∧
      (Y x)^2+(Z x)^2=Q0 := by
  have ht := positive_trig (angle_mem hx)
  have hs := sin_mono (by norm_num [start] : start∈Icc 0 (7/10)) (angle_mem hx) hx.1
  have hstart := HighOrderTaylor.S15_le_sin (by norm_num [start] : (0:ℝ)≤ start)
  norm_num [start,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7]
    at hstart hs
  have hz : -(123/500:ℝ)<Z x ∧ Z x<293/1000 := by
    dsimp [Z,z₀]
    constructor <;> linarith [ht.2.2.2.1,diagonal_fine.1,diagonal_fine.2]
  have hZ2 : (Z x)^2<86/1000 := by
    nlinarith [mul_pos (sub_pos.2 hz.2) (show 0<Z x+123/500 by linarith [hz.1])]
  have hrad : 0<Q0-(Z x)^2 := by norm_num [Q0]; linarith
  refine ⟨hz.1,hz.2,?_,?_,?_⟩
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num [Q0]; linarith)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num [Q0]; linarith [sq_nonneg (Z x)])
  · have he := Real.sq_sqrt hrad.le
    dsimp only [Y]
    linarith

lemma coordinates_positive {x : ℝ} (hx : x∈Icc start (7/10)) :
    (13/10:ℝ)<horizontal x ∧ 0<vertical x ∧ (19/39:ℝ)<factor x := by
  have hy := radical_data hx
  have ht := positive_trig (angle_mem hx)
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hymain := mul_lt_mul'' hy.2.2.1 ht.1 (by norm_num) (by norm_num)
  have hcut := mul_le_mul_of_nonneg_right hy.2.1.le ht.2.2.1
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.2.1.le (by norm_num : (0:ℝ)≤293/1000)
  have hv : vertical x=(Y x-Real.cos x)*Real.sin x+z₀*Real.cos x := by
    dsimp [vertical,Z]; ring
  have hp := mul_pos (show 0<z₀ by dsimp [z₀]; linarith [diagonal_fine.1]) hc
  have hn := mul_nonneg (show 0≤Y x-Real.cos x by linarith [hy.2.2.1,ht.2.1]) ht.2.2.1
  have hf : Real.cos x/Y x<(20/39:ℝ) := by
    apply (div_lt_iff₀ (by linarith [hy.2.2.1] : 0<Y x)).2
    linarith [ht.2.1,hy.2.2.1]
  refine ⟨?_,?_,?_⟩
  · dsimp [horizontal]; linarith
  · rw [hv]; linarith
  · dsimp [factor]; linarith

lemma circle {x : ℝ} (hx : x∈Icc start (7/10)) :
    (horizontal x)^2+(vertical x)^2=Q0 := by
  have hc := (radical_data hx).2.2.2.2
  dsimp [horizontal,vertical]
  linear_combination hc+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.cos x) x :=
  (Real.hasDerivAt_sin x).const_sub z₀

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt Y (Z x*Real.cos x/Y x) x := by
  have hy : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hrad : Q0-(Z x)^2≠0 := by nlinarith [(radical_data hx).2.2.2.2]
  refine ((((Z_hasDerivAt x).fun_pow 2).const_sub Q0).sqrt hrad).congr_deriv ?_
  rw [show Real.sqrt (Q0-Z x^2)=Y x from rfl]
  field_simp
  push_cast
  ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt horizontal (-vertical x*factor x) x := by
  have hy : 0<Y x := by linarith [(radical_data hx).2.2.1]
  refine (((Y_hasDerivAt hx).fun_mul (Real.hasDerivAt_cos x)).fun_sub
    ((Z_hasDerivAt x).fun_mul (Real.hasDerivAt_sin x))).congr_deriv ?_
  dsimp only [vertical,factor]
  field_simp
  ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt height (speed x) x := by
  have hy : 0<Y x := by linarith [(radical_data hx).2.2.1]
  refine ((((Y_hasDerivAt hx).fun_mul (Real.hasDerivAt_sin x)).fun_add
    ((Z_hasDerivAt x).fun_mul (Real.hasDerivAt_cos x))).sub_const (1/2)).congr_deriv ?_
  dsimp only [speed,horizontal,factor]
  field_simp
  ring

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt factor (factorD x) x := by
  have hy : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hn := (radical_data hx).2.2.2.2
  refine (((Real.hasDerivAt_cos x).fun_div (Y_hasDerivAt hx) hy.ne').const_sub 1).congr_deriv ?_
  dsimp only [factorD]
  dsimp only [Z] at hn ⊢
  field_simp
  linear_combination (Real.sin x)*hn+(z₀-Real.sin x)*(Real.sin_sq_add_cos_sq x)

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt speed (acceleration x) x :=
  ((horizontal_hasDerivAt hx).fun_mul (factor_hasDerivAt hx)).congr_deriv
    (by dsimp only [acceleration]; ring)

lemma horizontal_antitone : AntitoneOn horizontal (Icc start (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (horizontal_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => horizontal_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => by
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg
        (coordinates_positive (Ioo_subset_Icc_self hx)).2.1.le
        (by linarith [(coordinates_positive (Ioo_subset_Icc_self hx)).2.2])))

lemma height_monotone : MonotoneOn height (Icc start (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => mul_nonneg
      (by linarith [(coordinates_positive (Ioo_subset_Icc_self hx)).1])
      (by linarith [(coordinates_positive (Ioo_subset_Icc_self hx)).2.2]))

end SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
