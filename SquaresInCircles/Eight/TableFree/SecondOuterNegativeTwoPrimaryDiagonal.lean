module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoAligned

/-!
# The actual diagonal boundary for the lower source-primary owner

The target circle is rotated against a diagonal source.  The resulting
target coordinate increases, with strictly decreasing positive speed.
All identities below use the original circle at `Q0`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic

def offset : ℝ := 1/2-outerDiagonal
def Z (x : ℝ) : ℝ := Real.cos x+offset
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Y x*Real.cos x-Z x*Real.sin x
def vertical (x : ℝ) : ℝ := Y x*Real.sin x+Z x*Real.cos x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-Real.sin x/Y x
def factorD (x : ℝ) : ℝ :=
  (Z x*(Real.sin x)^2-Real.cos x*(Y x)^2)/(Y x)^3
def speed (x : ℝ) : ℝ := horizontal x*factor x
def acceleration (x : ℝ) : ℝ :=
  -vertical x*(factor x)^2+horizontal x*factorD x
def Domain (x : ℝ) : Prop := x∈Icc 0 (7/10) ∧ height x≤outerDiagonal

lemma offset_bounds : (-2/5:ℝ)<offset ∧ offset< -399/1000 := by
  dsimp [offset]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma radical_data {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<Z x ∧ Z x<61/100 ∧ (47/25:ℝ)<Y x ∧ Y x<2 ∧
      (Y x)^2+(Z x)^2=Q0 := by
  have ht := positive_trig hx
  have hz : 0<Z x ∧ Z x<61/100 := by
    dsimp [Z]
    constructor <;> linarith [offset_bounds.1,offset_bounds.2,ht.1,ht.2.1]
  have hrad : 0<Q0-(Z x)^2 := by
    norm_num [Q0]
    nlinarith [sq_nonneg (Z x)]
  have hy : 0<Y x := Real.sqrt_pos.2 hrad
  have he : (Y x)^2=Q0-(Z x)^2 := Real.sq_sqrt hrad.le
  refine ⟨hz.1,hz.2,?_,?_,by linarith⟩
  · norm_num [Q0] at he
    nlinarith
  · norm_num [Q0] at he
    nlinarith [sq_nonneg (Z x)]

lemma factor_bounds {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (13/20:ℝ)<factor x ∧ factor x≤1 := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hlo : Real.sin x/Y x<(7/20:ℝ) := by
    apply (div_lt_iff₀ hyp).2
    nlinarith [hy.2.2.1,ht.2.2.2.1]
  have hhi : 0≤Real.sin x/Y x := div_nonneg ht.2.2.1 hyp.le
  dsimp [factor]
  exact ⟨by linarith,by linarith⟩

lemma coordinates_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1<horizontal x ∧ 0<vertical x := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hmain := mul_lt_mul hy.2.2.1 ht.1 (by norm_num : (0:ℝ)<19121/25000) hyp.le
  have hsub := mul_le_mul hy.2.1.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤61/100)
  have hv1 := mul_nonneg hyp.le ht.2.2.1
  have hv2 := mul_pos hy.1 hc
  dsimp [horizontal,vertical]
  constructor <;> nlinarith

lemma circle {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (horizontal x)^2+(vertical x)^2=Q0 := by
  have hc := (radical_data hx).2.2.2.2
  dsimp [horizontal,vertical]
  linear_combination hc+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)

lemma height_zero : height 0=1-outerDiagonal := by
  norm_num [height,vertical,Z,offset]
  ring

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x :=
  (Real.hasDerivAt_cos x).add_const offset

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hy := radical_data hx
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hrad : Q0-(Z x)^2≠0 := by nlinarith [hy.2.2.2.2]
  have hd := (((Z_hasDerivAt x).pow 2).const_sub Q0).sqrt hrad
  convert hd using 1 <;> dsimp [Y] <;>
    field_simp [show Real.sqrt (Q0-(Z x)^2)≠0 from hyp.ne'] <;> ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt horizontal (-vertical x*factor x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x)).sub
    ((Z_hasDerivAt x).mul (Real.hasDerivAt_sin x))
  convert hd using 1 <;> dsimp [horizontal,vertical,factor] <;>
    field_simp [hyp.ne'] <;> ring

lemma vertical_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt vertical (speed x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Y_hasDerivAt hx).mul (Real.hasDerivAt_sin x)).add
    ((Z_hasDerivAt x).mul (Real.hasDerivAt_cos x))
  convert hd using 1 <;> dsimp [horizontal,vertical,factor,speed] <;>
    field_simp [hyp.ne'] <;> ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt height (speed x) x := (vertical_hasDerivAt hx).sub_const (1/2)

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt factor (factorD x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Real.hasDerivAt_sin x).div (Y_hasDerivAt hx) hyp.ne').const_sub 1
  convert hd using 1 <;> dsimp [factor,factorD] <;> field_simp [hyp.ne'] <;> ring

lemma factorD_numerator {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    factorD x*(Y x)^3=(1-Q0+offset^2)*Real.cos x+
      offset*(1+(Real.cos x)^2) := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hy := (radical_data hx).2.2.2.2
  have he : factorD x*(Y x)^3=Z x*(Real.sin x)^2-Real.cos x*(Y x)^2 := by
    dsimp [factorD]
    field_simp [hyp.ne']
  rw [he]
  dsimp [Z] at hy ⊢
  linear_combination (Real.cos x+offset)*(Real.sin_sq_add_cos_sq x)-Real.cos x*hy

lemma factorD_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : factorD x<0 := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hk := offset_bounds
  have he := factorD_numerator hx
  have hcoef : 1-Q0+offset^2<0 := by norm_num [Q0]; nlinarith
  have hfirst := mul_neg_of_neg_of_pos hcoef (by linarith [ht.1] : 0<Real.cos x)
  have hlast := mul_neg_of_neg_of_pos (by linarith [hk.2] : offset<0)
    (by nlinarith [sq_nonneg (Real.cos x)] : 0<1+(Real.cos x)^2)
  have hp := pow_pos (show 0<Y x by linarith [hy.2.2.1]) 3
  nlinarith

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt speed (acceleration x) x := by
  convert (horizontal_hasDerivAt hx).mul (factor_hasDerivAt hx) using 1 <;>
    dsimp [speed,acceleration] <;> ring

lemma speed_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : (1/2:ℝ)<speed x := by
  have hh := mul_lt_mul (coordinates_positive hx).1 (factor_bounds hx).1
    (by norm_num : (0:ℝ)<13/20)
    (by linarith [(coordinates_positive hx).1] : 0≤horizontal x)
  dsimp [speed]
  nlinarith

lemma acceleration_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : acceleration x<0 := by
  have hp := coordinates_positive hx
  have hf := factor_bounds hx
  have hleft := mul_pos hp.2 (pow_pos (show 0<factor x by linarith [hf.1]) 2)
  have hright := mul_neg_of_pos_of_neg (by linarith [hp.1] : 0<horizontal x)
    (factorD_negative hx)
  dsimp [acceleration]
  linarith

lemma height_monotone : MonotoneOn height (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [speed_positive (Ioo_subset_Icc_self hx)])

lemma height_half_monotone : MonotoneOn (fun x => height x-x/2) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => ((height_hasDerivAt hx).sub ((hasDerivAt_id x).div_const 2)).continuousAt.continuousWithinAt)
    (fun x hx => (height_hasDerivAt (Ioo_subset_Icc_self hx)).sub ((hasDerivAt_id x).div_const 2))
  intro x hx
  linarith [speed_positive (Ioo_subset_Icc_self hx)]

lemma horizontal_antitone : AntitoneOn horizontal (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (horizontal_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => horizontal_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => by
      have h := coordinates_positive (Ioo_subset_Icc_self hx)
      have f := factor_bounds (Ioo_subset_Icc_self hx)
      exact neg_nonpos.mpr (mul_nonneg h.2.le (by linarith [f.1])))

lemma factor_antitone : AntitoneOn factor (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (factor_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => factor_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => (factorD_negative (Ioo_subset_Icc_self hx)).le)

lemma speed_antitone : AntitoneOn speed (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (speed_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => speed_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => (acceleration_negative (Ioo_subset_Icc_self hx)).le)

lemma target_mem {x : ℝ} (hx : Domain x) : height x∈Icc 0 outerDiagonal := by
  have hz := height_monotone (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx.1 hx.1.1
  rw [height_zero] at hz
  exact ⟨by linarith [outer_endpoint_bounds.2.2.2],hx.2⟩

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.PrimaryDiagonal
