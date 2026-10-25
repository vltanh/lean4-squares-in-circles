module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeTargetDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ

/-!
# Eight squares: the source-diagonal curve on the negative half

The
explicit rotated circle is the unchanged original target. Its factor
has negative derivative; the literal target-label cost is concave.
The initial and final endpoints are aligned and double-diagonal.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev horizontal := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal
abbrev vertical := SecondWord.NegativeTwo.PrimaryDiagonal.vertical
abbrev height := SecondWord.NegativeTwo.PrimaryDiagonal.height
abbrev factor := SecondWord.NegativeTwo.PrimaryDiagonal.factor
abbrev factorD := SecondWord.NegativeTwo.PrimaryDiagonal.factorD

def value (r : Row) (x : ℝ) : ℝ := -x+c r+(p r+q r)*outerDiagonal+
  v r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := -1+(t r*horizontal x-v r*vertical x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  -(t r*vertical x+v r*horizontal x)*(factor x)^2+
    (t r*horizontal x-v r*vertical x)*factorD x

lemma angle_mem {x : ℝ} (hx : x∈Icc 0 finalAngle) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans final_mem.2⟩

lemma final_height : height finalAngle=outerDiagonal :=
  SecondWord.OppositeZero.NegativePJ.diagonal_original
    (TargetDiagonal.domain ⟨final_bound.1.le,le_rfl⟩) double_contact

lemma target_band {x : ℝ} (hx : x∈Icc 0 finalAngle) : height x∈Icc low outerDiagonal := by
  have hl := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone
    (by norm_num) (angle_mem hx) hx.1
  have hu := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone
    (angle_mem hx) final_mem hx.2
  rw [SecondWord.NegativeTwo.PrimaryDiagonal.height_zero] at hl
  rw [show SecondWord.NegativeTwo.PrimaryDiagonal.height finalAngle=outerDiagonal
    from final_height] at hu
  exact ⟨hl,hu⟩

lemma coordinates {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    U (height x)=horizontal x ∧ W (height x)=vertical x := by
  have hband := target_band hx
  have hmem : height x∈Icc 0 outerDiagonal := ⟨low_mem.1.trans hband.1,hband.2⟩
  have hcircle := SecondWord.NegativeTwo.PrimaryDiagonal.circle (angle_mem hx)
  have hactual := UW_circle (outer_domain hmem)
  have hU := U_positive (outer_domain hmem)
  have hu := (SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive (angle_mem hx)).1
  have hW : W (height x)=vertical x := by
    dsimp [W,height,SecondWord.NegativeTwo.PrimaryDiagonal.height]
    ring
  rw [hW] at hactual
  exact ⟨by nlinarith,hW⟩

lemma contact {x : ℝ} (hx : x∈Icc 0 finalAngle) : minus (height x) x=outerDiagonal := by
  have hcoords := coordinates hx
  have he : minus (height x) x=1/2+(1-W (height x))*Real.cos x+U (height x)*Real.sin x := by
    simp only [minus,SecondWord.OppositeZero.minus,U,W]
    ring
  rw [he,hcoords.1,hcoords.2]
  dsimp only [horizontal,vertical,SecondWord.NegativeTwo.PrimaryDiagonal.horizontal,
    SecondWord.NegativeTwo.PrimaryDiagonal.vertical,SecondWord.NegativeTwo.PrimaryDiagonal.Z,
    SecondWord.NegativeTwo.PrimaryDiagonal.offset]
  linear_combination (-(1/2+Real.cos x-outerDiagonal))*Real.sin_sq_add_cos_sq x

lemma physical_domain {x : ℝ} (hx : x∈Icc 0 finalAngle) : MinusDomain (height x) x :=
  ⟨⟨low_mem.1.trans (target_band hx).1,(target_band hx).2⟩,angle_mem hx,
    by show minus (height x) x∈_; rw [contact hx]; exact diagonal_mem⟩

lemma original_coordinates {B x : ℝ} (hd : MinusDomain B x)
    (he : minus B x=outerDiagonal) : x∈Icc 0 finalAngle ∧ height x=B :=
  ⟨⟨hd.2.1.1,original_angle hd⟩,
    SecondWord.OppositeZero.NegativePJ.diagonal_original hd he⟩

lemma value_actual (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    value r x=minusCost r (height x) x := by
  have hcoords := coordinates hx
  rw [minusCost,contact hx]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,add_zero,zero_mul,zero_add]
  have hA : arc (height x)=horizontal x-1/2 := by
    have hh := hcoords.1
    dsimp [U] at hh
    linarith
  rw [hA]
  dsimp [value,height,SecondWord.NegativeTwo.PrimaryDiagonal.height]
  ring

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (value r) (first r x) x := by
  have hU := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt (angle_mem hx)
  have hV := SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt (angle_mem hx)
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+(p r+q r)*outerDiagonal) (-1) x := by
    simpa using (((hasDerivAt_id x).neg).add_const (c r)).add_const ((p r+q r)*outerDiagonal)
  have h2 : HasDerivAt (fun y => v r*(horizontal y-1/2))
      (v r*(-SecondWord.NegativeTwo.PrimaryDiagonal.vertical x*
        SecondWord.NegativeTwo.PrimaryDiagonal.factor x)) x :=
    (hU.sub_const (1/2)).const_mul (v r)
  have h3 : HasDerivAt (fun y => t r*(vertical y-1/2))
      (t r*SecondWord.NegativeTwo.PrimaryDiagonal.speed x) x :=
    (hV.sub_const (1/2)).const_mul (t r)
  have h := (h1.fun_add h2).fun_add h3
  have he : value r=fun y => -y+c r+(p r+q r)*outerDiagonal+
      v r*(horizontal y-1/2)+t r*(vertical y-1/2) := rfl
  rw [he]
  convert h using 1
  simp only [first,SecondWord.NegativeTwo.PrimaryDiagonal.speed]
  ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (first r) (second r x) x := by
  have hU := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt (angle_mem hx)
  have hV := SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt (angle_mem hx)
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt (angle_mem hx)
  have h := (((hU.const_mul (t r)).fun_sub (hV.const_mul (v r))).fun_mul hf).const_add (-1)
  have he : first r=fun y => -1+(t r*horizontal y-v r*vertical y)*factor y := rfl
  rw [he]
  convert h using 1
  simp only [second,SecondWord.NegativeTwo.PrimaryDiagonal.speed]
  ring

lemma work_signs (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    0<t r*vertical x+v r*horizontal x ∧ 0<t r*horizontal x-v r*vertical x := by
  have hcoords := coordinates hx
  have hband := target_band hx
  have hu := band_root hband
  have hV : (3/5:ℝ)<vertical x := by
    rw [←hcoords.2]
    dsimp [W,low] at *
    linarith [hband.1,outer_endpoint_bounds.2.2.2]
  have hU : 0<horizontal x ∧ horizontal x<(943/500:ℝ) := by
    rw [←hcoords.1]
    exact ⟨by linarith [hu.1],hu.2⟩
  have hfirst : 0<t r*vertical x+v r*horizontal x := by
    fin_cases r <;> norm_num [v,t] <;> linarith
  have htarget := (slope_bounds r (physical_domain hx).1).2.2
  have hh := mul_pos htarget hU.1
  have he : h r (height x)*horizontal x=t r*horizontal x-v r*vertical x := by
    dsimp [h,ratio]
    change (t r-v r*(W (height x)/U (height x)))*horizontal x=_
    rw [hcoords.1,hcoords.2]
    field_simp [hU.1.ne']
  rw [he] at hh
  exact ⟨hfirst,hh⟩

lemma curvature_negative (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) : second r x<0 := by
  have hwork := work_signs r hx
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_bounds (angle_mem hx)
  have hfd := SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative (angle_mem hx)
  have hfirst := mul_pos hwork.1 (sq_pos_of_pos (by linarith [hf.1] : 0<factor x))
  have hsecond := mul_neg_of_pos_of_neg hwork.2 hfd
  dsimp [second]
  linarith

lemma endpoints (r : Row) : (89809/100000:ℝ)<value r 0 ∧
    (89809/100000:ℝ)<value r finalAngle := by
  have hz : (0:ℝ)∈Icc 0 finalAngle := ⟨le_rfl,final_bound.1.le⟩
  have ht : finalAngle∈Icc 0 finalAngle := ⟨final_bound.1.le,le_rfl⟩
  constructor
  · rw [value_actual r hz,minusCost,contact hz,
      show height 0=1-outerDiagonal from SecondWord.NegativeTwo.PrimaryDiagonal.height_zero]
    have hh := aligned_original r diagonal_mem low_mem (by dsimp [low]; ring)
    simpa only [neg_zero,zero_add] using hh
  · rw [value_actual r ht,final_height]
    exact (TargetDiagonal.endpoints r).2

theorem lower (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    (89809/100000:ℝ)<value r x := by
  have hc : ConcaveOn ℝ (Icc 0 finalAngle) (value r) :=
    concave_of_deriv2 (fun x hx => value_hasDerivAt r hx)
      (fun x hx => first_hasDerivAt r hx) (fun x hx => (curvature_negative r hx).le)
  exact concave_gt_of_endpoints hc hx (endpoints r).1 (endpoints r).2

theorem original_lower (r : Row) {B x : ℝ} (hd : MinusDomain B x)
    (he : minus B x=outerDiagonal) : (89809/100000:ℝ)< minusCost r B x := by
  obtain ⟨hx,hB⟩ := original_coordinates hd he
  have hh := lower r hx
  rw [value_actual r hx,hB] at hh
  exact hh

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.SourceDiagonal
