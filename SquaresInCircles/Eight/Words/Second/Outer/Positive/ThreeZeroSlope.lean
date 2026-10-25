module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCut
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyMinorant
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceSlope

/-!
# Eight squares: positive original derivative on the entire zero-source arc

The quotient curvature bound uses the same four positive terms as
the short-source argument.  The previously established target
curvature already makes the comparison slope strictly concave;
its actual two endpoint values close the full later interval.
-/

section
/-!
## The actual meeting point of the two diagonal contact boundaries

The original source coordinate at a diagonal target decreases
strictly with the angle.  Two fixed Taylor references locate its
unique crossing of the source diagonal between `1.014` and `1.015`.
The crossing is constructed by the intermediate value theorem.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact

open CommonQuarter CorePairGeometry Arithmetic

def parameter : ℝ := 1/2-outerDiagonal
def height (φ : ℝ) : ℝ := FirstContact.source outerDiagonal φ
def heightFirst (φ : ℝ) : ℝ :=
  (1/2-outerDiagonal)*Real.cos φ-(outerDiagonal+1/2)*Real.sin φ
def heightSecond (φ : ℝ) : ℝ := 1/2-height φ

lemma diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
lemma parameter_mem : parameter∈Icc (-2/5:ℝ) (1/2) := by
  dsimp [parameter]
  constructor <;> linarith [outer_endpoint_bounds.2.2.2,fine_outer_endpoint_bounds.2]

lemma height_formula (φ : ℝ) :
    height φ=1/2+(1/2-outerDiagonal)*Real.sin φ+
      (outerDiagonal+1/2)*Real.cos φ := by
  dsimp [height,FirstContact.source,U,W]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma height_hasDerivAt (φ : ℝ) : HasDerivAt height (heightFirst φ) φ := by
  have hd := (((Real.hasDerivAt_sin φ).const_mul (1/2-outerDiagonal)).const_add
    (1/2)).add ((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2))
  convert hd using 1
  · ext t
    exact height_formula t
  · dsimp [heightFirst]
    ring

lemma heightFirst_hasDerivAt (φ : ℝ) :
    HasDerivAt heightFirst (heightSecond φ) φ := by
  have hd := ((Real.hasDerivAt_cos φ).const_mul (1/2-outerDiagonal)).sub
    ((Real.hasDerivAt_sin φ).const_mul (outerDiagonal+1/2))
  convert hd using 1
  · rfl
  · rw [heightSecond,height_formula]
    ring

lemma heightFirst_upper {φ : ℝ} (hφ : Lower φ) : heightFirst φ<(-1:ℝ) := by
  have ht := lower_trig hφ
  have hfirst := mul_nonpos_of_nonpos_of_nonneg
    (show 1/2-outerDiagonal≤0 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hlast := mul_lt_mul''
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.1 (by norm_num : (0:ℝ)≤1399/1000) (by norm_num : (0:ℝ)≤19121/25000)
  dsimp [heightFirst]
  linarith

lemma height_antitone : AntitoneOn height (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => (height_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => height_hasDerivAt φ)
    (fun φ hφ => by linarith [heightFirst_upper (Ioo_subset_Icc_self hφ)])

lemma height_shift_antitone :
    AntitoneOn (fun φ => height φ+φ) (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => ((height_hasDerivAt φ).add (hasDerivAt_id φ)).continuousAt.continuousWithinAt)
    (fun φ _ => (height_hasDerivAt φ).add (hasDerivAt_id φ))
    (fun φ hφ => by linarith [heightFirst_upper (Ioo_subset_Icc_self hφ)])

lemma reference_lower : outerDiagonal<height (507/500) := by
  have ht := PointProducts.trig (show (0:ℝ)≤507/500 by norm_num)
  have hneg : 1/2-outerDiagonal∈Icc
      (1/2-(89921406510941/10^14:ℝ)) (1/2-(89921406510940/10^14:ℝ)) :=
    ⟨by linarith [diagonal_fine.2],by linarith [diagonal_fine.1]⟩
  have hpos : outerDiagonal+1/2∈Icc
      ((89921406510940/10^14:ℝ)+1/2) ((89921406510941/10^14:ℝ)+1/2) :=
    ⟨by linarith [diagonal_fine.1],by linarith [diagonal_fine.2]⟩
  have hs := PointProducts.product hneg ht.1
  have hc := PointProducts.product hpos ht.2
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at hs hc
  rw [height_formula]
  linarith [hs.1,hc.1,diagonal_fine.2]

lemma reference_upper : height (203/200)<outerDiagonal := by
  have ht := PointProducts.trig (show (0:ℝ)≤203/200 by norm_num)
  have hneg : 1/2-outerDiagonal∈Icc
      (1/2-(89921406510941/10^14:ℝ)) (1/2-(89921406510940/10^14:ℝ)) :=
    ⟨by linarith [diagonal_fine.2],by linarith [diagonal_fine.1]⟩
  have hpos : outerDiagonal+1/2∈Icc
      ((89921406510940/10^14:ℝ)+1/2) ((89921406510941/10^14:ℝ)+1/2) :=
    ⟨by linarith [diagonal_fine.1],by linarith [diagonal_fine.2]⟩
  have hs := PointProducts.product hneg ht.1
  have hc := PointProducts.product hpos ht.2
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at hs hc
  rw [height_formula]
  linarith [hs.2,hc.2,diagonal_fine.1]

lemma join_lower {e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200)) : Lower e := by
  constructor
  · dsimp [lowerAngle]
    linarith [he.1,pi_hand_enclosure.2]
  · linarith [he.2,pi_hand_enclosure.1]

theorem exists_join : ∃ e : ℝ, e∈Icc (507/500:ℝ) (203/200) ∧ height e=outerDiagonal := by
  have hc : Continuous height := continuous_iff_continuousAt.mpr
    (fun t => (height_hasDerivAt t).continuousAt)
  obtain ⟨e,he,hh⟩ := intermediate_value_Icc (show (507/500:ℝ)≤203/200 by norm_num)
    hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-height (507/500)) (-height (203/200)) from
      ⟨by linarith [reference_lower],by linarith [reference_upper]⟩)
  have hh' : -height e=-outerDiagonal := hh
  exact ⟨e,he,by linarith⟩

lemma before_join {φ e : ℝ} (hφ : Lower φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal)
    (hh : outerDiagonal≤height φ) : φ≤e := by
  rcases le_total φ e with h | h
  · exact h
  · have hs : height φ+φ≤height e+e := height_shift_antitone (join_lower he) hφ h
    rw [hc] at hs
    linarith

lemma after_join {φ e : ℝ} (hφ : Lower φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal)
    (hh : height φ≤outerDiagonal) : e≤φ := by
  rcases le_total e φ with h | h
  · exact h
  · have hs : height e+e≤height φ+φ := height_shift_antitone hφ (join_lower he) h
    rw [hc] at hs
    linarith

lemma corner_value {e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200)) :
    (44889/50000:ℝ)<value outerDiagonal outerDiagonal e := by
  dsimp [value]
  linarith [he.1,V_diagonal_bounds.1,L_diagonal_upper]

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact
end
end
end

section
/-!
## Original endpoint reserves for the positive diagonal boundaries

The close endpoint is the source diagonal at `pi/2-0.7`.  Its target
is computed by the exact circle rotation, then the literal target
label is bounded at that actual point.  The reserve is strictly
above `0.89778`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma lower_angle_mem : Lower lowerAngle := by
  constructor
  · rfl
  · dsimp [lowerAngle]
    linarith

lemma left_domain : SourceCurve.Domain parameter lowerAngle :=
  ⟨parameter_mem,lower_angle_mem⟩

lemma left_z : z parameter lowerAngle∈Icc (36562811/10^8:ℝ) (36562813/10^8) := by
  dsimp [z,parameter]
  exact ⟨by linarith [EarlyCut.left_trig.1.1,diagonal_fine.2],
    by linarith [EarlyCut.left_trig.1.2,diagonal_fine.1]⟩

lemma left_radical :
    y parameter lowerAngle∈Icc (194471489/10^8:ℝ) (194471493/10^8) := by
  have hh := y_data left_domain
  have hz := left_z
  have hz0 : 0≤z parameter lowerAngle := by linarith [hz.1]
  have hzl2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤36562811/10^8) hz.1 2
  have hzh2 := pow_le_pow_left₀ hz0 hz.2 2
  norm_num [Q0] at hh
  constructor <;> nlinarith

lemma left_rotation :
    u parameter lowerAngle∈Icc (15324675/10^7:ℝ) (15324676/10^7) ∧
      w parameter lowerAngle∈Icc (12518558/10^7:ℝ) (12518560/10^7) := by
  have hz := left_z
  have hy := left_radical
  have hs := EarlyCut.left_trig.1
  have hc := EarlyCut.left_trig.2
  have hz0 : 0≤z parameter lowerAngle := by linarith [hz.1]
  have hy0 : 0≤y parameter lowerAngle := by linarith [hy.1]
  have hs0 : 0≤Real.sin lowerAngle := by linarith [hs.1]
  have hc0 : 0≤Real.cos lowerAngle := by linarith [hc.1]
  have hzslo := mul_le_mul hz.1 hs.1 (by norm_num) hz0
  have hzshi := mul_le_mul hz.2 hs.2 hs0 (by norm_num)
  have hyclo := mul_le_mul hy.1 hc.1 (by norm_num) hy0
  have hychi := mul_le_mul hy.2 hc.2 hc0 (by norm_num)
  have hyslo := mul_le_mul hy.1 hs.1 (by norm_num) hy0
  have hyshi := mul_le_mul hy.2 hs.2 hs0 (by norm_num)
  have hzclo := mul_le_mul hz.1 hc.1 (by norm_num) hz0
  have hzchi := mul_le_mul hz.2 hc.2 hc0 (by norm_num)
  dsimp [u,w]
  exact ⟨⟨by norm_num at hzslo hyclo; linarith,
    by norm_num at hzshi hychi; linarith⟩,
    ⟨by norm_num at hyslo hzchi; linarith,
    by norm_num at hyshi hzclo; linarith⟩⟩

lemma left_target : target parameter lowerAngle∈Icc (3/4:ℝ) outerDiagonal := by
  have hw := left_rotation.2
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma left_target_mem : target parameter lowerAngle∈Icc 0 outerDiagonal :=
  ⟨by linarith [left_target.1],left_target.2⟩

lemma diagonal_V_lower : (1620101/2500000:ℝ)<V outerDiagonal := by
  have hd := diagonal_fine
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤89921406510940/100000000000000) hd.1.le 2
  rw [V_diagonal]
  nlinarith

lemma left_value :
    (44889/50000:ℝ)<value outerDiagonal (target parameter lowerAngle) lowerAngle := by
  have hw := left_rotation.2
  have hB : target parameter lowerAngle∈Icc
      (7518558/10^7:ℝ) (7518560/10^7) := by
    dsimp [target]
    constructor <;> linarith [hw.1,hw.2]
  have hU : U (target parameter lowerAngle)∈Icc
      (15324675/10^7:ℝ) (15324676/10^7) := by
    rw [target_U left_domain left_target_mem]
    exact left_rotation.1
  have hL := LReference.target left_target_mem hB hU (by norm_num) (by norm_num)
  have hLhi := hL.2.1
  norm_num [LReference.valueHi] at hLhi
  have hA : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [value]
  linarith [diagonal_V_lower,pi_hand_enclosure.1]

lemma upper_join_trig : Real.sin (203/200)<(17/20:ℝ) ∧
    (527/1000:ℝ)<Real.cos (203/200) := by
  have ht := PointProducts.trig (show (0:ℝ)≤203/200 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨by linarith [ht.1.2],by linarith [ht.2.1]⟩

lemma lower_join_sine : (106/125:ℝ)<Real.sin (507/500) := by
  have ht := PointProducts.trig (show (0:ℝ)≤507/500 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  linarith [ht.1.1]

lemma target_three_quarters_mem : (3/4:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma target_three_quarters_curvature : (8/5:ℝ)<LLabel.d2 (3/4) := by
  have hU := shifted_chart_reference (outer_domain target_three_quarters_mem)
    (l := (76699/50000:ℝ)) (u := (767/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_three_quarters_mem
    (show (3/4:ℝ)∈Icc (3/4) (3/4) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hlo := hL.2.2.2.2.1
  norm_num [LReference.secondLo,Q0] at hlo
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact
end
end
end

section
/-!
## The entire original source-diagonal boundary

The actual target increases from the lower-angle endpoint to the
unique diagonal crossing.  On that whole physical arc the target
curvature and angular speed make the cost strictly concave.  The
two actual endpoint reserves therefore control every contact.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic SourceCurve
open DiagonalContact (parameter parameter_mem diagonal_mem)

def Domain (φ : ℝ) : Prop := Lower φ ∧ target parameter φ≤outerDiagonal
def cost (φ : ℝ) : ℝ := value outerDiagonal (target parameter φ) φ
def first (φ : ℝ) : ℝ := 1-LLabel.d1 (target parameter φ)*bp parameter φ
def second (φ : ℝ) : ℝ :=
  -LLabel.d2 (target parameter φ)*(bp parameter φ)^2-
    LLabel.d1 (target parameter φ)*bpp parameter φ

lemma source_domain {φ : ℝ} (hφ : Domain φ) : SourceCurve.Domain parameter φ :=
  ⟨parameter_mem,hφ.1⟩

lemma target_data {φ : ℝ} (hφ : Domain φ) :
    target parameter φ∈Icc (3/4:ℝ) outerDiagonal := by
  have hh := target_monotone parameter_mem DiagonalContact.lower_angle_mem hφ.1 hφ.1.1
  exact ⟨DiagonalContact.left_target.1.trans hh,hφ.2⟩

lemma target_mem {φ : ℝ} (hφ : Domain φ) : target parameter φ∈Icc 0 outerDiagonal :=
  ⟨by linarith [(target_data hφ).1],hφ.2⟩

lemma endpoint_target {e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200))
    (hc : DiagonalContact.height e=outerDiagonal) : target parameter e=outerDiagonal := by
  apply (unique_target (show SourceCurve.Domain parameter e from
    ⟨parameter_mem,DiagonalContact.join_lower he⟩) diagonal_mem ?_).symm
  simpa only [parameter,DiagonalContact.height,sub_sub_cancel] using hc

lemma domain_before {φ e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200))
    (hc : DiagonalContact.height e=outerDiagonal) (hφ : φ∈Icc lowerAngle e) : Domain φ := by
  have hl : Lower φ := ⟨hφ.1,hφ.2.trans (DiagonalContact.join_lower he).2⟩
  have hh := target_monotone parameter_mem hl (DiagonalContact.join_lower he) hφ.2
  rw [endpoint_target he hc] at hh
  exact ⟨hl,hh⟩

lemma bounded_by_end {φ e : ℝ} (hφ : Domain φ)
    (he : e∈Icc (507/500:ℝ) (203/200))
    (hc : DiagonalContact.height e=outerDiagonal) : φ≤e := by
  have hcontact := contact (source_domain hφ) (target_mem hφ)
  have hh := FirstContact.source_monotone hφ.1 (target_mem hφ) diagonal_mem hφ.2
  have heq : (1/2:ℝ)-parameter=outerDiagonal := by dsimp [parameter]; ring
  dsimp only at hh
  rw [hcontact,heq] at hh
  exact DiagonalContact.before_join hφ.1 he hc hh

lemma angle_upper {φ : ℝ} (hφ : Domain φ) : φ≤(203/200:ℝ) := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  exact (bounded_by_end hφ he hc).trans he.2

lemma geometry {φ : ℝ} (hφ : Domain φ) :
    (963/500:ℝ)<y parameter φ ∧ y parameter φ<(973/500:ℝ) ∧
      (1331/2000:ℝ)<SecondWord.PositiveThree.SourceCurve.f parameter φ ∧ SecondWord.PositiveThree.SourceCurve.f parameter φ<(73/100:ℝ) ∧
      (93/100:ℝ)<bp parameter φ ∧
      -(7/5:ℝ)*(73/100)^2<bpp parameter φ := by
  have hsdom := source_domain hφ
  have ht := lower_trig hφ.1
  have hupp : Lower (203/200:ℝ) := DiagonalContact.join_lower ⟨by norm_num,le_rfl⟩
  have hsupper := lower_sin_monotone hφ.1 hupp (angle_upper hφ)
  have hclower := lower_cos_antitone hφ.1 hupp (angle_upper hφ)
  have hz : (9121/25000:ℝ)<z parameter φ ∧ z parameter φ<(451/1000:ℝ) := by
    dsimp [z,parameter]
    constructor <;> linarith [ht.1,hsupper,DiagonalContact.upper_join_trig.1,
      fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]
  have hy := y_data hsdom
  have hyp : 0<y parameter φ := by linarith [hy.1]
  have hzl := pow_lt_pow_left₀ hz.1 (by norm_num) two_ne_zero
  have hzh := pow_lt_pow_left₀ hz.2 (by linarith [hz.1]) two_ne_zero
  have hybounds : (963/500:ℝ)<y parameter φ ∧ y parameter φ<(973/500:ℝ) := by
    norm_num [Q0] at hy hzl hzh
    constructor
    · exact lt_of_pow_lt_pow_left₀ 2 hyp.le (by norm_num; linarith)
    · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by norm_num; linarith)
  have hcoslo : (527/1000:ℝ)<Real.cos φ :=
    DiagonalContact.upper_join_trig.2.trans_le hclower
  have hfraclo : (27/100:ℝ)<Real.cos φ/y parameter φ := by
    apply (lt_div_iff₀ hyp).2
    linarith [hybounds.2,hcoslo]
  have hfrachigh : Real.cos φ/y parameter φ<(669/2000:ℝ) := by
    apply (div_lt_iff₀ hyp).2
    linarith [hybounds.1,ht.2.2.2.1]
  have hfb : (1331/2000:ℝ)<SourceCurve.f parameter φ ∧ SourceCurve.f parameter φ<(73/100:ℝ) := by
    dsimp [SourceCurve.f]
    exact ⟨by linarith,by linarith⟩
  have hub := UW_bounds (target_mem hφ)
  rw [target_U hsdom (target_mem hφ),target_W] at hub
  have hbp := mul_lt_mul hub.1 hfb.1.le
    (by norm_num : (0:ℝ)<1331/2000) (u_positive hsdom).le
  have hf0 := (f_bounds hsdom).1
  have hf2 : (SourceCurve.f parameter φ)^2<(73/100:ℝ)^2 := pow_lt_pow_left₀ hfb.2 hf0.le two_ne_zero
  have hprod := mul_lt_mul hub.2.2.2 hf2.le (sq_pos_of_pos hf0)
    (by norm_num : (0:ℝ)≤7/5)
  have hpositive := mul_pos (u_positive hsdom) (fp_positive hsdom)
  refine ⟨hybounds.1,hybounds.2,hfb.1,hfb.2,?_,?_⟩
  · dsimp [bp]
    norm_num at hbp
    linarith
  · dsimp [bpp]
    linarith

lemma cost_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt cost (first φ) φ := by
  have hd := ((hasDerivAt_id φ).add_const (V outerDiagonal)).sub
    ((LLabel.outer_hasDerivAt (outer_domain (target_mem hφ))).comp φ
      (target_hasDerivAt (source_domain hφ)))
  convert hd using 1
  · funext t
    simp only [cost,value,L,Pi.sub_apply,Function.comp_apply,id]
  · simp only [first]

lemma first_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt first (second φ) φ := by
  have hd := (((LLabel.d1_hasDerivAt (outer_domain (target_mem hφ))).comp φ
    (target_hasDerivAt (source_domain hφ))).mul
      (bp_hasDerivAt (source_domain hφ))).const_sub 1
  convert hd using 1
  · funext t
    simp only [first,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

lemma second_negative {φ : ℝ} (hφ : Domain φ) : second φ<0 := by
  have hg := geometry hφ
  have hL := L_first_bounds (target_mem hφ)
  have hLp : 0<LLabel.d1 (target parameter φ) := by linarith [hL.1]
  have hLdd := DiagonalContact.target_three_quarters_curvature.trans_le
    (L_second_monotone DiagonalContact.target_three_quarters_mem
      (target_mem hφ) (target_data hφ).1)
  have hbp2 : (93/100:ℝ)^2<(bp parameter φ)^2 :=
    pow_lt_pow_left₀ hg.2.2.2.2.1 (by norm_num) two_ne_zero
  have hneg := mul_lt_mul hLdd hbp2.le (by norm_num : (0:ℝ)<(93/100)^2)
    (by linarith [hLdd] : 0≤LLabel.d2 (target parameter φ))
  have hlast1 := mul_lt_mul_of_pos_left hg.2.2.2.2.2 hLp
  have hlast2 := mul_lt_mul_of_pos_right hL.2
    (by norm_num : (0:ℝ)<(7/5)*(73/100)^2)
  dsimp [second]
  linarith

theorem cost_lower {φ : ℝ} (hφ : Domain φ) : (44889/50000:ℝ)<cost φ := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  have hφe := bounded_by_end hφ he hc
  have hconcave : ConcaveOn ℝ (Icc lowerAngle e) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (domain_before he hc ht))
      (fun t ht => first_hasDerivAt (domain_before he hc ht))
      (fun t ht => (second_negative (domain_before he hc ht)).le)
  have hleft : (44889/50000:ℝ)<cost lowerAngle := DiagonalContact.left_value
  have hright : (44889/50000:ℝ)<cost e := by
    dsimp [cost]
    rw [endpoint_target he hc]
    exact DiagonalContact.corner_value he
  exact concave_gt_of_endpoints hconcave ⟨hφ.1.1,hφe⟩ hleft hright

theorem original_contact {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : Lower φ) (hc : FirstContact.source B φ=outerDiagonal) :
    (44889/50000:ℝ)<value outerDiagonal B φ := by
  have he := unique_target (show SourceCurve.Domain parameter φ from ⟨parameter_mem,hφ⟩)
    hB (show FirstContact.source B φ=1/2-parameter by simpa [parameter] using hc)
  have hd : Domain φ := ⟨hφ,by rw [←he]; exact hB.2⟩
  simpa only [cost,←he] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalSource
end
end
end

section
/-!
## The early support on the entire physical target arc

The target support has curvature at least `1.29` up to `0.34`.
Beyond that coordinate its first derivative is positive: angle
monotonicity reduces to `1.3`, and concavity reduces the remaining
target interval to its two endpoints.  Thus the one quadratic
minorant controls every original target, including weak contacts.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def cut : ℝ := 17/50

lemma cut_mem : cut∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [cut])

lemma cut_references :
    (11721/25000:ℝ)<ratio cut ∧ (68083/100000:ℝ)<ratioD cut ∧
      LLabel.d1 cut<17297/25000 ∧ LLabel.d2 cut< -(39003/50000:ℝ) := by
  have hU := shifted_chart_reference (outer_domain cut_mem)
    (l := (179164728671689/10^14:ℝ)) (u := (179164728671690/10^14:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [cut,W,Q0]) (by norm_num [cut,W,Q0])
  have hr := FixedReference.ratios cut_mem
    (show cut∈Icc cut cut from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ cut_mem.1 (by norm_num)
  have hL := LReference.target cut_mem
    (show cut∈Icc cut cut from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ cut_mem.1 (by norm_num)
  have hr1 := hr.1
  have hr2 := hr.2.2.1
  have hL1 := hL.2.2.2.1
  have hL2 := hL.2.2.2.2.2
  norm_num [cut,Q0] at hr1 hr2
  norm_num [LReference.firstHi,LReference.secondHi,cut,Q0] at hL1 hL2
  dsimp only [cut]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma end_trig :
    (19271/20000:ℝ)<Real.sin (13/10) ∧
      (26749/100000:ℝ)<Real.cos (13/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  constructor <;> linarith [ht.1.1,ht.2.1]

lemma cut_second {φ : ℝ} (hφ : Lower φ) : m<targetSecond cut φ := by
  have ht := lower_trig hφ
  have hr := cut_references
  have hprod := mul_lt_mul'' hr.2.1 ht.1
    (by norm_num : (0:ℝ)≤68083/100000) (by norm_num : (0:ℝ)≤19121/25000)
  dsimp [targetSecond,g,m]
  linarith [hr.2.2.2]

lemma targetSecond_antitone {φ : ℝ} (hφ : Lower φ) :
    AntitoneOn (fun B => targetSecond B φ) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (targetSecond_hasDerivAt hB φ).continuousAt.continuousWithinAt)
    (fun _ hB => targetSecond_hasDerivAt (Ioo_subset_Icc_self hB) φ)
    (fun _ hB => (targetThird_negative (Ioo_subset_Icc_self hB) hφ).le)

lemma targetSecond_lower {B φ : ℝ} (hB : B∈Icc 0 cut) (hφ : Lower φ) :
    m≤targetSecond B φ := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans cut_mem.2⟩
  exact (cut_second hφ).le.trans (targetSecond_antitone hφ hBout cut_mem hB.2)

lemma minorant_le_before_cut {B φ : ℝ} (hB : B∈Icc 0 cut) (hφ : Lower φ) :
    minorant φ≤ support B φ := by
  have hstar : star∈Icc 0 cut := by norm_num [star,cut]
  have hh := curvature_tangent (f := fun t => support t φ)
    (d := fun t => targetFirst t φ) (dd := fun t => targetSecond t φ)
    (κ := m) hB hstar
    (fun t ht => support_hasDerivAt ⟨ht.1,ht.2.trans cut_mem.2⟩ φ)
    (fun t ht => targetFirst_hasDerivAt ⟨ht.1,ht.2.trans cut_mem.2⟩ φ)
    (fun t ht => targetSecond_lower ht hφ)
  have h2 : (targetFirst star φ)^2/(2*m)=50/129*(targetFirst star φ)^2 := by
    simp only [m]
    ring
  simp only [m] at hh
  dsimp only [minorant]
  rw [h2]
  nlinarith [sq_nonneg ((129/100)*(B-star)+targetFirst star φ)]

lemma targetFirst_angle_general (B φ : ℝ) :
    HasDerivAt (targetFirst B)
      (g*(ratio B*Real.cos φ-Real.sin φ)) φ := by
  have hd := ((((Real.hasDerivAt_sin φ).const_mul (ratio B)).add
    (Real.hasDerivAt_cos φ)).const_mul g).sub_const (LLabel.d1 B)
  convert hd using 1
  funext t
  simp only [targetFirst,Pi.add_apply]

lemma targetFirst_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (targetFirst B) (Icc lowerAngle (13/10)) := by
  refine antiOn_of_hasDeriv_nonpos
    (fun φ _ => (targetFirst_angle_general B φ).continuousAt.continuousWithinAt)
    (fun φ _ => targetFirst_angle_general B φ) ?_
  intro φ hφ
  have ht := lower_trig (early_lower (Ioo_subset_Icc_self hφ))
  have hr := (outer_ratio_bounds hB).2.1
  have hm := mul_le_mul_of_nonneg_right hr ht.2.2.1
  dsimp [g]
  nlinarith [ht.1,ht.2.2.2.1]

lemma cut_first_end : (1/100:ℝ)<targetFirst cut (13/10) := by
  have hr := cut_references
  have ht := end_trig
  have hm := mul_lt_mul'' hr.1 ht.1
    (by norm_num : (0:ℝ)≤11721/25000) (by norm_num : (0:ℝ)≤19271/20000)
  dsimp [targetFirst,g]
  linarith [hr.2.2.1,ht.2]

lemma diagonal_first_end : (1/50:ℝ)<targetFirst outerDiagonal (13/10) := by
  have hL := L_first_upper
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)
  rw [targetFirst,ratio_diagonal]
  dsimp [g]
  nlinarith [end_trig.1,end_trig.2]

lemma targetFirst_end_positive {B : ℝ} (hB : B∈Icc cut outerDiagonal) :
    0<targetFirst B (13/10) := by
  have hc : ConcaveOn ℝ (Icc cut outerDiagonal)
      (fun t => targetFirst t (13/10)) :=
    concave_of_deriv2
      (fun t ht => targetFirst_hasDerivAt ⟨cut_mem.1.trans ht.1,ht.2⟩ (13/10))
      (fun t ht => targetSecond_hasDerivAt ⟨cut_mem.1.trans ht.1,ht.2⟩ (13/10))
      (fun t ht => (targetThird_negative ⟨cut_mem.1.trans ht.1,ht.2⟩
        (early_lower end_mem)).le)
  have hh := hc.min_le_of_mem_Icc
    (show cut∈Icc cut outerDiagonal from ⟨le_rfl,cut_mem.2⟩)
    (show outerDiagonal∈Icc cut outerDiagonal from ⟨cut_mem.2,le_rfl⟩) hB
  exact (lt_min (by linarith [cut_first_end])
    (by linarith [diagonal_first_end])).trans_le hh

lemma targetFirst_positive {B φ : ℝ} (hB : B∈Icc cut outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10)) : 0<targetFirst B φ := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨cut_mem.1.trans hB.1,hB.2⟩
  exact (targetFirst_end_positive hB).trans_le
    (targetFirst_angle_antitone hBout hφ end_mem hφ.2)

lemma support_monotone_after_cut {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    MonotoneOn (fun B => support B φ) (Icc cut outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (support_hasDerivAt ⟨cut_mem.1.trans hB.1,hB.2⟩ φ).continuousAt.continuousWithinAt)
    (fun _ hB => support_hasDerivAt
      ⟨cut_mem.1.trans hB.1.le,hB.2.le⟩ φ)
    (fun _ hB => (targetFirst_positive (Ioo_subset_Icc_self hB) hφ).le)

theorem minorant_le_support {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10)) : minorant φ≤ support B φ := by
  by_cases hc : B≤cut
  · exact minorant_le_before_cut ⟨hB.1,hc⟩ (early_lower hφ)
  · have hcut : cut∈Icc 0 cut := ⟨cut_mem.1,le_rfl⟩
    exact (minorant_le_before_cut hcut (early_lower hφ)).trans
      (support_monotone_after_cut hφ ⟨le_rfl,cut_mem.2⟩
        ⟨le_of_not_ge hc,hB.2⟩ (le_of_not_ge hc))

theorem original_short {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc lowerAngle (13/10)) (hb : b≤7/20)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (451/500:ℝ)<value b B φ :=
  (minorant_lower hφ).trans_le (minorant_le_support (NegativeTwo.source_mem ht) hφ)
    |>.trans (original_short_support hs ht (early_lower hφ) hb hm)

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end

section
/-!
## The original zero-source contact on the later angle interval

The curve uses the same original circle and source secondary
coordinate zero.  Its aligned endpoint is exactly the previously
constructed target with primary coordinate one.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

def parameter : ℝ := 1/2
def g : ℝ := 1303/1250
def Domain (φ : ℝ) : Prop := φ∈Icc (13/10:ℝ) (Real.pi/2)
def cost (φ : ℝ) : ℝ := value 0 (target parameter φ) φ
def first (φ : ℝ) : ℝ := 1-LLabel.d1 (target parameter φ)*bp parameter φ
def second (φ : ℝ) : ℝ :=
  -LLabel.d2 (target parameter φ)*(bp parameter φ)^2-
    LLabel.d1 (target parameter φ)*bpp parameter φ

lemma parameter_mem : parameter∈Icc (-2/5:ℝ) (1/2) := by norm_num [parameter]
lemma parameter_nonnegative : parameter∈Icc (0:ℝ) (1/2) := by norm_num [parameter]
lemma domain {φ : ℝ} (hφ : Domain φ) : SourceCurve.Domain parameter φ := by
  refine ⟨parameter_mem,?_,hφ.2⟩
  dsimp [lowerAngle]
  linarith [hφ.1,pi_hand_enclosure.2]
lemma left_mem : Domain (13/10) := ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩
lemma middle_mem : Domain (7/5) := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
lemma right_mem : Domain (Real.pi/2) := ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩

lemma quarter_target : target parameter (Real.pi/2)=zeroTarget := by
  norm_num [target,w,y,z,parameter,zeroTarget,ShortOuterOne.SameContact.arc]

lemma quarter_u : u parameter (Real.pi/2)=(3/2:ℝ) := by
  norm_num [u,z,parameter]

lemma quarter_y : y parameter (Real.pi/2)=zeroTarget+1/2 := by
  have hh := quarter_target
  simp only [target,w,Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero] at hh
  linarith

lemma quarter_w : w parameter (Real.pi/2)=zeroTarget+1/2 := by
  simpa only [w,Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero]
    using quarter_y

lemma quarter_fp : fp parameter (Real.pi/2)=1/y parameter (Real.pi/2) := by
  have hy := y_data (domain right_mem)
  have hz : z parameter (Real.pi/2)=3/2 := by norm_num [z,parameter]
  rw [hz] at hy
  have hp : y parameter (Real.pi/2)≠0 := by linarith [hy.1]
  have he : (y parameter (Real.pi/2))^2=Q0-9/4 := by linarith [hy.2]
  rw [fp,Real.sin_pi_div_two]
  generalize y parameter (Real.pi/2)=Y at hp he ⊢
  rw [show parameter=(1/2:ℝ) from rfl,div_eq_div_iff (pow_ne_zero 3 hp) hp]
  linear_combination (-Y)*he

lemma quarter_geometry :
    (129/100:ℝ)<y parameter (Real.pi/2) ∧ y parameter (Real.pi/2)<1291/1000 ∧
      fp parameter (Real.pi/2)<31/40 := by
  rw [quarter_y,quarter_fp,quarter_y]
  have hp : 0<zeroTarget+1/2 := by linarith [zeroTarget_bounds.1]
  refine ⟨by linarith [zeroTarget_bounds.1],by linarith [zeroTarget_bounds.2],?_⟩
  apply (div_lt_iff₀ hp).2
  nlinarith [zeroTarget_bounds.1]

lemma right_slope : 0<slope g parameter (Real.pi/2) := by
  have htarget := quarter_target
  have hq : (43/50:ℝ)<quotient parameter (Real.pi/2) := by
    rw [quotient,quarter_y,quarter_u]
    linarith [zeroTarget_bounds.1]
  dsimp only [SourceCurve.slope]
  rw [htarget]
  dsimp only [g]
  nlinarith [zeroTarget_labels.2.1]

lemma quarter_value : (361/400:ℝ)<cost (Real.pi/2) := by
  rw [cost,quarter_target]
  exact zero_aligned_value

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
end
end
end

section
/-!
## The two finite references on the original zero-source arc

The references at `1.3` and `1.4` use only Taylor inequalities and
the original circle square.  They provide the initial scalar reserve,
both label slopes, and the positive target curvature at `1.4`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma left_curve :
    y parameter (13/10)∈Icc (133176429/10^8:ℝ) (133176479/10^8) ∧
      u parameter (13/10)∈Icc (17664687/10^7:ℝ) (17664702/10^7) ∧
      w parameter (13/10)∈Icc (8917320/10^7:ℝ) (8917336/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (13/10)∈Icc (799/1000:ℝ) (4/5) ∧
      fp parameter (13/10)∈Icc (679/1000:ℝ) (17/25) := by
  have hh := SourceReference.curve (domain left_mem) parameter_nonnegative.1
    EarlyCut.right_trig.1 EarlyCut.right_trig.2
    (yl := (133176429/10^8:ℝ)) (yh := (133176479/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(1/2:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma middle_trig :
    Real.sin (7/5)∈Icc (98544971/10^8:ℝ) (98545074/10^8) ∧
      Real.cos (7/5)∈Icc (16996702/10^8:ℝ) (16996715/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩,
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩

lemma middle_curve :
    y parameter (7/5)∈Icc (130730107/10^8:ℝ) (130730225/10^8) ∧
      u parameter (7/5)∈Icc (16860339/10^7:ℝ) (16860371/10^7) ∧
      w parameter (7/5)∈Icc (10358014/10^7:ℝ) (10358048/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (7/5)∈Icc (8699/10000:ℝ) (87/100) ∧
      fp parameter (7/5)∈Icc (73/100:ℝ) (147/200) := by
  have hh := SourceReference.curve (domain middle_mem) parameter_nonnegative.1
    middle_trig.1 middle_trig.2
    (yl := (130730107/10^8:ℝ)) (yh := (130730225/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(1/2:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma left_target : target parameter (13/10)∈Icc 0 outerDiagonal := by
  have hw := left_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma middle_target : target parameter (7/5)∈Icc 0 outerDiagonal := by
  have hw := middle_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma left_labels : LLabel.d1 (target parameter (13/10))<659/1000 ∧
    (451/500:ℝ)<cost (13/10) := by
  have hh := left_curve
  have hb : target parameter (13/10)∈Icc (3917320/10^7:ℝ) (3917336/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hu : U (target parameter (13/10))∈Icc (17664687/10^7:ℝ) (17664702/10^7) := by
    rw [target_U (domain left_mem) left_target]
    exact hh.2.1
  have hL := LReference.target left_target hb hu (by norm_num) (by norm_num)
  have hfirst := hL.2.2.2.1
  have hvalue := hL.2.1
  norm_num [LReference.firstHi,LReference.valueHi] at hfirst hvalue
  constructor
  · linarith
  · dsimp [cost,value]
    linarith [V_zero_bounds.1]

lemma middle_labels : LLabel.d1 (target parameter (7/5))<659/1000 ∧
    (161/1000:ℝ)<LLabel.d2 (target parameter (7/5)) := by
  have hh := middle_curve
  have hb : target parameter (7/5)∈Icc (5358014/10^7:ℝ) (5358048/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hu : U (target parameter (7/5))∈Icc (16860339/10^7:ℝ) (16860371/10^7) := by
    rw [target_U (domain middle_mem) middle_target]
    exact hh.2.1
  have hL := LReference.target middle_target hb hu (by norm_num) (by norm_num)
  have hfirst := hL.2.2.2.1
  have hsecond := hL.2.2.2.2.1
  norm_num [LReference.firstHi,LReference.secondLo,Q0] at hfirst hsecond
  exact ⟨by linarith,by linarith⟩

lemma quarter_curvature : LLabel.d2 zeroTarget<(21/10:ℝ) := by
  have hL := LReference.target zeroTarget_mem
    ⟨zeroTarget_bounds.1.le,zeroTarget_bounds.2.le⟩
    (show U zeroTarget∈Icc (3/2) (3/2) by rw [zeroTarget_U]; exact ⟨le_rfl,le_rfl⟩)
    (by norm_num) (by norm_num)
  have hh := hL.2.2.2.2.2
  norm_num [LReference.secondHi,Q0] at hh
  linarith

lemma left_slope : 0<slope g parameter (13/10) := by
  have hh := left_curve
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  dsimp only [SourceCurve.slope,quotient,g]
  norm_num at hq
  nlinarith [hq.1,left_labels.1]

lemma middle_speed : bp parameter (7/5)<(1467/1000:ℝ) := by
  have hh := middle_curve
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter (7/5) := by linarith [hh.2.2.2.1.1]
  have hp := mul_le_mul hh.2.1.2 hh.2.2.2.1.2 hf0 (by norm_num : (0:ℝ)≤16860371/10^7)
  dsimp [bp]
  norm_num at hp
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
end
end
end

section
/-!
## Whole-arc bounds for the original zero-source contact

All coordinate and velocity bounds are consequences of the actual
endpoint values and monotonicity.  The target-label bounds reuse
the already proved lower reference at `0.252` and the exact aligned
target with primary coordinate one.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma geometry {φ : ℝ} (hφ : Domain φ) :
    u parameter φ∈Icc (3/2:ℝ) (1767/1000) ∧
      w parameter φ∈Icc (891/1000:ℝ) (1291/1000) ∧
      y parameter φ∈Icc (129/100:ℝ) (333/250) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter φ∈Icc (799/1000:ℝ) 1 ∧
      fp parameter φ∈Icc (679/1000:ℝ) (31/40) := by
  have hp := (domain hφ).2
  have hl := (domain left_mem).2
  have hr := (domain right_mem).2
  have hul := u_antitone parameter_mem hp hr hφ.2
  have huh := u_antitone parameter_mem hl hp hφ.1
  have hyl := y_antitone parameter_mem hp hr hφ.2
  have hyh := y_antitone parameter_mem hl hp hφ.1
  have hwl := target_monotone parameter_mem hl hp hφ.1
  have hwh := target_monotone parameter_mem hp hr hφ.2
  dsimp [target] at hwl hwh
  have hfl := f_monotone parameter_mem hl hp hφ.1
  have hfh := (f_bounds (domain hφ)).2
  have hfpl := fp_monotone parameter_nonnegative hl hp hφ.1
  have hfph := fp_monotone parameter_nonnegative hp hr hφ.2
  rw [quarter_u] at hul
  rw [quarter_w] at hwh
  have hh := left_curve
  have hq := quarter_geometry
  refine ⟨⟨hul,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,hfh⟩,⟨?_,?_⟩⟩ <;>
    linarith [hh.1.1,hh.1.2,hh.2.1.1,hh.2.1.2,hh.2.2.1.1,hh.2.2.1.2,
      hh.2.2.2.1.1,hh.2.2.2.2.1,hq.1,hq.2.2,zeroTarget_bounds.2]

lemma target_data {φ : ℝ} (hφ : Domain φ) :
    target parameter φ∈Icc (391/1000:ℝ) zeroTarget := by
  have hh := target_monotone parameter_mem (domain hφ).2 (domain right_mem).2 hφ.2
  rw [quarter_target] at hh
  have hw := (geometry hφ).2.1.1
  exact ⟨by dsimp [target]; linarith,hh⟩

lemma target_mem {φ : ℝ} (hφ : Domain φ) : target parameter φ∈Icc 0 outerDiagonal :=
  ⟨by linarith [(target_data hφ).1],(target_data hφ).2.trans zeroTarget_mem.2⟩

lemma velocities {φ : ℝ} (hφ : Domain φ) :
    (3/2:ℝ)*(799/1000)≤bp parameter φ ∧
      bpp parameter φ∈Icc (-(273/1000:ℝ)) (137/100) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hu0 : 0≤u parameter φ := by linarith [hu.1]
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have hf2 : (SecondWord.PositiveThree.SourceCurve.f parameter φ)^2≤1 := by nlinarith [hf.2]
  have htermhi := mul_le_mul hw.2 hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤1291/1000)
  have htermlo := mul_nonneg hw0 (sq_nonneg (SecondWord.PositiveThree.SourceCurve.f parameter φ))
  have hupLo := mul_le_mul hu.1 hfp.1 (by norm_num : (0:ℝ)≤679/1000) hu0
  have hupHi := mul_le_mul hu.2 hfp.2 hfp0 (by norm_num : (0:ℝ)≤1767/1000)
  have hbp := mul_le_mul hu.1 hf.1 (by norm_num : (0:ℝ)≤799/1000) hu0
  dsimp [bp,bpp]
  exact ⟨hbp,⟨by nlinarith,by nlinarith⟩⟩

lemma label_curvature {φ : ℝ} (hφ : Domain φ) :
    LLabel.d2 (target parameter φ)∈Icc (-(567/500:ℝ)) (21/10) ∧
      (383/100:ℝ)<LLabel.d3 (target parameter φ) := by
  have ht := target_mem hφ
  have hlo : (63/250:ℝ)≤target parameter φ := by linarith [(target_data hφ).1]
  have hlow := L_second_monotone EarlyCut.target_left_mem ht hlo
  have hhigh := L_second_monotone ht zeroTarget_mem (target_data hφ).2
  have hthird := L_third_monotone EarlyCut.target_left_mem ht hlo
  exact ⟨⟨by linarith [EarlyCut.target_left_curvature.1],by linarith [quarter_curvature]⟩,
    EarlyCut.target_left_curvature.2.trans_le hthird⟩

lemma cost_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt cost (first φ) φ := by
  have hd := ((hasDerivAt_id φ).add_const (V 0)).sub
    ((LLabel.outer_hasDerivAt (outer_domain (target_mem hφ))).comp φ
      (target_hasDerivAt (domain hφ)))
  convert hd using 1
  · funext t
    simp only [cost,value,L,Pi.sub_apply,Function.comp_apply,id]
  · simp only [first]

lemma first_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt first (second φ) φ := by
  have hd := (((LLabel.d1_hasDerivAt (outer_domain (target_mem hφ))).comp φ
    (target_hasDerivAt (domain hφ))).mul (bp_hasDerivAt (domain hφ))).const_sub 1
  convert hd using 1
  · funext t
    simp only [first,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

private lemma div_upper {n d nh dl : ℝ} (hn : n≤nh) (hd : dl≤d)
    (hnh : 0≤nh) (hdl : 0<dl) : n/d≤nh/dl := by
  exact (div_le_div_iff₀ (hdl.trans_le hd) hdl).2
    (mul_le_mul hn hd hdl.le hnh)

lemma quotient_curvature {φ : ℝ} (hφ : Domain φ) :
    quotientSecond parameter φ<(179/50:ℝ) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hy := hh.2.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hy0 : 0≤y parameter φ := by linarith [hy.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have ht := lower_trig (domain hφ).2
  have hs0 : 0≤Real.sin φ := by linarith [ht.1]
  have hf2 : (SecondWord.PositiveThree.SourceCurve.f parameter φ)^2≤1 := by nlinarith [hf.2]
  have hw2 := pow_le_pow_left₀ hw0 hw.2 2
  have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 3
  have hn1 := mul_le_mul (z_bounds (domain hφ)).2 ht.2.1 hs0 (by norm_num : (0:ℝ)≤3/2)
  have hd1 := mul_le_mul hy.1 hu.1 (by norm_num : (0:ℝ)≤3/2) hy0
  have ht1 := div_upper hn1 hd1 (by norm_num) (by norm_num)
  have hn2 := mul_le_mul hy.2 hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤333/250)
  have ht2 := div_upper hn2 hu.1 (by norm_num) (by norm_num)
  have hyw := mul_le_mul hy.2 hw.2 hw0 (by norm_num : (0:ℝ)≤333/250)
  have hn3 := mul_le_mul hyw hfp.2 hfp0
    (by norm_num : (0:ℝ)≤(333/250)*(1291/1000))
  have ht3 := div_upper hn3 hu2 (by norm_num) (by norm_num)
  have hyw2 := mul_le_mul (mul_le_mul_of_nonneg_left hy.2 (by norm_num : (0:ℝ)≤2))
    hw2 (sq_nonneg _) (by norm_num : (0:ℝ)≤2*(333/250))
  have hn4 := mul_le_mul hyw2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤2*(333/250)*(1291/1000)^2)
  have ht4 := div_upper hn4 hu3 (by norm_num) (by norm_num)
  have hsum := quotientSecond_le (domain hφ)
  dsimp [quotientUpper] at hsum
  norm_num at ht1 ht2 ht3 ht4
  linarith

lemma opposite_product_upper {x y : ℝ}
    (hx : x∈Icc (-(567/500:ℝ)) (21/10))
    (hy : y∈Icc (-(273/1000:ℝ)) (137/100)) : -x*y<(777/500:ℝ) := by
  by_cases hxs : 0≤x
  · by_cases hys : 0≤y
    · nlinarith [mul_nonneg hxs hys]
    · have hh := mul_le_mul hx.2 (show -y≤273/1000 by linarith [hy.1])
        (neg_nonneg.mpr (le_of_not_ge hys)) (by norm_num : (0:ℝ)≤21/10)
      nlinarith
  · by_cases hys : 0≤y
    · have hh := mul_le_mul (show -x≤567/500 by linarith [hx.1]) hy.2 hys
        (by norm_num : (0:ℝ)≤567/500)
      nlinarith
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hxs) (le_of_not_ge hys)]

lemma slope_curvature {φ : ℝ} (hφ : Domain φ) :
    slopeSecond g parameter φ< -(21/100:ℝ) := by
  have hq := mul_lt_mul_of_pos_left (quotient_curvature hφ)
    (show 0<g by norm_num [g])
  have hvel := velocities hφ
  have hlabel := label_curvature hφ
  have hbp2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(3/2)*(799/1000)) hvel.1 2
  have hthird := mul_le_mul hlabel.2.le hbp2
    (by norm_num : (0:ℝ)≤((3/2)*(799/1000))^2)
    (by linarith [hlabel.2] : 0≤LLabel.d3 (target parameter φ))
  have hlast := opposite_product_upper hlabel.1 hvel.2
  dsimp [slopeSecond,g] at *
  nlinarith

lemma slope_concave : ConcaveOn ℝ (Icc (13/10) (Real.pi/2)) (slope g parameter) :=
  concave_of_deriv2
    (fun φ hφ => slope_hasDerivAt g (domain hφ) (target_mem hφ))
    (fun φ hφ => slopeFirst_hasDerivAt g (domain hφ) (target_mem hφ))
    (fun φ hφ => by linarith [slope_curvature hφ])

theorem slope_positive {φ : ℝ} (hφ : Domain φ) : 0<slope g parameter φ :=
  (lt_min left_slope right_slope).trans_le
    (slope_concave.min_le_of_mem_Icc left_mem right_mem hφ)

theorem original_derivative {φ : ℝ} (hφ : Domain φ) :
    0<FirstContact.first (target parameter φ) φ := by
  have hg : g≤VLabel.d1 (1/2-parameter) := by
    norm_num [parameter,g]
    exact V_zero_first_lower.le
  exact (slope_positive hφ).trans_le
    (original_slope_of_lower (domain hφ) (target_mem hφ) hg)

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
end
end
end
