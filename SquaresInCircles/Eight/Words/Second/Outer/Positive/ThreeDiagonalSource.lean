module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeDiagonalReferences

/-!
# Eight squares: the entire original source-diagonal boundary

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
