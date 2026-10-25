module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeOuterSupports
public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeOuterHeight
public import SquaresInCircles.Eight.TableFree.SecondMixedCoreCorner

/-!
# The complete negative-outer mixed corner contact

The primary separator gives a lower bound on the original outer
height.  The resulting contact cost is concave across the complete
core corner and increases in the complete early angle range.  Two
initial endpoint references therefore bound the whole rectangle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig)
open NegativeThree

def earlyAngles : Set ℝ := Icc lowerAngle (549/500)
def contactPrimary (B φ : ℝ) : ℝ :=
  1/2+(MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def contactTangent (B φ : ℝ) : ℝ := MixedCorner.w B*Real.cos φ+Real.sin φ
def contactSpeed (B φ : ℝ) : ℝ :=
  (MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ
def cornerCost (B φ : ℝ) : ℝ := φ+TPrimaryLabel.outer (contactPrimary B φ)+c₀+g*B
def cornerD (B φ : ℝ) : ℝ := -TPrimaryLabel.d1 (contactPrimary B φ)*contactTangent B φ+g
def cornerDD (B φ : ℝ) : ℝ :=
  TPrimaryLabel.d2 (contactPrimary B φ)*(contactTangent B φ)^2-
    TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ*(1+(MixedCorner.w B)^2)/MixedCorner.z B

lemma early_subset : earlyAngles⊆Icc lowerAngle (Real.pi/2) :=
  fun φ hφ => ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma early_cosine {φ : ℝ} (hφ : φ∈earlyAngles) : (91/200:ℝ)<Real.cos φ := by
  have hm : AntitoneOn Real.cos (Icc lowerAngle (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt)
      (fun x _ => Real.hasDerivAt_cos x)
      (fun x hx => by linarith [(lower_trig (Ioo_subset_Icc_self hx)).1])
  have hh := hm (early_subset hφ)
    (early_subset (show (549/500:ℝ)∈earlyAngles by
      constructor
      · dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]
      · exact le_rfl)) hφ.2
  have hc := HighOrderTaylor.C14_le_cos (x := (549/500:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hc
  linarith

lemma contact_range {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    contactPrimary B φ∈primaryRange := by
  have htr := lower_trig (early_subset hφ)
  have hcos := early_cosine hφ
  have hb := MixedCorner.chart_bounds hB
  have haL : (279/500:ℝ)<MixedCorner.a B := by
    dsimp [MixedCorner.a]
    linarith [hb.1,CoreAngleEndpoint.diagonal_bounds.1]
  have haU : MixedCorner.a B≤(7/12:ℝ) := by dsimp [MixedCorner.a]; linarith [hb.2.1]
  have hAcL := mul_nonneg (show 0≤MixedCorner.a B+1/2-529/500 by linarith) htr.2.2.1
  have hAcU := mul_nonneg (sub_nonneg.mpr haU) htr.2.2.1
  have hBs := mul_nonneg (sub_nonneg.mpr hB.1) (show 0≤Real.sin φ by linarith [htr.1])
  have hBsU := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) (sub_nonneg.mpr hB.1)
  have hBhi : B-1/2<(59/1000:ℝ) := by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]
  dsimp [primaryRange,contactPrimary]
  constructor <;> nlinarith [htr.2.2.2.1]

lemma primary_second_reference : TPrimaryLabel.d2 (6/5)<(803/250:ℝ) := by
  have hh := TPrimaryLabel.second_chart_reference
    (primary_domain OppositeThree.primary_six_fifths_mem)
    (l := (101271911/100000000:ℝ)) (u := (25317978/25000000:ℝ))
    (dlo := (3:ℝ)) (dhi := (803/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_second_upper {a : ℝ} (ha : a∈primaryRange) : TPrimaryLabel.d2 a<(803/250:ℝ) := by
  have hm : MonotoneOn TPrimaryLabel.d2 primaryRange :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (TPrimaryLabel.d2_hasDerivAt (primary_domain (primaryRange_subset hx))).continuousAt.continuousWithinAt)
      (fun x hx => TPrimaryLabel.d2_hasDerivAt (primary_domain (primaryRange_subset (Ioo_subset_Icc_self hx))))
      (fun x hx => (primary_third_positive (primaryRange_subset (Ioo_subset_Icc_self hx))).le)
  exact (hm ha (by norm_num [primaryRange]) ha.2).trans_lt primary_second_reference

lemma contactPrimary_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun t => contactPrimary t φ) (-contactTangent B φ) B := by
  refine ((((MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const (Real.cos φ)).const_add
    (1/2)).sub (((hasDerivAt_id B).sub_const (1/2)).mul_const (Real.sin φ)) |>.congr_deriv ?_
  simp only [contactTangent]
  ring


lemma contactTangent_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun t => contactTangent t φ)
      ((1+(MixedCorner.w B)^2)*Real.cos φ/MixedCorner.z B) B := by
  refine ((MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).add_const (Real.sin φ)
    |>.congr_deriv ?_
  ring


lemma cornerCost_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (fun t => cornerCost t φ) (cornerD B φ) B := by
  refine ((((TPrimaryLabel.outer_hasDerivAt
    (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp B
      (contactPrimary_hasDerivAt_B hB)).const_add φ).add_const c₀).add
        ((hasDerivAt_id B).const_mul g) |>.congr_deriv ?_
  simp only [cornerD]
  ring


lemma cornerD_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (fun t => cornerD t φ) (cornerDD B φ) B := by
  refine ((((TPrimaryLabel.d1_hasDerivAt
    (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp B
      (contactPrimary_hasDerivAt_B hB)).neg.mul (contactTangent_hasDerivAt_B hB)).add_const g)
    |>.congr_deriv ?_
  simp only [cornerDD,Pi.neg_apply,Function.comp_apply]
  ring


lemma cornerDD_negative {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    cornerDD B φ<0 := by
  have ha := contact_range hB hφ
  have hm := primary_first_lower (primaryRange_subset ha)
  have hsecond := primary_second_upper ha
  have hc := early_cosine hφ
  have hz := MixedCorner.z_positive hB
  have hzU := (MixedCorner.chart_bounds hB).2.1
  have hnorm : (contactTangent B φ)^2≤1+(MixedCorner.w B)^2 := by
    have he : (contactTangent B φ)^2+
        (Real.cos φ-MixedCorner.w B*Real.sin φ)^2=1+(MixedCorner.w B)^2 := by
      dsimp [contactTangent]
      linear_combination (1+(MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (Real.cos φ-MixedCorner.w B*Real.sin φ)]
  have hprod := (mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<19/25)).trans
    (mul_lt_mul_of_pos_right hm (by linarith [hc] : 0<Real.cos φ))
  have hpay : (803/250:ℝ)<TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ/MixedCorner.z B := by
    apply (lt_div_iff₀ hz).2
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hsecond.le (sq_nonneg (contactTangent B φ))
  have hnext := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ)≤803/250)
  have hstrict := mul_lt_mul_of_pos_right hpay
    (show 0<1+(MixedCorner.w B)^2 by positivity)
  have heq : TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ/MixedCorner.z B*
      (1+(MixedCorner.w B)^2)=TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ*
      (1+(MixedCorner.w B)^2)/MixedCorner.z B := by ring
  dsimp only [cornerDD]
  linarith


lemma contactPrimary_hasDerivAt_φ (B φ : ℝ) :
    HasDerivAt (contactPrimary B) (-contactSpeed B φ) φ := by
  refine (((Real.hasDerivAt_cos φ).const_mul (MixedCorner.a B+1/2)).const_add (1/2)).sub
    ((Real.hasDerivAt_sin φ).const_mul (B-1/2)) |>.congr_deriv ?_
  simp only [contactSpeed]
  ring


lemma contactSpeed_eq {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    contactSpeed B φ=coreSpeed ((MixedCorner.a B+1/2)^2+(B-1/2)^2) (contactPrimary B φ) := by
  have ht := lower_trig (early_subset hφ)
  have ha := (CoreAngleEndpoint.state_bounds (MixedCorner.state hB)).1
  have hp : 0<contactSpeed B φ := by
    dsimp [contactSpeed]
    have hfirst := mul_pos (show 0<MixedCorner.a B+1/2 by linarith) (show 0<Real.sin φ by linarith [ht.1])
    have hsecond := mul_nonneg (sub_nonneg.mpr hB.1) ht.2.2.1
    linarith
  have hs := speed_data (MixedCorner.endpoint_mass hB) (contact_range hB hφ)
  have he : (contactSpeed B φ)^2+(contactPrimary B φ-1/2)^2=
      (MixedCorner.a B+1/2)^2+(B-1/2)^2 := by
    dsimp [contactSpeed,contactPrimary]
    linear_combination ((MixedCorner.a B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq φ)
  nlinarith [hs.1,hs.2.1]

lemma cornerCost_hasDerivAt_φ {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (cornerCost B) (1-TPrimaryLabel.d1 (contactPrimary B φ)*contactSpeed B φ) φ := by
  refine (((hasDerivAt_id φ).add
    ((TPrimaryLabel.outer_hasDerivAt (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp φ
      (contactPrimary_hasDerivAt_φ B φ))).add_const c₀).add_const (g*B) |>.congr_deriv ?_
  ring


lemma corner_angle_monotone {B : ℝ} (hB : B∈MixedCorner.domain) :
    MonotoneOn (cornerCost B) earlyAngles := by
  apply monoOn_of_hasDeriv_nonneg
    (fun φ hφ => (cornerCost_hasDerivAt_φ hB hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => cornerCost_hasDerivAt_φ hB (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have h := Ioo_subset_Icc_self hφ
  have hh := speedProduct_upper (MixedCorner.endpoint_mass hB) (contact_range hB h)
  rw [contactSpeed_eq hB h]
  dsimp [speedProduct] at hh
  linarith

lemma initial_value_references :
    (-107733/250000:ℝ)<TPrimaryLabel.outer (119789/100000) ∧
      (-489529/1000000:ℝ)<TPrimaryLabel.outer (11371/10000) := by
  have hjoin : (119789/100000:ℝ)∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩
  have hdiag : (11371/10000:ℝ)∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩
  have hj := shifted_chart_reference (primary_domain hjoin)
    (l := (101625269/100000000:ℝ)) (u := (10162527/10000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := shifted_chart_reference (primary_domain hdiag)
    (l := (111153209/100000000:ℝ)) (u := (11115321/10000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hj hd
  norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,RoleLabel.outer,RoleLabel.eval,Q0]
  constructor <;> nlinarith

lemma initial_cost_references :
    (9196/10000:ℝ)<cornerCost (1/2) lowerAngle ∧
      (8977/10000:ℝ)<cornerCost CoreAngleEndpoint.diagonal lowerAngle := by
  have hleft : lowerAngle∈earlyAngles :=
    ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
  have hj : (1/2:ℝ)∈MixedCorner.domain :=
    ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
  have hd : CoreAngleEndpoint.diagonal∈MixedCorner.domain :=
    ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩
  have ht := MixedAffine.left_trig
  have hjcut : (119789/100000:ℝ)≤contactPrimary (1/2) lowerAngle := by
    dsimp [contactPrimary]
    rw [MixedCorner.join]
    nlinarith [ht.2.2.1]
  have hdcut : (11371/10000:ℝ)≤contactPrimary CoreAngleEndpoint.diagonal lowerAngle := by
    have hl := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-55892556/100000000 by
      linarith [CoreAngleEndpoint.diagonal_bounds.1]) (show 0≤Real.cos lowerAngle by linarith [ht.2.2.1])
    have hu := mul_nonneg (show 0≤55892557/100000000-CoreAngleEndpoint.diagonal by
      linarith [CoreAngleEndpoint.diagonal_bounds.2]) (show 0≤Real.sin lowerAngle by linarith [ht.1])
    dsimp [contactPrimary]
    rw [MixedCorner.diagonal]
    nlinarith [ht.2.2.1,ht.2.1]
  have hmj := primary_monotone
    (show (119789/100000:ℝ)∈Icc outerDiagonal outerAxial from
      ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩)
    (primaryRange_subset (contact_range hj hleft)) hjcut
  have hmd := primary_monotone
    (show (11371/10000:ℝ)∈Icc outerDiagonal outerAxial from
      ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩)
    (primaryRange_subset (contact_range hd hleft)) hdcut
  have hla : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [cornerCost,g,c₀]
  constructor <;> linarith [initial_value_references.1,initial_value_references.2,
    CoreAngleEndpoint.diagonal_bounds.1,pi_hand_enclosure.1]


theorem corner_lower {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    (8977/10000:ℝ)<cornerCost B φ := by
  have hleft : lowerAngle∈earlyAngles :=
    ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
  have hc : ConcaveOn ℝ MixedCorner.domain (fun t => cornerCost t lowerAngle) :=
    concave_of_deriv2
      (fun t ht => cornerCost_hasDerivAt_B ht hleft)
      (fun t ht => cornerD_hasDerivAt_B ht hleft)
      (fun t ht => (cornerDD_negative ht hleft).le)
  have hl := concave_gt_of_endpoints hc hB
    (show (8977/10000:ℝ)<cornerCost (1/2) lowerAngle by linarith [initial_cost_references.1])
    initial_cost_references.2
  exact hl.trans_le (corner_angle_monotone hB hleft hφ hφ.1)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
