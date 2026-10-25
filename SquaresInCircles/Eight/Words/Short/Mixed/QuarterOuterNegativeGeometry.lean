module

public import SquaresInCircles.Eight.Words.Second.Mixed.CoreCorner
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeData

/-!
# Eight squares: whole lower-angle geometry of the unchanged core corner

The continued contact height stays between 1.32 and
1.7 on the full early rectangle. The same original circle chart includes
the side join and the diagonal, with no strict-owner convention.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry Arithmetic Reference

def lowerAngles : Set ℝ := Icc lowerAngle (Real.pi/2)
def earlyAngles : Set ℝ := Icc lowerAngle (6/5)
def contactPrimary (B φ : ℝ) : ℝ :=
  1/2+(SecondWord.MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def contactTangent (B φ : ℝ) : ℝ := SecondWord.MixedCorner.w B*Real.cos φ+Real.sin φ
def contactSpeed (B φ : ℝ) : ℝ :=
  (SecondWord.MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ

theorem lower_parameter {φ : ℝ} (hφ : φ∈lowerAngles) :
    Real.pi/2-φ∈Icc 0 (7/10) ∧ φ=angle false (Real.pi/2-φ) := by
  constructor
  · constructor <;> dsimp [lowerAngle,lowerAngles] at hφ <;> linarith [hφ.1,hφ.2]
  · dsimp [angle,direction]; ring
theorem lower_trig {φ : ℝ} (hφ : φ∈lowerAngles) :
    (191/250:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<129/200 := by
  obtain ⟨hx,he⟩ := lower_parameter hφ
  have ht := positive_trig hx
  rw [he,angle_sin,angle_cos]
  dsimp [direction]
  refine ⟨by linarith [ht.1],Real.cos_le_one _,by linarith [ht.2.2.1],by linarith [ht.2.2.2.1]⟩
theorem early_subset : earlyAngles⊆lowerAngles := by
  intro φ hφ
  exact ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
theorem early_left : lowerAngle∈earlyAngles := by
  exact ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
theorem early_right : (6/5:ℝ)∈earlyAngles := by
  exact ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩

theorem early_cosine {φ : ℝ} (hφ : φ∈earlyAngles) : (181/500:ℝ)<Real.cos φ := by
  have hm : AntitoneOn Real.cos lowerAngles :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt)
      (fun x _ => Real.hasDerivAt_cos x)
      (fun x hx => by linarith [(lower_trig (Ioo_subset_Icc_self hx)).1])
  have hcmp := hm (early_subset hφ) (early_subset early_right) hφ.2
  have href : (181/500:ℝ)<Real.cos (6/5) := by
    have h := (cosine (by norm_num : (0:ℝ)≤6/5)).mem.1
    have hb : (181/500:ℝ)<(cosine (by norm_num : (0:ℝ)≤6/5)).lo := by mixed_fixed
    exact hb.trans_le h
  linarith

theorem contact_height_range {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HeightRange (contactPrimary B φ+1/2) := by
  have ht := lower_trig (early_subset hφ)
  have hc := early_cosine hφ
  have ha := CoreAngleEndpoint.state_bounds (SecondWord.MixedCorner.state hB)
  have hchart := SecondWord.MixedCorner.chart_bounds hB
  have haL : (529/500:ℝ)<SecondWord.MixedCorner.a B+1/2 := by
    dsimp [SecondWord.MixedCorner.a]
    linarith [hchart.1,CoreAngleEndpoint.diagonal_bounds.1]
  have haU : SecondWord.MixedCorner.a B+1/2≤13/12 := by linarith [ha.2.1]
  have hBb : 0≤B-1/2 ∧ B-1/2<59/1000 :=
    ⟨sub_nonneg.mpr hB.1,by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]⟩
  have hAcL := mul_lt_mul_of_pos_right haL (show 0<Real.cos φ by linarith)
  have hAcU := mul_le_mul_of_nonneg_right haU ht.2.2.1
  have hBsL := mul_nonneg hBb.1 (show 0≤Real.sin φ by linarith [ht.1])
  have hBsU := mul_le_mul_of_nonneg_left ht.2.1 hBb.1
  dsimp [HeightRange,contactPrimary]
  constructor <;> nlinarith

theorem contact_domain {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) (hφ : φ∈earlyAngles) :
    SourceDomain (contactPrimary B φ) := by
  have h := height_source_domain (contact_height_range hB hφ)
  simpa using h

theorem contactPrimary_hasDerivAt_B {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (fun t => contactPrimary t φ) (-contactTangent B φ) B := by
  have h := ((((SecondWord.MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const
    (Real.cos φ)).const_add (1/2)).sub
      (((hasDerivAt_id' B).sub_const (1/2)).mul_const (Real.sin φ))
  exact h.congr_deriv (by simp only [contactTangent]; ring)
theorem contactTangent_hasDerivAt_B {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (fun t => contactTangent t φ)
      ((1+(SecondWord.MixedCorner.w B)^2)*Real.cos φ/SecondWord.MixedCorner.z B) B := by
  have h := ((SecondWord.MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).add_const
    (Real.sin φ)
  exact h.congr_deriv (by ring)

theorem actual_height (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (_hB : B∈SecondWord.MixedCorner.domain) (hA : A=SecondWord.MixedCorner.a B) (hφ : φ∈earlyAngles)
    (hm : sourcePrimary r a b A B φ) : contactPrimary B φ≤a := by
  have ht := lower_trig (early_subset hφ)
  rw [primary_separator r hr] at hm
  rw [pairWidth,abs_of_nonneg (by linarith [ht.1]),abs_of_nonneg ht.2.2.1,hA] at hm
  dsimp [contactPrimary]
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
