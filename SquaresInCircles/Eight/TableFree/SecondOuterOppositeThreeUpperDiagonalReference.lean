module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperDiagonalData
public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference

/-!
# One rational source reference on the target diagonal

The inverse angle is bounded from below by a direct trigonometric
contact comparison.  All radical and derivative bounds concern this
single rational source coordinate.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def reference : ℝ := 542853/100000000
def referenceAngle : ℝ := 4521/40000

lemma reference_mem : reference∈Icc 0 (1/10) := by norm_num [reference]

lemma reference_U : (7652599/4000000:ℝ)<U reference ∧
    U reference<23914372/12500000 := by
  exact shifted_chart_reference (outer_domain (early_domain reference_mem))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0])
    (by norm_num [reference,W,Q0])

lemma reference_q : (3404064/3125000:ℝ)<NegativeTwo.Inverse.q (U reference) ∧
    NegativeTwo.Inverse.q (U reference)<2178601/2000000 := by
  dsimp [NegativeTwo.Inverse.q]
  norm_num [Q0]
  constructor <;> linarith [reference_U.1,reference_U.2]

lemma reference_z : (19960703/50000000:ℝ)<z ∧ z<39921407/100000000 := by
  dsimp [z,OppositeTwo.TargetRatio.z]
  constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]

lemma reference_speed : (19286561/20000000:ℝ)<speed reference ∧
    speed reference<12054101/12500000 := by
  have hd := OppositeTwo.PrimaryInverse.data (early_domain reference_mem) z_mem
  have hvp : 0<speed reference := hd.2.2.1
  have hvn : z^2+(speed reference)^2=NegativeTwo.Inverse.q (U reference) := hd.2.2.2
  constructor <;> nlinarith [reference_q.1,reference_q.2,reference_z.1,reference_z.2,hvp,hvn]

lemma reference_ratio : (26418659/100000000:ℝ)<ratio reference ∧
    ratio reference<26418661/100000000 := by
  have hu := U_positive (outer_domain (early_domain reference_mem))
  change (26418659/100000000:ℝ)<(reference+1/2)/U reference ∧
    (reference+1/2)/U reference<26418661/100000000
  constructor
  · apply (lt_div_iff₀ hu).2
    norm_num [reference]
    nlinarith [reference_U.2]
  · apply (div_lt_iff₀ hu).2
    norm_num [reference]
    nlinarith [reference_U.1]

lemma reference_factor : (12010885/12500000:ℝ)<NegativeTwo.Inverse.factor (U reference) ∧
    NegativeTwo.Inverse.factor (U reference)<9608711/10000000 := by
  have hu := U_positive (outer_domain (early_domain reference_mem))
  have hq : 0<NegativeTwo.Inverse.q (U reference) := by linarith [reference_q.1]
  have hlo := mul_lt_mul reference_U.1 reference_q.1 (by norm_num) hu.le
  have hhi := mul_lt_mul reference_U.2 reference_q.2 hq (by norm_num)
  dsimp [NegativeTwo.Inverse.factor]
  constructor
  · apply (lt_div_iff₀ (mul_pos hu hq)).2
    norm_num [Q0] at *
    nlinarith [reference_U.2]
  · apply (div_lt_iff₀ (mul_pos hu hq)).2
    norm_num [Q0] at *
    nlinarith [reference_U.1]

lemma reference_correction :
    (502011/5000000:ℝ)<z*ratio reference/(NegativeTwo.Inverse.q (U reference)*speed reference) ∧
    z*ratio reference/(NegativeTwo.Inverse.q (U reference)*speed reference)<502013/5000000 := by
  have hq : 0<NegativeTwo.Inverse.q (U reference) := by linarith [reference_q.1]
  have hv : 0<speed reference := by linarith [reference_speed.1]
  have hr : 0≤ratio reference := by linarith [reference_ratio.1]
  have hnlo := mul_lt_mul reference_z.1 reference_ratio.1 (by norm_num)
    (by linarith [reference_z.1] : 0≤z)
  have hnhi := mul_lt_mul reference_z.2 reference_ratio.2
    (by linarith [reference_ratio.1] : 0<ratio reference) (by norm_num)
  have hdlo := mul_lt_mul reference_q.1 reference_speed.1 (by norm_num) hq.le
  have hdhi := mul_lt_mul reference_q.2 reference_speed.2 hv (by norm_num)
  constructor
  · apply (lt_div_iff₀ (mul_pos hq hv)).2
    norm_num at hnlo hdhi
    nlinarith
  · apply (div_lt_iff₀ (mul_pos hq hv)).2
    norm_num at hnhi hdlo
    nlinarith

lemma reference_T : T reference<(22481/1000000:ℝ) ∧
    (13265915/12500000:ℝ)<TLabel.d1 reference ∧
      TLabel.d1 reference<1326592/1250000 := by
  have hh := FixedReference.target (early_domain reference_mem)
    (show reference∈Icc reference reference from ⟨le_rfl,le_rfl⟩)
    ⟨reference_U.1.le,reference_U.2.le⟩
    (by norm_num [reference]) (by norm_num)
  norm_num [FixedReference.valueHi,FixedReference.firstLo,FixedReference.firstHi,
    reference,Q0] at hh
  exact ⟨by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2.1]⟩

lemma reference_first : |first reference|<(1/1000000:ℝ) := by
  have hF := reference_factor
  have hc := reference_correction
  have hT := reference_T
  rw [abs_lt]
  dsimp [first]
  rw [OppositeTwo.TargetRatio.F_formula]
  constructor <;> linarith

lemma reference_contact_before : outerDiagonal<upperPrimary reference referenceAngle := by
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have hs := sin_le_sin9 hx.1
  have hc := cos10_le_cos hx.1
  have ht := positive_trig hx
  have hu : arc reference-1/2<(11414372/12500000:ℝ) := by
    have hh := reference_U.2
    dsimp [U] at hh
    linarith
  have hup : 0≤arc reference-1/2 := by
    have hh := reference_U.1
    dsimp [U] at hh
    linarith
  have hproduct := mul_le_mul hu.le hs ht.2.2.1 (by norm_num)
  norm_num [referenceAngle,sin9,sin7,cos10,cos8] at hs hc hproduct
  dsimp [upperPrimary,reference,referenceAngle]
  nlinarith [diagonal_fine.2]

lemma reference_angle : referenceAngle<UpperInverse.X z reference := by
  have hzero : 0≤UpperInverse.X z reference :=
    UpperInverse.X_nonnegative (early_domain reference_mem) (by
      dsimp [z,OppositeTwo.TargetRatio.z,W,reference]
      linarith [outer_endpoint_bounds.2.2.2])
  by_contra hbad
  have hle : UpperInverse.X z reference≤referenceAngle := le_of_not_gt hbad
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have hX : UpperInverse.X z reference∈Icc 0 (7/10) := ⟨hzero,hle.trans hx.2⟩
  have hmono := upperPrimary_antitone (early_domain reference_mem) hX hx hle
  rw [UpperInverse.X_contact (early_domain reference_mem) z_mem] at hmono
  have he : z+1/2=outerDiagonal := by dsimp [z,OppositeTwo.TargetRatio.z]; ring
  rw [he] at hmono
  linarith [reference_contact_before]

lemma reference_value : (224443/250000:ℝ)<value reference := by
  have hx := reference_angle
  have ht := reference_T.1
  have hl := L_diagonal_upper
  dsimp [value,referenceAngle] at *
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
