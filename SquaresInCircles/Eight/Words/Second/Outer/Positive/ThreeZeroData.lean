module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeAlignedReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceSlope

/-!
# Eight squares: the original zero-source contact on the later angle interval

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
