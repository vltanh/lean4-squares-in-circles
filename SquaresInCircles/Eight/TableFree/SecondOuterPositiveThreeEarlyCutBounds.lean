module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeEarlyCutReferences

/-!
# Whole-arc geometry of the source `0.35` contact

Monotonicity transfers the two actual endpoint references to the
entire angle interval.  The target-label curvature bounds come from
its monotone second and third derivatives at the two ends of the
resulting target arc.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma geometry {φ : ℝ} (hφ : Domain φ) :
    u parameter φ∈Icc (151/100:ℝ) (1831/1000) ∧
      w parameter φ∈Icc (94/125:ℝ) (1279/1000) ∧
      y parameter φ∈Icc (327/200:ℝ) (351/200) ∧
      f parameter φ∈Icc (79/125:ℝ) (837/1000) ∧
      fp parameter φ∈Icc (73/200:ℝ) (571/1000) := by
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
  have hfh := f_monotone parameter_mem hp hr hφ.2
  have hfpl := fp_monotone parameter_nonnegative hl hp hφ.1
  have hfph := fp_monotone parameter_nonnegative hp hr hφ.2
  have hleft := left_curve
  have hright := right_curve
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith [hleft.1.1,hleft.1.2,hleft.2.1.1,hleft.2.1.2,
      hleft.2.2.1.1,hleft.2.2.1.2,hleft.2.2.2.1.1,hleft.2.2.2.1.2,
      hleft.2.2.2.2.1,hleft.2.2.2.2.2,
      hright.1.1,hright.1.2,hright.2.1.1,hright.2.1.2,
      hright.2.2.1.1,hright.2.2.1.2,hright.2.2.2.1.1,hright.2.2.2.1.2,
      hright.2.2.2.2.1,hright.2.2.2.2.2]

lemma target_bounds {φ : ℝ} (hφ : Domain φ) :
    target parameter φ∈Icc (63/250:ℝ) (779/1000) := by
  have hw := (geometry hφ).2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2]

lemma target_mem {φ : ℝ} (hφ : Domain φ) : target parameter φ∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem
    ⟨by linarith [(target_bounds hφ).1],by linarith [(target_bounds hφ).2]⟩

lemma velocities {φ : ℝ} (hφ : Domain φ) :
    (151/100:ℝ)*(79/125)≤bp parameter φ ∧
      bpp parameter φ∈Icc (-(69/200:ℝ)) (373/500) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hu0 : 0≤u parameter φ := by linarith [hu.1]
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hf0 : 0≤f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have hflow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤79/125) hf.1 2
  have hfhigh := pow_le_pow_left₀ hf0 hf.2 2
  have htermlo := mul_le_mul hw.1 hflow
    (by norm_num : (0:ℝ)≤(79/125)^2) hw0
  have htermhi := mul_le_mul hw.2 hfhigh (sq_nonneg _) (by norm_num : (0:ℝ)≤1279/1000)
  have hupLo := mul_le_mul hu.1 hfp.1 (by norm_num : (0:ℝ)≤73/200) hu0
  have hupHi := mul_le_mul hu.2 hfp.2 hfp0 (by norm_num : (0:ℝ)≤1831/1000)
  have hbp := mul_le_mul hu.1 hf.1 (by norm_num : (0:ℝ)≤79/125) hu0
  dsimp [bp,bpp]
  exact ⟨hbp,⟨by nlinarith,by nlinarith⟩⟩

lemma target_left_mem : (63/250:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma target_right_mem : (779/1000:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma target_left_curvature :
    (-(567/500:ℝ))<LLabel.d2 (63/250) ∧ (383/100:ℝ)<LLabel.d3 (63/250) := by
  have hU := shifted_chart_reference (outer_domain target_left_mem)
    (l := (18303267467/10^10:ℝ)) (u := (18303267468/10^10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_left_mem
    (show (63/250:ℝ)∈Icc (63/250) (63/250) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hLlo := hL.2.2.2.2.1
  norm_num [LReference.secondLo,Q0] at hLlo
  have he := LLabel.third_numerator (outer_domain target_left_mem)
  have hp := pow_pos (U_positive (outer_domain target_left_mem)) 5
  have hpower := pow_le_pow_left₀ (U_positive (outer_domain target_left_mem)).le hU.2.le 5
  have hcomp := mul_le_mul_of_nonneg_left hpower (by norm_num : (0:ℝ)≤383/100)
  norm_num [LLabel,W,Q0] at he hcomp
  constructor
  · linarith
  · nlinarith

lemma target_right_curvature : LLabel.d2 (779/1000)<(19/10:ℝ) := by
  have hU := shifted_chart_reference (outer_domain target_right_mem)
    (l := (15098870818/10^10:ℝ)) (u := (15098870819/10^10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_right_mem
    (show (779/1000:ℝ)∈Icc (779/1000) (779/1000) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hLhi := hL.2.2.2.2.2
  norm_num [LReference.secondHi,Q0] at hLhi
  linarith

lemma label_curvature {φ : ℝ} (hφ : Domain φ) :
    LLabel.d2 (target parameter φ)∈Icc (-(567/500:ℝ)) (19/10) ∧
      (383/100:ℝ)<LLabel.d3 (target parameter φ) := by
  have hb := target_bounds hφ
  have ht := target_mem hφ
  have hlow := L_second_monotone target_left_mem ht hb.1
  have hhigh := L_second_monotone ht target_right_mem hb.2
  have hthird := L_third_monotone target_left_mem ht hb.1
  exact ⟨⟨by linarith [target_left_curvature.1],
    by linarith [target_right_curvature]⟩,
    target_left_curvature.2.trans_le hthird⟩

lemma sine_upper {φ : ℝ} (hφ : Domain φ) : Real.sin φ≤(241/250:ℝ) := by
  have hm := lower_sin_monotone (domain hφ).2 (domain right_mem).2 hφ.2
  linarith [right_trig.1.2]

lemma z_upper {φ : ℝ} (hφ : Domain φ) : z parameter φ≤(557/500:ℝ) := by
  dsimp [z,parameter]
  linarith [sine_upper hφ]

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.EarlyCut
