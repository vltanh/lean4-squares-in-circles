module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeZeroReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCutBounds

/-!
# Eight squares: whole-arc bounds for the original zero-source contact

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
