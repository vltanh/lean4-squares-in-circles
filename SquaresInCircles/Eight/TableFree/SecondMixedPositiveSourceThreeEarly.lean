module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeEarlyReferences

/-!
# Every early positive-core transverse owner

A single quadratic tangent controls the whole initial target interval.
The fixed harmonic coefficient cages transfer to the proved rational
whole-angle polynomial. Concavity of the target derivative handles all
remaining targets at once. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD)
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (13/10)

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma polynomial_evaluation (φ : ℝ) : Polynomial.aeval φ PositiveEarlyPolynomial.lowerPoly=
    φ-204013/1000000-(159591/250000)*HighOrderTaylor.S13 φ+
      (168423/125000)*HighOrderTaylor.C14 φ-
      (79539/500000)*HighOrderTaylor.C12 (2*φ)-
      (153197/1000000)*HighOrderTaylor.S13 (2*φ)-γ := by
  norm_num [PositiveEarlyPolynomial.lowerPoly,PositiveEarlyPolynomial.S13,
    PositiveEarlyPolynomial.C12,PositiveEarlyPolynomial.C14,Polynomial.aeval_comp,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,γ,EdgeThreeAligned.threshold]
  ring

lemma scalar_lower {φ : ℝ} (hφ : φ∈angles) : γ<G φ := by
  have ht := lower_trig (lower_mem hφ)
  have hφ0 : 0≤φ := by dsimp [angles,lowerAngle] at hφ; linarith [pi_hand_enclosure.1,hφ.1]
  have hs : 0≤Real.sin φ := by linarith [ht.1]
  have hc := ht.2.2.1
  have hs2 : 0≤Real.sin (2*φ) := by rw [Real.sin_two_mul]; positivity
  have hc2 : Real.cos (2*φ)≤0 := by
    rw [Real.cos_two_mul]
    have hcsq := pow_le_pow_left₀ hc ht.2.2.2.1.le 2
    nlinarith
  have ha := mul_le_mul_of_nonneg_right coefficients.2.1.le hs
  have hb := mul_le_mul_of_nonneg_right coefficients.2.2.1.le hc
  have hd := mul_le_mul_of_nonpos_right coefficients.2.2.2.1.le hc2
  have he := mul_le_mul_of_nonneg_right coefficients.2.2.2.2.le hs2
  have hS := HighOrderTaylor.sin_le_S13 hφ0
  have hC := HighOrderTaylor.C14_le_cos hφ0
  have hS2 := HighOrderTaylor.sin_le_S13 (show 0≤2*φ by linarith)
  have hC2 := HighOrderTaylor.cos_le_C12 (show 0≤2*φ by linarith)
  have hp := PositiveEarlyPolynomial.lower
    (show φ∈Icc (87/100:ℝ) (13/10) from
      ⟨by dsimp [lowerAngle] at hφ; linarith [hφ.1,pi_hand_enclosure.1],hφ.2⟩)
  rw [polynomial_evaluation] at hp
  rw [harmonic]
  nlinarith [coefficients.1]

lemma curvature_lower {B φ : ℝ} (hB : B∈Icc (0:ℝ) (31/100)) (hφ : angles φ) : m≤FBB B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hBf : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans hcut.2⟩
  have hm := FBB_antitone φ hBf hcut hB.2
  have ht := lower_trig (lower_mem hφ)
  have hd := (outer_ratio_bounds hcut).2.2.1
  have hp := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤g*ratioD (31/100) by dsimp [g,EdgeThreeAligned.gp]; linarith)
  dsimp [FBB] at hm
  linarith [curvature_reference]

lemma initial_target {B φ : ℝ} (hB : B∈Icc (0:ℝ) (31/100)) (hφ : φ∈angles) : γ<F B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (31/100)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans hcut.2⟩
  have ht := curvature_tangent (f := fun y => F y φ) (d := fun y => FB y φ)
    (dd := fun y => FBB y φ) (κ := m) hB
    (show r∈Icc (0:ℝ) (31/100) by norm_num [r])
    (fun y hy => F_hasDerivAt (hdom hy)) (fun y hy => FB_hasDerivAt (hdom hy))
    (fun y hy => curvature_lower hy hφ)
  have hh := scalar_lower hφ
  have hs := sq_nonneg (m*(B-r)+FB r φ)
  dsimp [G,m] at *
  nlinarith

lemma later_derivative {B φ : ℝ} (hB : B∈Icc (31/100:ℝ) outerDiagonal) (hφ : φ∈angles) :
    0<FB B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hterminal : Lower (13/10:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hl := FB_angle_antitone hcut (lower_mem hφ) hterminal hφ.2
  have hr := FB_angle_antitone hd (lower_mem hφ) hterminal hφ.2
  have hm := (FB_concave φ).min_le_of_mem_Icc hcut hd hB
  exact (lt_min (derivative_references.1.trans_le hl) (derivative_references.2.trans_le hr)).trans_le hm

lemma all_targets {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : φ∈angles) : γ<F B φ := by
  by_cases he : B≤31/100
  · exact initial_target ⟨hB.1,he⟩ hφ
  · have hdom {y : ℝ} (hy : y∈Icc (31/100:ℝ) outerDiagonal) : y∈Icc 0 outerDiagonal :=
      ⟨by linarith [hy.1],hy.2⟩
    have hm : MonotoneOn (fun y => F y φ) (Icc (31/100:ℝ) outerDiagonal) :=
      monoOn_of_hasDeriv_nonneg
        (fun y hy => (F_hasDerivAt (φ := φ) (hdom hy)).continuousAt.continuousWithinAt)
        (fun y hy => F_hasDerivAt (φ := φ) (hdom (Ioo_subset_Icc_self hy)))
        (fun y hy => (later_derivative (Ioo_subset_Icc_self hy) hφ).le)
    exact (initial_target (show (31/100:ℝ)∈Icc (0:ℝ) (31/100) by norm_num) hφ).trans_le
      (hm ⟨le_rfl,(Asymmetric.rational_outer_mem (by norm_num : (31/100:ℝ)∈Icc 0 (899/1000))).2⟩
        ⟨by linarith,hB.2⟩ (by linarith))

theorem original {b A B φ : ℝ} (ht : OuterState A B) (hφ : φ∈angles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ) : γ<value b B φ :=
  (all_targets (NegativeTwo.source_mem ht) hφ).trans_le (PositiveSource.original_lower ht hsep)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
