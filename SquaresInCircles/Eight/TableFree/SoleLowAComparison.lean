module

public import SquaresInCircles.Eight.TableFree.SoleNormGain
public import SquaresInCircles.Eight.TableFree.CorrelatedSameBlock

/-!
# The low-family A charge and same-B-block comparison

Uncompiled source. The A angle keeps coefficient ell rather than the
larger force coefficient k. The positive cosine difference pays the
actual change from k to c. The same-block comparison uses the surviving
correlated trigonometric bound, whose ratio is weaker than the present
low-family ratio.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleLowAComparison
open SoleECoefficients SoleNormGain SingleAngleConcavity
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

theorem coefficient_interval {t : ℝ} (ht : t∈domain .low) :
    0<k .low t ∧ k .low t≤c .low t ∧
    (117/200)*c .low t≤ell .low t ∧ ell .low t≤(18/25)*k .low t ∧
    173/500<c .low t-ell .low t ∧ c .low t-k .low t=(3/10)*t := by
  have hb := low_bounds ht
  have hc := low_correlations ht
  have hp := positive ht
  have htc := mul_nonneg ht.1 hp.2.2.1.le
  refine ⟨hp.1,hb.2.2.1,?_,hc.2.2.1.le,hc.2.2.2,?_⟩
  · nlinarith [hc.1]
  · dsimp [c]
    ring

theorem cosine_loss_lower {t : ℝ} (ht : t∈Icc 0 (1/5 : ℝ)) :
    (299/600)*t^2≤1-Real.cos t := by
  have hc := cos_upper_four ht.1
  have ht2 : t^2≤1/25 := by
    have h := pow_le_pow_left₀ ht.1 ht.2 2
    norm_num at h
    linarith
  have ht4 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
  nlinarith

theorem A_ge_B {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vnu R (ell .low t) (c .low t) (c .low t) t≤
      Vnu R (ell .low t) (k .low t) (ell .low t) t := by
  rcases coefficient_interval ht with ⟨hk,hkc,hr0,hr1,hcl,hck⟩
  have hg := coefficient_short hR hk hkc hr0 hr1 ht
  have hcos := cosine_loss_lower ht
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hm := mul_le_mul_of_nonneg_right hcl.le hcos0
  have hm' := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤173/500)
  rw [hck] at hg
  dsimp [Vnu,V,normGain] at *
  nlinarith [sq_nonneg t]

theorem A_ge_B_at_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vnu R (ell .low t) (c .low t) (c .low t) frameCap≤
      Vnu R (ell .low t) (k .low t) (ell .low t) frameCap := by
  rcases coefficient_interval ht with ⟨hk,hkc,hr0,hr1,hcl,hck⟩
  have hg := coefficient_cap hR hk hkc hr0 hr1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc : (117/500 : ℝ)≤1-Real.cos frameCap := by
    norm_num [frameCap] at hcos
    linarith
  have hm := mul_le_mul_of_nonneg_right hcl.le (show 0≤1-Real.cos frameCap by linarith)
  have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤173/500)
  have hcku : c .low t-k .low t≤3/50 := by rw [hck]; linarith [ht.2]
  dsimp [Vnu,V,normGain] at *
  linarith

theorem B_same_block {R t : ℝ} (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤M R (ell .low t) (c .low t) t := by
  have hc := (positive ht).2.2.1
  have hr := (low_correlations ht).1
  have htc := mul_nonneg ht.1 hc.le
  have hratio : PositiveStressCoefficients.ratio t*c .low t≤ell .low t := by
    dsimp [PositiveStressCoefficients.ratio]
    nlinarith
  have hh := CorrelatedSameBlock.negative_surplus (R := R) hc.le hratio (angle ht)
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hid : mixedBlock R (ell .low t) (c .low t) (frameCap-t) frameCap=
      M R (ell .low t) (c .low t) t := by
    simpa only [show t+(frameCap-t)=frameCap by ring] using
      mixedBlock_saturated R (ell .low t) (c .low t) t
  simpa only [sub_zero,hid] using hh

end SquaresInCircles.Eight.TableFree.SoleLowAComparison
