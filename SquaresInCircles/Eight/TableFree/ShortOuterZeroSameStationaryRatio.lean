module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameStationaryShape

/-!
# The written concave target-ratio tangent

Uncompiled transcription of Section 5.3. The target ratio is concave on
one complete height interval. Its tangent at 1.84 is bounded by the
written affine function; the endpoint radical is checked by squaring.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic

abbrev ratioDomain : Set ℝ := Icc (4369/2500) (92117/50000)
def targetRoot (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)
def targetRatioD (u : ℝ) : ℝ := -Q0/(u^2*targetRoot u)
def targetRatioDD (u : ℝ) : ℝ :=
  Q0*(2*Q0-3*u^2)/(u^3*(targetRoot u)^3)

lemma targetRoot_data {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    0<u ∧ 0<targetRoot u ∧ (targetRoot u)^2=Q0-u^2 := by
  have hp : 0<Q0-u^2 := by norm_num [Q0]; nlinarith [hu.1,hu.2]
  exact ⟨by linarith [hu.1],Real.sqrt_pos.mpr hp,Real.sq_sqrt hp.le⟩

lemma targetRoot_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRoot (-u/targetRoot u) u := by
  have h := targetRoot_data hu
  have hn : Q0-u^2≠0 := by nlinarith [h.2.1,h.2.2]
  convert (((hasDerivAt_id u).pow 2).const_sub Q0).sqrt hn using 1 <;>
    dsimp [targetRoot] <;> field_simp [h.2.1.ne'] <;> ring

lemma targetRatio_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRatio (targetRatioD u) u := by
  have h := targetRoot_data hu
  convert (targetRoot_hasDerivAt hu).div (hasDerivAt_id u) h.1.ne' using 1
  · rfl
  · dsimp [targetRatioD]
    field_simp [h.1.ne',h.2.1.ne']
    nlinarith [h.2.2]

lemma targetRatioD_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRatioD (targetRatioDD u) u := by
  have h := targetRoot_data hu
  have hd := (hasDerivAt_const u (-Q0)).div
    (((hasDerivAt_id u).pow 2).mul (targetRoot_hasDerivAt hu))
    (mul_ne_zero (pow_ne_zero 2 h.1.ne') h.2.1.ne')
  convert hd using 1
  · rfl
  · dsimp [targetRatioDD]
    field_simp [h.1.ne',h.2.1.ne']
    nlinarith [h.2.2]

lemma ratio_domain_inclusion {u : ℝ} (hu : u∈ratioDomain) :
    u∈Icc (1747/1000:ℝ) (951/500) := ⟨by linarith [hu.1],by linarith [hu.2]⟩

lemma targetRatio_concave : ConcaveOn ℝ ratioDomain targetRatio :=
  concave_of_deriv2
    (fun u hu => targetRatio_hasDerivAt (ratio_domain_inclusion hu))
    (fun u hu => targetRatioD_hasDerivAt (ratio_domain_inclusion hu))
    (fun u hu => by
      have h := targetRoot_data (ratio_domain_inclusion hu)
      have hn : 2*Q0-3*u^2≤0 := by norm_num [Q0]; nlinarith [hu.1]
      dsimp [targetRatioDD]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num [Q0]) hn) (by positivity))

lemma tangent_reference : targetRatio (46/25)<(19783/50000:ℝ) ∧
    |targetRatioD (46/25)+158863/100000|<(1/100000:ℝ) := by
  have h := targetRoot_data (show (46/25:ℝ)∈Icc (1747/1000) (951/500) by norm_num)
  have hroot : (72801/100000:ℝ)<targetRoot (46/25) ∧
      targetRoot (46/25)<728011/1000000 := by
    norm_num [Q0] at h
    constructor <;> nlinarith [h.2.1,h.2.2]
  constructor
  · dsimp [targetRatio,targetRoot] at hroot ⊢
    norm_num
    linarith [hroot.2]
  · rw [abs_lt]
    dsimp [targetRatioD]
    constructor
    · have hh := (div_lt_iff₀ (by positivity : 0<(46/25:ℝ)^2*targetRoot (46/25))).2
        (show Q0<(158864/100000:ℝ)*(46/25)^2*targetRoot (46/25) by
          norm_num [Q0]; linarith [hroot.1])
      linarith
    · have hh := (lt_div_iff₀ (by positivity : 0<(46/25:ℝ)^2*targetRoot (46/25))).2
        (show (158862/100000:ℝ)*(46/25)^2*targetRoot (46/25)<Q0 by
          norm_num [Q0]; linarith [hroot.2])
      linarith

lemma targetRatio_tangent {u : ℝ} (hu : u∈ratioDomain) :
    targetRatio u<(82969/25000:ℝ)-(158863/100000)*u := by
  have ht := SplitConcavityTools.tangent_upper targetRatio_concave
    (show (46/25:ℝ)∈ratioDomain by norm_num [ratioDomain]) hu
    (targetRatio_hasDerivAt (by norm_num))
  have hd := tangent_reference.2
  have hdist : |u-46/25|≤(1/10:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hu.1,hu.2]
  have hp : |(targetRatioD (46/25)+158863/100000)*(u-46/25)|≤(1/100000)*(1/10:ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hd.le hdist (abs_nonneg _) (by norm_num)
  have he := (abs_le.mp hp).2
  nlinarith [tangent_reference.1]

lemma targetRatio_nonneg {u : ℝ} (hu : 0<u) : 0≤targetRatio u :=
  div_nonneg (Real.sqrt_nonneg _) hu.le

lemma targetRatio_upper {u lo k : ℝ}
    (hu : u∈Icc (1747/1000:ℝ) (951/500)) (hlo : 0≤lo) (hul : lo≤u)
    (hk : 0<k) (hbound : Q0<lo^2*(1+k^2)) : targetRatio u<k := by
  have h := targetRoot_data hu
  have hs := pow_le_pow_left₀ hlo hul 2
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0≤1+k^2)
  have hsq : (targetRoot u)^2<(k*u)^2 := by nlinarith [h.2.2]
  have hp := mul_pos hk h.1
  have hroot : targetRoot u<k*u := by nlinarith
  exact (div_lt_iff₀ h.1).2 hroot

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
