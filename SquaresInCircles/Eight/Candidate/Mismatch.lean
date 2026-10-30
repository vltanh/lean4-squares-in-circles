module

public import SquaresInCircles.Eight.Candidate.Model
public import SquaresInCircles.Eight.Arithmetic.Taylor

/-!
# Eight squares: the mismatch chain

The frame charge `h x = (|sin x| + |cos x| - 1)/2` is increasing and concave on `[0, 7/10]`
(`h_monotone`, `h_concave`), so it lies above its chords, and it lies above the polynomials
`hLower7` and `x/2 - x²/4 - x³/12` (`hLower7_le`, `h_cubic_lower`). The charges of the aligned
edges add up to at least `h` of the mismatch (`hSum_ge_h_mismatch`). So a charged bound with
charge `β` and constants `γᵢ` bounds the mismatch (`mismatch_contract`): if `∑ γᵢ + β L` exceeds
`2π` for some `L ≤ h t`, the mismatch is less than `t`.

These are the scalar steps of the chain. The coarse table gives mismatch below `2/5` and then
below `13/50` (`coarse_first_contraction`, `coarse_enhanced_contraction`), and the three later
tables give, each from the bound before it, mismatch below `1/10`, `3/200` and `1/1000`
(`contraction_026_to_01`, `contraction_01_to_015`, `contraction_015_to_001`). The charged bounds
themselves are hypotheses here; `Generated/AffineBudgets.lean` proves them from the affine tables,
and `Capture.lean` chains the steps.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate

theorem seven_tenths_lt_pi_four : (7 : ℝ) / 10 < Real.pi / 4 := by
  linarith [Real.pi_gt_d2]

theorem h_eq_smooth {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (7 / 10)) : h x = hSmooth x := by
  have hh := cos_sin_nonneg ⟨hx.1, by linarith [hx.2, seven_tenths_lt_pi_four, Real.pi_pos]⟩
  simp [h, hSmooth, abs_of_nonneg hh.1, abs_of_nonneg hh.2]

theorem h_monotone : MonotoneOn h (Icc (0 : ℝ) (7 / 10)) := by
  intro x hx y hy hxy
  rw [h_eq_smooth hx, h_eq_smooth hy]
  have hh := cos_add_sin_mono hx.1 hxy (hy.2.trans seven_tenths_lt_pi_four.le)
  unfold hSmooth
  linarith

theorem h_concave : ConcaveOn ℝ (Icc (0 : ℝ) (7 / 10)) h := by
  have hd (x : ℝ) : HasDerivAt hSmooth ((Real.cos x - Real.sin x) / 2) x := by
    have hfun : hSmooth = fun y => (Real.sin y + Real.cos y - 1) / 2 := rfl
    rw [hfun]
    convert (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).sub_const 1).div_const 2
      using 1
  have hd' (x : ℝ) : HasDerivAt (fun t => (Real.cos t - Real.sin t) / 2)
      (-(Real.sin x + Real.cos x) / 2) x := by
    convert ((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).div_const 2 using 1
    ring
  have hf : ConcaveOn ℝ (Icc (0 : ℝ) (7 / 10)) hSmooth :=
    concave_of_deriv2 (fun x _ => hd x) (fun x _ => hd' x) (fun x hx => by
      have htrig := cos_sin_nonneg ⟨hx.1, by linarith [hx.2, seven_tenths_lt_pi_four, Real.pi_pos]⟩
      linarith)
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ Icc (0 : ℝ) (7 / 10) :=
    (convex_Icc (0 : ℝ) (7 / 10)) hx hy ha hb hab
  rw [h_eq_smooth hx, h_eq_smooth hy, h_eq_smooth hz]
  exact hf.2 hx hy ha hb hab

theorem h_above_chord {L x : ℝ} (hL : 0 < L) (hLmax : L ≤ 7 / 10)
    (hx : 0 ≤ x ∧ x ≤ L) : x / L * h L ≤ h x := by
  have ht0 : 0 ≤ x / L := div_nonneg hx.1 hL.le
  have ht1 : x / L ≤ 1 := (div_le_one hL).2 hx.2
  have hc := h_concave.2 (show (0 : ℝ) ∈ Icc 0 (7 / 10) by norm_num)
    ⟨hL.le, hLmax⟩ (sub_nonneg.mpr ht1) ht0 (show (1 - x / L) + x / L = 1 by ring)
  have hxid : x / L * L = x := div_mul_cancel₀ x (ne_of_gt hL)
  simpa only [smul_eq_mul, mul_zero, zero_add, hxid, h_zero] using hc

theorem h_above_rational_chord {L x κ : ℝ} (hL : 0 < L) (hLmax : L ≤ 7 / 10)
    (hx : 0 ≤ x ∧ x ≤ L) (hend : κ * L ≤ h L) : κ * x ≤ h x := by
  have hh := mul_le_mul_of_nonneg_left hend (div_nonneg hx.1 hL.le)
  have hid : x / L * (κ * L) = κ * x := by field_simp
  rw [hid] at hh
  exact hh.trans (h_above_chord hL hLmax hx)

def hLower7 (x : ℝ) : ℝ :=
  x / 2 - x ^ 2 / 4 - x ^ 3 / 12 + x ^ 4 / 48 + x ^ 5 / 240 -
    x ^ 6 / 1440 - x ^ 7 / 10080

theorem hLower7_le {x : ℝ} (hx : 0 ≤ x) : hLower7 x ≤ h x := by
  have hs := sin_lower_seven hx
  have hc := cos_lower_six hx
  have has := le_abs_self (Real.sin x)
  have hac := le_abs_self (Real.cos x)
  unfold hLower7 h
  linarith

theorem h_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x / 2 - x ^ 2 / 4 - x ^ 3 / 12 ≤ h x := by
  have hs := Real.sin_ge_sub_cube hx
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have has := le_abs_self (Real.sin x)
  have hac := le_abs_self (Real.cos x)
  unfold h
  linarith

theorem h_seven_tenths_chord : (29 : ℝ) / 100 * (7 / 10) ≤ h (7 / 10) := by
  have hh := hLower7_le (x := (7 : ℝ) / 10) (by norm_num)
  norm_num [hLower7] at hh ⊢
  linarith

theorem hSum_ge_chord {θ : Vertex → ℝ}
    (hsmall : ∀ i ∈ charged, |delta θ i| ≤ 7 / 10) :
    (29 : ℝ) / 100 * mismatch θ ≤ hSum θ := by
  have hh := Finset.sum_le_sum (s := charged) (fun i hi =>
    h_above_rational_chord (by norm_num : (0 : ℝ) < 7 / 10) le_rfl
      ⟨abs_nonneg _, hsmall i hi⟩ h_seven_tenths_chord)
  simpa only [hSum, mismatch, Finset.mul_sum] using hh

theorem hSum_ge_h_mismatch {θ : Vertex → ℝ} (hsmall : mismatch θ ≤ 7 / 10) :
    h (mismatch θ) ≤ hSum θ := by
  rcases (mismatch_nonneg θ).eq_or_lt with hzero | hpos
  · rw [← hzero, h_zero]
    exact Finset.sum_nonneg fun _ _ => h_nonneg _
  · have hh := Finset.sum_le_sum (s := charged) (fun i hi =>
      h_above_chord hpos hsmall ⟨abs_nonneg _, delta_le_mismatch θ hi⟩)
    have hid : (∑ i ∈ charged, |delta θ i| / mismatch θ * h (mismatch θ)) =
        h (mismatch θ) := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      change mismatch θ / mismatch θ * h (mismatch θ) = h (mismatch θ)
      rw [div_self (ne_of_gt hpos), one_mul]
    simpa only [hid, hSum] using hh

theorem mismatch_contract {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    {β t U L : ℝ} {γ : Vertex → ℝ}
    (P : ChargedBound C F β γ) (hβ : 0 ≤ β)
    (hS : mismatch F.theta ≤ 7 / 10)
    (ht : 0 ≤ t ∧ t ≤ 7 / 10) (hL : L ≤ h t)
    (hπ : 2 * Real.pi < U) (hreserve : U ≤ (∑ i, γ i) + β * L) :
    mismatch F.theta < t := by
  by_contra! hnot
  have hh := h_monotone ht ⟨mismatch_nonneg _, hS⟩ hnot
  have hsum := hSum_ge_h_mismatch hS
  have hprod := mul_le_mul_of_nonneg_left (hL.trans (hh.trans hsum)) hβ
  have hc := P.cyclic
  linarith

def coarseBeta : ℝ := 99 / 5000
def coarseGamma : Vertex → ℝ := fun _ => 89727 / 100000
def retainedReserve : Vertex → ℝ :=
  ![15 / 1000000, 13 / 1000000, 18 / 1000000, 12 / 1000000,
    15 / 1000000, 23 / 1000000, 6 / 1000000]
def enhancedGamma (i : Vertex) : ℝ := coarseGamma i + retainedReserve i
def middleGamma : Vertex → ℝ := fun _ => 448791 / 500000
def intermediateGamma : Vertex → ℝ :=
  ![8975928 / 10000000, 8975928 / 10000000, 8975928 / 10000000,
    8975928 / 10000000, 8975928 / 10000000,
    89759275 / 100000000, 8975917 / 10000000]
def finalGamma : Vertex → ℝ :=
  ![897595 / 1000000, 897595 / 1000000, 897595 / 1000000,
    897595 / 1000000, 897595 / 1000000, 897595 / 1000000,
    8975925 / 10000000]

theorem coarse_first_contraction {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (P : ChargedBound C F coarseBeta coarseGamma) : mismatch F.theta < 2 / 5 := by
  have hsum := hSum_ge_chord (θ := F.theta) (fun i _ => (F.delta_small i).le)
  have hbudget := P.cyclic
  have hπ := Arithmetic.two_pi_lt_710_over_113
  by_contra! hnot
  have hprod := mul_le_mul_of_nonneg_left hsum (by norm_num [coarseBeta] : 0 ≤ coarseBeta)
  norm_num [coarseGamma, coarseBeta, Fin.sum_univ_succ] at hbudget hprod
  nlinarith

theorem coarse_enhanced_contraction {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (P : ChargedBound C F coarseBeta coarseGamma)
    (Pplus : ChargedBound C F coarseBeta enhancedGamma) :
    mismatch F.theta < 13 / 50 := by
  apply mismatch_contract Pplus (by norm_num [coarseBeta])
    (by linarith [coarse_first_contraction P])
    (by norm_num : (0 : ℝ) ≤ 13 / 50 ∧ (13 : ℝ) / 50 ≤ 7 / 10)
    (hLower7_le (by norm_num)) Arithmetic.two_pi_lt_710_over_113
  norm_num [coarseBeta, coarseGamma, enhancedGamma, retainedReserve,
    hLower7, Fin.sum_univ_succ]

theorem contraction_026_to_01 {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (P : ChargedBound C F (1 / 400) middleGamma)
    (hS : mismatch F.theta ≤ 13 / 50) : mismatch F.theta < 1 / 10 := by
  apply mismatch_contract P (by norm_num) (by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 10 ∧ (1 : ℝ) / 10 ≤ 7 / 10)
    (h_cubic_lower (by norm_num)) Arithmetic.two_pi_lt_710_over_113
  norm_num [middleGamma, Fin.sum_univ_succ]

theorem contraction_01_to_015 {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (P : ChargedBound C F (1 / 200) intermediateGamma)
    (hS : mismatch F.theta ≤ 1 / 10) : mismatch F.theta < 3 / 200 := by
  have hL : (238191 : ℝ) / 32000000 ≤ h (3 / 200) := by
    have hh := h_cubic_lower (x := (3 : ℝ) / 200) (by norm_num)
    norm_num at hh ⊢
    linarith
  apply mismatch_contract P (by norm_num) (by linarith)
    (by norm_num : (0 : ℝ) ≤ 3 / 200 ∧ (3 : ℝ) / 200 ≤ 7 / 10)
    hL Arithmetic.two_pi_lt_628318531_over_1e8
  norm_num [intermediateGamma, Fin.sum_univ_succ]

theorem contraction_015_to_001 {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (P : ChargedBound C F (1 / 20) finalGamma)
    (hS : mismatch F.theta ≤ 3 / 200) : mismatch F.theta < 1 / 1000 := by
  have hL : (5996999 : ℝ) / 12000000000 ≤ h (1 / 1000) := by
    have hh := h_cubic_lower (x := (1 : ℝ) / 1000) (by norm_num)
    norm_num at hh ⊢
    linarith
  apply mismatch_contract P (by norm_num) (by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 1000 ∧ (1 : ℝ) / 1000 ≤ 7 / 10)
    hL Arithmetic.two_pi_lt_628318531_over_1e8
  norm_num [finalGamma, Fin.sum_univ_succ]

end SquaresInCircles.Eight.Candidate
