module
public import SquaresInCircles.Six.Normalization.Constants
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-!
# Exact cap-branch identity I1 and the opposite-cardinal budget deduction

The scalar tilt estimate K5 is not proved by this file. Its use in the final
lemma is explicit, together with BOTH opposite-cardinal cap hypotheses.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

def capSwitch : ℝ := Real.arcsin (1 / (2 * R0))

def capFirst (t : ℝ) : ℝ :=
  (rho0 - 1 / 2) * Real.cos t - (1 / 2) * Real.sin t

def capSecond (t : ℝ) : ℝ := R0 - Real.cos t - Real.sin t

def capDepth (t : ℝ) : ℝ :=
  if t ≤ capSwitch then capFirst t else capSecond t

lemma R0_pos : 0 < R0 := Real.sqrt_pos.mpr Q0_pos

lemma R0_gt_one : 1 < R0 := by
  have hs : Real.sqrt (1 : ℝ) < Real.sqrt Q0 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num [Q0])
  simpa only [Real.sqrt_one] using hs

lemma switch_sine_bounds : 0 < 1 / (2 * R0) ∧ 1 / (2 * R0) < 1 := by
  have hp : 0 < 2 * R0 := by linarith [R0_pos]
  exact ⟨div_pos (by norm_num) hp,
    (div_lt_one hp).mpr (by linarith [R0_gt_one])⟩

lemma capSwitch_nonneg : 0 ≤ capSwitch :=
  Real.arcsin_nonneg.mpr switch_sine_bounds.1.le

lemma sin_capSwitch : Real.sin capSwitch = 1 / (2 * R0) := by
  exact Real.sin_arcsin (by linarith [switch_sine_bounds.1]) switch_sine_bounds.2.le

lemma cos_capSwitch : Real.cos capSwitch = (rho0 + 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  have hid : 1 - (1 / (2 * R0)) ^ 2 = ((rho0 + 1 / 2) / R0) ^ 2 := by
    field_simp [hn]
    nlinarith [R0_sq, rho0_identity]
  rw [capSwitch, Real.cos_arcsin, hid, Real.sqrt_sq]
  exact div_nonneg (by linarith [rho0_gt_one]) R0_pos.le

lemma capFirst_switch : capFirst capSwitch = (rho0 ^ 2 - 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  rw [capFirst, cos_capSwitch, sin_capSwitch]
  field_simp [hn] <;> ring

lemma capSecond_switch : capSecond capSwitch = (rho0 ^ 2 - 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  rw [capSecond, cos_capSwitch, sin_capSwitch]
  field_simp [hn]
  nlinarith [R0_sq, rho0_sq]

/-- I1 is an exact identity, not a numerical equality test. -/
lemma cap_branches_agree : capFirst capSwitch = capSecond capSwitch :=
  capFirst_switch.trans capSecond_switch.symm

lemma capDepth_zero : capDepth 0 = rho0 - 1 / 2 := by
  simp [capDepth, capFirst, capSwitch_nonneg]

/-- K5, when established, implies N26 only with both cardinal cap conditions.
The two zero-angle case is handled separately to retain the strict conclusion. -/
lemma opposite_cardinal_angle_budget {x e w : ℝ}
    (hE : 1 / 2 + x ≤ capDepth |e|)
    (hW : 1 / 2 - x ≤ capDepth |w|)
    (he : |e| ≤ 2 / 5) (hw : |w| ≤ 2 / 5)
    (htilt : ∀ t : ℝ, 0 < t → t ≤ 2 / 5 →
      capDepth t < rho0 - 1 / 2 - t / 2) :
    |e| + |w| < 4 * c0 := by
  have hweak (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 2 / 5) :
      capDepth t ≤ rho0 - 1 / 2 - t / 2 := by
    rcases ht.eq_or_lt with hzero | hpos
    · subst t
      simp [capDepth_zero]
    · exact (htilt t hpos ht').le
  by_cases he0 : e = 0
  · by_cases hw0 : w = 0
    · subst e
      subst w
      simpa using mul_pos (by norm_num : (0 : ℝ) < 4) c0_pos
    · have hs := htilt |w| (abs_pos.mpr hw0) hw
      have h0 := hweak |e| (abs_nonneg e) he
      dsimp [c0]
      linarith
  · have hs := htilt |e| (abs_pos.mpr he0) he
    have h0 := hweak |w| (abs_nonneg w) hw
    dsimp [c0]
    linarith

end SquaresInCircles.Six.Normalization
