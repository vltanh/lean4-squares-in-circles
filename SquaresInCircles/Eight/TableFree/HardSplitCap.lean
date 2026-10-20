module

public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# Convex hard-quarter caps at the actual squared radius

Uncompiled draft, following
`HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md`.

The cap uses its own actual squared radius `q`.  The fixed ceiling is used
only for rational estimates.  Strict curvature is proved on the complete
interval `[0, 7/10]`, including the part where the cap is nonpositive.
The two formulas for the curvature numerator avoid a positivity assumption
on the cap itself.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HardSplitCap

/-- These are the scalar consequences of an actual hard contact and its
own corner-circle inequality.  No endpoint or extremality is assumed. -/
structure Feasible (q D : ℝ) : Prop where
  ceiling : q ≤ qCap
  transverse : 3/5 ≤ D
  corner : (D+1)^2+1/4 ≤ q

def contact (D θ : ℝ) : ℝ := D+Real.cos θ
def root (q D θ : ℝ) : ℝ := Real.sqrt (q-(contact D θ)^2)
def cap (q D θ : ℝ) : ℝ :=
  Real.cos θ*root q D θ-Real.sin θ*contact D θ
def cornerX (q D θ : ℝ) : ℝ :=
  Real.cos θ*contact D θ+Real.sin θ*root q D θ
def drift (q D θ : ℝ) : ℝ := root q D θ-Real.sin θ
def first (q D θ : ℝ) : ℝ := -cornerX q D θ*drift q D θ/root q D θ
def second (q D θ : ℝ) : ℝ :=
  (cap q D θ*root q D θ*(cornerX q D θ-(drift q D θ)^2)+
    cornerX q D θ*drift q D θ*contact D θ*Real.sin θ)/(root q D θ)^3

theorem parameter_bounds {q D : ℝ} (h : Feasible q D) :
    0 < D ∧ D < 183/200 ∧ D < 19/20 ∧ 0 < q := by
  have hD : 0 < D := by linarith [h.transverse]
  have hD' : D < 183/200 := by
    by_contra! hn
    have hc := h.ceiling
    dsimp [qCap] at hc
    nlinarith [h.corner,sq_nonneg (D-183/200)]
  exact ⟨hD,hD',by linarith,by nlinarith [h.corner,sq_nonneg (D+1)]⟩

theorem radicand_lower {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    1/4 ≤ q-(contact D θ)^2 ∧
      1/4 ≤ q-(contact D θ)^2-(Real.sin θ)^2 := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  have hD := (parameter_bounds h).1
  have hp := mul_nonneg hD.le (sub_nonneg.mpr hc1)
  have hc2 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.cos θ) hc1 2
  dsimp [contact]
  constructor <;> nlinarith [h.corner,Real.sin_sq_add_cos_sq θ]

theorem root_sq {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (root q D θ)^2=q-(contact D θ)^2 :=
  Real.sq_sqrt (by linarith [(radicand_lower h hθ).1])

theorem root_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < root q D θ := by
  exact Real.sqrt_pos.mpr (by linarith [(radicand_lower h hθ).1])

theorem contact_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < contact D θ := by
  dsimp [contact]
  linarith [(parameter_bounds h).1,(transport_trig_coarse hθ).1]

theorem drift_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < drift q D θ := by
  have hr := root_pos h hθ
  have hrs := root_sq h hθ
  have hs := (transport_trig_coarse hθ).2.1
  have hb := (radicand_lower h hθ).2
  dsimp [drift]
  nlinarith

theorem cornerX_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < cornerX q D θ := by
  have hc : 0 < Real.cos θ := by linarith [(transport_trig_coarse hθ).1]
  have hs := (transport_trig_coarse hθ).2.1
  exact add_pos_of_pos_of_nonneg (mul_pos hc (contact_pos h hθ))
    (mul_nonneg hs (root_pos h hθ).le)

/-- The half-angle comparison used for the first curvature factor is
proved by positive squaring.  It is uniform in the actual radius. -/
theorem root_half_angle {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    0 < (root q D θ-Real.sin θ)*(1+Real.cos θ)-D*Real.sin θ := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  obtain ⟨hD,hD915,hD95,hq⟩ := parameter_bounds h
  have hw : 0 < w := root_pos h hθ
  have hwsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hden : 0 < 1+c := by dsimp [c]; linarith
  have hD2 : D^2 ≤ (19/20 : ℝ)^2 :=
    pow_le_pow_left₀ hD.le hD95.le 2
  have hgap : 0 ≤ 1-c := by dsimp [c]; linarith
  have hgap' : 1-c ≤ 1/4 := by dsimp [c]; linarith
  have hprod : D^2*(1-c) ≤ (19/20 : ℝ)^2*(1/4) := by
    calc
      D^2*(1-c) ≤ (19/20 : ℝ)^2*(1-c) :=
        mul_le_mul_of_nonneg_right hD2 hgap
      _ ≤ (19/20 : ℝ)^2*(1/4) :=
        mul_le_mul_of_nonneg_left hgap' (by norm_num)
  have hcore : 0 < (1+c)/4-D^2*(1-c) := by dsimp [c] at *; nlinarith
  have hf := mul_le_mul_of_nonneg_left h.corner (sq_nonneg (1+c))
  have hid : (w*(1+c))^2-(s*(1+c+D))^2=
      (1+c)^2*(q-(D+1)^2)-D^2*(1-c^2) := by
    calc
      (w*(1+c))^2-(s*(1+c+D))^2 =
          w^2*(1+c)^2-s^2*(1+c+D)^2 := by ring
      _ = (1+c)^2*(q-(D+1)^2)-D^2*(1-c^2) := by
        rw [hwsq,show s^2=1-c^2 by nlinarith [hunit]]
        ring
  have hdiff : 0 < (w*(1+c))^2-(s*(1+c+D))^2 := by
    rw [hid]
    have hp := mul_pos hden hcore
    nlinarith
  have hleft := mul_pos hw hden
  have hright : 0 ≤ s*(1+c+D) := by
    exact mul_nonneg hs (by linarith)
  have hcomp : s*(1+c+D) < w*(1+c) := by nlinarith
  change 0 < (w-s)*(1+c)-D*s
  nlinarith

theorem first_curvature_factor {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    611/2500 ≤ cornerX q D θ-(drift q D θ)^2 := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hden : 0 < 1+c := by dsimp [c]; linarith
  have hbr : 0 < (w-s)*(1+c)-D*s := root_half_angle h hθ
  have hmul := mul_nonneg hs hbr.le
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hid : (s*(w-s)-D*(1-c))*(1+c)=
      s*((w-s)*(1+c)-D*s) := by
    linear_combination D*hunit
  have hnonneg : 0 ≤ s*(w-s)-D*(1-c) := by
    have hh : 0 ≤ (s*(w-s)-D*(1-c))*(1+c) := by rw [hid]; exact hmul
    exact nonneg_of_mul_nonneg_left hh hden
  have hf : cornerX q D θ-(drift q D θ)^2=
      D^2+3*D+2-q+3*(s*(w-s)-D*(1-c)) := by
    dsimp [cornerX,drift,contact]
    change c*(D+c)+s*w-(w-s)^2=
      D^2+3*D+2-q+3*(s*(w-s)-D*(1-c))
    nlinarith [hunit,hsq]
  have hD2 : (3/5 : ℝ)^2 ≤ D^2 :=
    pow_le_pow_left₀ (by norm_num) h.transverse 2
  have hq := h.ceiling
  dsimp [qCap] at hq
  rw [hf]
  nlinarith [h.transverse]

theorem second_curvature_factor {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    41/320 ≤ Real.cos θ*(root q D θ)^2-contact D θ*(Real.sin θ)^2 := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  obtain ⟨hD,hD915,hD95,hq⟩ := parameter_bounds h
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hid : c*w^2-(D+c)*s^2=c*(q-D^2-1)-D*(1+c^2) := by
    linear_combination c*hsq-(D+c)*hunit
  have hp := mul_nonneg (by dsimp [c]; linarith : 0 ≤ c)
    (show 0 ≤ q-(D+1)^2-1/4 by linarith [h.corner])
  have hgap : (1-c)^2 ≤ (1/4 : ℝ)^2 :=
    pow_le_pow_left₀ (by dsimp [c]; linarith)
      (by dsimp [c]; linarith) 2
  have hprod : D*(1-c)^2 ≤ (19/20 : ℝ)*(1/4)^2 := by
    calc
      D*(1-c)^2 ≤ (19/20 : ℝ)*(1-c)^2 :=
        mul_le_mul_of_nonneg_right hD95.le (sq_nonneg _)
      _ ≤ (19/20 : ℝ)*(1/4)^2 :=
        mul_le_mul_of_nonneg_left hgap (by norm_num)
  change 41/320 ≤ c*w^2-(D+c)*s^2
  rw [hid]
  dsimp [c] at *
  nlinarith

theorem second_alternate (q D θ : ℝ) :
    second q D θ=
      (cornerX q D θ*(Real.cos θ*(root q D θ)^2-
          contact D θ*(Real.sin θ)^2)-
        cap q D θ*root q D θ*(drift q D θ)^2)/(root q D θ)^3 := by
  unfold second cap cornerX drift
  congr 1
  ring

/-- The sign split concerns the cap value on one continuous interval;
there is no angular subdivision or sampled certificate. -/
theorem second_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < second q D θ := by
  have hw := root_pos h hθ
  have hX := cornerX_pos h hθ
  have hk := drift_pos h hθ
  have hC := contact_pos h hθ
  have hs := (transport_trig_coarse hθ).2.1
  by_cases hL : 0 < cap q D θ
  · unfold second
    apply div_pos _ (pow_pos hw 3)
    have hf : 0 < cornerX q D θ-(drift q D θ)^2 := by
      linarith [first_curvature_factor h hθ]
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hL hw) hf)
      (mul_nonneg (mul_nonneg (mul_nonneg hX.le hk.le) hC.le) hs)
  · rw [second_alternate]
    apply div_pos _ (pow_pos hw 3)
    have hf : 0 < Real.cos θ*(root q D θ)^2-contact D θ*(Real.sin θ)^2 := by
      linarith [second_curvature_factor h hθ]
    have hn : cap q D θ*root q D θ*(drift q D θ)^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hL) hw.le) (sq_nonneg _)
    linarith [mul_pos hX hf]

end SquaresInCircles.Eight.TableFree.HardSplitCap
