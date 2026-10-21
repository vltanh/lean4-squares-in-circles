module

public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# Whole-interval Taylor bounds for the seven scalar inequalities

Uncompiled source draft. The alternating inequalities follow by integrating
the preceding derivative inequality from zero. The bounds are global for
nonnegative arguments; only the final tiny remainder uses the frame cap.
No angle subdivision or numerical trigonometric evaluation is involved.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.HighOrderTaylor
open Arithmetic

def S11 (x : ℝ) : ℝ := sin9 x-x^11/39916800
def C12 (x : ℝ) : ℝ := cos10 x+x^12/479001600
def S13 (x : ℝ) : ℝ := S11 x+x^13/6227020800
def C14 (x : ℝ) : ℝ := C12 x-x^14/87178291200
def S15 (x : ℝ) : ℝ := S13 x-x^15/1307674368000
def C16 (x : ℝ) : ℝ := C14 x+x^16/20922789888000
def S17 (x : ℝ) : ℝ := S15 x+x^17/355687428096000
def C18 (x : ℝ) : ℝ := C16 x-x^18/6402373705728000

theorem S11_le_sin {x : ℝ} (hx : 0≤x) : S11 x≤Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S11 t)
    (by dsimp [S11,sin9,sin7]; fun_prop) (by norm_num [S11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [S11,sin9,sin7]
      have hc := cos10_le_cos ht
      dsimp [cos10,cos8] at hc
      nlinarith) hx
  linarith

theorem cos_le_C12 {x : ℝ} (hx : 0≤x) : Real.cos x≤C12 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C12 t-Real.cos t)
    (by dsimp [C12,cos10,cos8]; fun_prop) (by norm_num [C12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [C12,cos10,cos8]
      have hs := S11_le_sin ht
      dsimp [S11,sin9,sin7] at hs
      nlinarith) hx
  linarith

theorem sin_le_S13 {x : ℝ} (hx : 0≤x) : Real.sin x≤S13 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S13 t-Real.sin t)
    (by dsimp [S13,S11,sin9,sin7]; fun_prop) (by norm_num [S13,S11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [S13,S11,sin9,sin7]
      have hc := cos_le_C12 ht
      dsimp [C12,cos10,cos8] at hc
      nlinarith) hx
  linarith

theorem C14_le_cos {x : ℝ} (hx : 0≤x) : C14 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C14 t)
    (by dsimp [C14,C12,cos10,cos8]; fun_prop) (by norm_num [C14,C12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [C14,C12,cos10,cos8]
      have hs := sin_le_S13 ht
      dsimp [S13,S11,sin9,sin7] at hs
      nlinarith) hx
  linarith

theorem S15_le_sin {x : ℝ} (hx : 0≤x) : S15 x≤Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S15 t)
    (by dsimp [S15,S13,S11,sin9,sin7]; fun_prop)
    (by norm_num [S15,S13,S11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [S15,S13,S11,sin9,sin7]
      have hc := C14_le_cos ht
      dsimp [C14,C12,cos10,cos8] at hc
      nlinarith) hx
  linarith

theorem cos_le_C16 {x : ℝ} (hx : 0≤x) : Real.cos x≤C16 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C16 t-Real.cos t)
    (by dsimp [C16,C14,C12,cos10,cos8]; fun_prop)
    (by norm_num [C16,C14,C12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [C16,C14,C12,cos10,cos8]
      have hs := S15_le_sin ht
      dsimp [S15,S13,S11,sin9,sin7] at hs
      nlinarith) hx
  linarith

theorem sin_le_S17 {x : ℝ} (hx : 0≤x) : Real.sin x≤S17 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S17 t-Real.sin t)
    (by dsimp [S17,S15,S13,S11,sin9,sin7]; fun_prop)
    (by norm_num [S17,S15,S13,S11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [S17,S15,S13,S11,sin9,sin7]
      have hc := cos_le_C16 ht
      dsimp [C16,C14,C12,cos10,cos8] at hc
      nlinarith) hx
  linarith

theorem C18_le_cos {x : ℝ} (hx : 0≤x) : C18 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C18 t)
    (by dsimp [C18,C16,C14,C12,cos10,cos8]; fun_prop)
    (by norm_num [C18,C16,C14,C12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [C18,C16,C14,C12,cos10,cos8]
      have hs := sin_le_S17 ht
      dsimp [S17,S15,S13,S11,sin9,sin7] at hs
      nlinarith) hx
  linarith

def remainder : ℝ := 1/1000000000000000

theorem frame_remainders {x : ℝ} (hx : x∈Set.Icc 0 frameCap) :
    0≤Real.sin x-S15 x ∧ Real.sin x-S15 x<remainder ∧
    0≤C16 x-Real.cos x ∧ C16 x-Real.cos x<remainder := by
  have hslo := S15_le_sin hx.1
  have hshi := sin_le_S17 hx.1
  have hclo := C18_le_cos hx.1
  have hchi := cos_le_C16 hx.1
  have hp17 := pow_le_pow_left₀ hx.1 hx.2 17
  have hp18 := pow_le_pow_left₀ hx.1 hx.2 18
  have he17 : frameCap^17/355687428096000<remainder := by norm_num [frameCap,remainder]
  have he18 : frameCap^18/6402373705728000<remainder := by norm_num [frameCap,remainder]
  dsimp [S17] at hshi
  dsimp [C18] at hclo
  refine ⟨sub_nonneg.mpr hslo,?_,sub_nonneg.mpr hchi,?_⟩ <;> nlinarith

end SquaresInCircles.Eight.TableFree.HighOrderTaylor
