module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Mixed.NegativeACaps

/-!
# Eight squares: the same derivative reserve for both mixed-sign A motions

All angles stay on the single
interval [0,19/50]. The exact comparison cos² > 43/50 pays both
secant derivatives. The two gap derivatives share the literal reserve
10459/25800 > 2/5; no contact or angle subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.MixedNegativeA
open Candidate Secondary

def secSq (r : ℝ) : ℝ := 1/Real.cos r^2
def secTan (r : ℝ) : ℝ := Real.sin r/Real.cos r^2

theorem capD_identity (P k r : ℝ) : capD P k r=P*secTan r+k*secSq r := by
  dsimp [capD,secTan,secSq]
  ring

theorem secant_bounds {r : ℝ} (hr : r∈Icc 0 cut) :
    1≤ secSq r ∧ secSq r<50/43 ∧ 0≤ secTan r ∧ secTan r<19/43 := by
  have hcos := cosine_positive hr
  have hcoslo := Real.one_sub_sq_div_two_le_cos (x:=r)
  have hr2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hcoscut : (4639/5000:ℝ)≤Real.cos r := by simp only [cut] at hr2; nlinarith
  have hcos2 : (43/50:ℝ)<Real.cos r^2 := by nlinarith
  have hcos1 : Real.cos r^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq r,sq_nonneg (Real.sin r)]
  have hsin := (transport_trig (angle_domain hr)).2.2.1
  have hsine := (Real.sin_le hr.1).trans hr.2
  refine ⟨?_,?_,?_,?_⟩
  · unfold secSq
    apply (le_div_iff₀ (pow_pos hcos 2)).2
    simpa using hcos1
  · unfold secSq
    apply (div_lt_iff₀ (pow_pos hcos 2)).2
    nlinarith only [hcos2]
  · exact div_nonneg hsin (sq_nonneg _)
  · unfold secTan
    apply (div_lt_iff₀ (pow_pos hcos 2)).2
    simp only [cut] at hsine
    nlinarith only [hcos2,hsine]

theorem upper_negative_slope {P r : ℝ} (hP : P∈Ioo 0 (183/200:ℝ))
    (hr : r∈Icc 0 cut) : capD P (-K) r<0 := by
  have hb := secant_bounds hr
  have hh := mul_le_mul hP.2.le hb.2.2.2.le hb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  rw [capD_identity]
  simp only [K]
  nlinarith [hb.1]

theorem lower_negative_slope {B r : ℝ} (hB : B<9/10)
    (hr : r∈Icc 0 cut) : 0<capD (1/2-B) K r := by
  have hb := secant_bounds hr
  have hh := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hb.2.2.1
  rw [capD_identity]
  dsimp [K]
  nlinarith [hb.1,hb.2.2.2]

theorem lower_positive_slope {B r : ℝ} (hB : (1/2:ℝ)≤B)
    (hr : r∈Icc 0 cut) : capD (1/2-B) (-k0) r<0 := by
  have hb := secant_bounds hr
  have hh := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1/2-B≤0) hb.2.2.1
  rw [capD_identity]
  dsimp [k0]
  nlinarith [hb.1]

theorem Uminus_antitone {P : ℝ} (hP : P∈Ioo 0 (183/200:ℝ)) :
    AntitoneOn (Uminus P) (Icc 0 cut) :=
  antiOn_of_hasDeriv_nonpos
    (fun r hr => (Uminus_hasDerivAt P hr).continuousAt.continuousWithinAt)
    (fun r hr => Uminus_hasDerivAt P (Ioo_subset_Icc_self hr))
    (fun r hr => (upper_negative_slope hP (Ioo_subset_Icc_self hr)).le)

theorem Lminus_monotone {B : ℝ} (hB : B<9/10) :
    MonotoneOn (Lminus B) (Icc 0 cut) :=
  monoOn_of_hasDeriv_nonneg
    (fun r hr => (Lminus_hasDerivAt B hr).continuousAt.continuousWithinAt)
    (fun r hr => Lminus_hasDerivAt B (Ioo_subset_Icc_self hr))
    (fun r hr => (lower_negative_slope hB (Ioo_subset_Icc_self hr)).le)

theorem Lplus_antitone {B : ℝ} (hB : (1/2:ℝ)≤B) :
    AntitoneOn (Lplus B) (Icc 0 cut) :=
  antiOn_of_hasDeriv_nonpos
    (fun r hr => (Lplus_hasDerivAt B hr).continuousAt.continuousWithinAt)
    (fun r hr => Lplus_hasDerivAt B (Ioo_subset_Icc_self hr))
    (fun r hr => (lower_positive_slope hB (Ioo_subset_Icc_self hr)).le)

theorem Lminus_lower {B r : ℝ} (hB : B<9/10) (hr : r∈Icc 0 cut) :
    (1/10:ℝ)<Lminus B r := by
  have hh := Lminus_monotone hB (show (0:ℝ)∈Icc 0 cut by norm_num [cut]) hr hr.1
  rw [Lminus_zero] at hh
  linarith

theorem common_derivative_reserve {P B x y : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hx : x∈Icc 0 cut) (hy : y∈Icc 0 cut) :
    (2/5:ℝ)< -capD P (-K) x+capD (1/2-B) (-k0) y ∧
    (2/5:ℝ)< -capD P k0 y+capD (1/2-B) K x := by
  have hxb := secant_bounds hx
  have hyb := secant_bounds hy
  have hPx := mul_le_mul hP.2.le hxb.2.2.2.le hxb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hPy := mul_le_mul hP.2.le hyb.2.2.2.le hyb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hBx := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hxb.2.2.1
  have hBy := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hyb.2.2.1
  rw [capD_identity,capD_identity,capD_identity,capD_identity]
  dsimp [K,k0]
  constructor <;> nlinarith [hxb.1,hyb.2.1,hxb.2.2.2,hyb.2.2.2]

def gap (negativeGA : Bool) (P B n p τ : ℝ) : ℝ :=
  if negativeGA then Uminus P (n-τ)-Lplus B (p-τ)
  else Uplus P (p-τ)-Lminus B (n-τ)

def gapD (negativeGA : Bool) (P B n p τ : ℝ) : ℝ :=
  if negativeGA then -capD P (-K) (n-τ)+capD (1/2-B) (-k0) (p-τ)
  else -capD P k0 (p-τ)+capD (1/2-B) K (n-τ)

theorem motion_angles {n p τ : ℝ} (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n)
    (hτ : τ∈Icc 0 p) : n-τ∈Icc 0 cut ∧ p-τ∈Icc 0 cut := by
  exact ⟨⟨by linarith [hτ.2,hp.2],by linarith [hn.2,hτ.1]⟩,
    ⟨by linarith [hτ.2],by linarith [hn.2,hp.2,hτ.1]⟩⟩

theorem gap_hasDerivAt (negativeGA : Bool) (P B : ℝ) {n p τ : ℝ}
    (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p) :
    HasDerivAt (gap negativeGA P B n p) (gapD negativeGA P B n p τ) τ := by
  have hm := motion_angles hn hp hτ
  cases negativeGA
  · have h1 := (Uplus_hasDerivAt P hm.2).comp τ ((hasDerivAt_id' τ).const_sub p)
    have h2 := (Lminus_hasDerivAt B hm.1).comp τ ((hasDerivAt_id' τ).const_sub n)
    convert h1.sub h2 using 1
    · funext x; simp [gap]
    · simp only [gapD,Bool.false_eq_true,↓reduceIte]; ring
  · have h1 := (Uminus_hasDerivAt P hm.1).comp τ ((hasDerivAt_id' τ).const_sub n)
    have h2 := (Lplus_hasDerivAt B hm.2).comp τ ((hasDerivAt_id' τ).const_sub p)
    convert h1.sub h2 using 1
    · funext x; simp [gap]
    · simp only [gapD,↓reduceIte]; ring

theorem gap_growth (negativeGA : Bool) {P B n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p) :
    gap negativeGA P B n p 0+(2/5)*τ≤gap negativeGA P B n p τ := by
  have hm : MonotoneOn (fun τ => gap negativeGA P B n p τ-(2/5)*τ) (Icc 0 p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun τ hτ => ((gap_hasDerivAt negativeGA P B hn hp hτ).sub
        ((hasDerivAt_id τ).const_mul (2/5:ℝ))).continuousAt.continuousWithinAt)
      (fun τ hτ => (gap_hasDerivAt negativeGA P B hn hp (Ioo_subset_Icc_self hτ)).sub
        ((hasDerivAt_id τ).const_mul (2/5:ℝ)))
    intro τ hτ
    have hangles := motion_angles hn hp (Ioo_subset_Icc_self hτ)
    have hres := common_derivative_reserve hP hB hangles.1 hangles.2
    cases negativeGA <;> dsimp [gapD] <;> linarith
  have hh := hm ⟨le_rfl,hp.1⟩ hτ hτ.1
  simp only [mul_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.MixedNegativeA
