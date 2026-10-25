module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EParameters
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the exact flat-core-E secant gain and its derivatives

The same gain is used for DE3 and EH1; their separate secants
cancel the signed E tangent before these scalar comparisons.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Arithmetic

def g (s : ℝ) : ℝ := (K*Real.sin s-a*(1-Real.cos s))/Real.cos s
def gd (s : ℝ) : ℝ := (K-a*Real.sin s)/Real.cos s^2
def numerator (s : ℝ) : ℝ := 2*K*Real.sin s-a*(1+Real.sin s^2)
def gdd (s : ℝ) : ℝ := numerator s/Real.cos s^3
def ratioNumerator (s : ℝ) : ℝ := s*gd s-g s

theorem cosine_pos {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<Real.cos s :=
  transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)

@[simp] theorem g_zero : g 0=0 := by norm_num [g]
@[simp] theorem ratioNumerator_zero : ratioNumerator 0=0 := by simp [ratioNumerator]

theorem g_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) : HasDerivAt g (gd s) s := by
  have hc := (cosine_pos hs).ne'
  have hh := (((Real.hasDerivAt_sin s).const_mul K).fun_sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul a)).fun_div (Real.hasDerivAt_cos s) hc
  refine (show HasDerivAt g _ s from hh).congr_deriv ?_
  rw [gd]
  congr 1
  linear_combination K*Real.sin_sq_add_cos_sq s

theorem gd_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) : HasDerivAt gd (gdd s) s := by
  have hc := (cosine_pos hs).ne'
  have hh := (((Real.hasDerivAt_sin s).const_mul a).const_sub K).fun_div
    ((Real.hasDerivAt_cos s).fun_pow 2) (pow_ne_zero 2 hc)
  refine (show HasDerivAt gd _ s from hh).congr_deriv ?_
  rw [gdd,numerator,div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hc)) (pow_ne_zero 3 hc)]
  rw [show (2:ℕ)-1=1 from rfl,pow_one]
  push_cast
  linear_combination (-a*Real.cos s^4)*Real.sin_sq_add_cos_sq s

theorem numerator_hasDerivAt (s : ℝ) :
    HasDerivAt numerator (2*Real.cos s*(K-a*Real.sin s)) s := by
  have hh := ((Real.hasDerivAt_sin s).const_mul (2*K)).fun_sub
    ((((Real.hasDerivAt_sin s).fun_pow 2).const_add 1).const_mul a)
  refine (show HasDerivAt numerator _ s from hh).congr_deriv ?_
  rw [show (2:ℕ)-1=1 from rfl,pow_one]
  push_cast
  ring

theorem numerator_monotone : MonotoneOn numerator (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (numerator_hasDerivAt s).continuousAt.continuousWithinAt)
    (fun s _ => numerator_hasDerivAt s)
  intro s hs
  have ht := transport_trig (Ioo_subset_Icc_self hs)
  have hk : 0<K-a*Real.sin s := by dsimp [K,a]; linarith [ht.2.2.2.1]
  exact mul_nonneg (by linarith [ht.1]) hk.le

theorem ratioNumerator_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt ratioNumerator (s*gdd s) s := by
  have hh := ((hasDerivAt_id s).fun_mul (gd_hasDerivAt hs)).fun_sub (g_hasDerivAt hs)
  convert hh using 1
  · funext x
    simp only [ratioNumerator,id]
  · simp only [id]
    ring

def capC6 : ℝ := 1-frameCap^2/2+frameCap^4/24-frameCap^6/720
def capS7 : ℝ := sin7 frameCap
def capC8 : ℝ := cos8 frameCap

theorem cap_trig_bounds :
    0<capS7 ∧ capS7≤Real.sin frameCap ∧
    0<capC6 ∧ capC6≤Real.cos frameCap ∧ Real.cos frameCap≤capC8 := by
  have hh : 0≤frameCap := by norm_num [frameCap]
  refine ⟨by norm_num [capS7,sin7,frameCap],?_,
    by norm_num [capC6,frameCap],cos_lower_six hh,cos_le_cos8 hh⟩
  simpa [capS7,sin7] using sin_lower_seven hh

theorem ratioNumerator_cap_identity :
    Real.cos frameCap^2*ratioNumerator frameCap=
      K*frameCap-a*frameCap*Real.sin frameCap-
      K*Real.sin frameCap*Real.cos frameCap+a*Real.cos frameCap-a*Real.cos frameCap^2 := by
  have hc := (cosine_pos (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)).ne'
  dsimp [ratioNumerator,gd,g]
  field_simp [hc]
  ring

theorem ratioNumerator_cap_negative : ratioNumerator frameCap<0 := by
  have ht := cap_trig_bounds
  have hp := mul_le_mul ht.2.1 ht.2.2.2.1 ht.2.2.1.le
    (by linarith [ht.1,ht.2.1] : 0≤Real.sin frameCap)
  have hsq := pow_le_pow_left₀ ht.2.2.1.le ht.2.2.2.1 2
  have hupper : Real.cos frameCap^2*ratioNumerator frameCap≤
      K*frameCap-a*frameCap*capS7-K*capS7*capC6+a*capC8-a*capC6^2 := by
    rw [ratioNumerator_cap_identity]
    dsimp [K,a,frameCap] at *
    nlinarith [ht.2.2.2.2]
  have he : K*frameCap-a*frameCap*capS7-K*capS7*capC6+a*capC8-a*capC6^2=
      -(3654654647214851707/155520000000000000000:ℝ) := by
    norm_num [K,a,frameCap,capS7,capC6,capC8,sin7,cos8]
  have hc := cosine_pos (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)
  rw [he] at hupper
  nlinarith [sq_pos_of_pos hc]

theorem ratioNumerator_nonpos {s : ℝ} (hs : s∈Icc 0 frameCap) : ratioNumerator s≤0 := by
  by_cases hn : numerator s≤0
  · have hm : AntitoneOn ratioNumerator (Icc 0 s) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun z hz => (ratioNumerator_hasDerivAt ⟨hz.1,hz.2.trans hs.2⟩).continuousAt.continuousWithinAt)
        (fun z hz => ratioNumerator_hasDerivAt ⟨hz.1.le,hz.2.le.trans hs.2⟩)
      intro z hz
      have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2.le.trans hs.2⟩
      have hnum := (numerator_monotone hzi hs hz.2.le).trans hn
      exact mul_nonpos_of_nonneg_of_nonpos hz.1.le
        (div_nonpos_of_nonpos_of_nonneg hnum (pow_nonneg (cosine_pos hzi).le 3))
    simpa only [ratioNumerator_zero] using
      hm ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1
  · have hm : MonotoneOn ratioNumerator (Icc s frameCap) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun z hz => (ratioNumerator_hasDerivAt ⟨hs.1.trans hz.1,hz.2⟩).continuousAt.continuousWithinAt)
        (fun z hz => ratioNumerator_hasDerivAt ⟨hs.1.trans hz.1.le,hz.2.le⟩)
      intro z hz
      have hzi : z∈Icc 0 frameCap := ⟨hs.1.trans hz.1.le,hz.2.le⟩
      have hnum := (lt_of_not_ge hn).le.trans (numerator_monotone hs hzi hz.1.le)
      exact mul_nonneg hzi.1 (div_nonneg hnum (pow_nonneg (cosine_pos hzi).le 3))
    exact (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2).trans ratioNumerator_cap_negative.le

theorem ratio_antitone {s t : ℝ} (hs : 0<s) (ht : t≤frameCap) (hst : s≤t) :
    g t/t≤g s/s := by
  have hm : AntitoneOn (fun z => g z/z) (Icc s t) := by
    apply antiOn_of_hasDeriv_nonpos (d:=fun z => ratioNumerator z/z^2)
    · intro z hz
      exact ((g_hasDerivAt ⟨(hs.trans_le hz.1).le,hz.2.trans ht⟩).fun_div
        (hasDerivAt_id z) (hs.trans_le hz.1).ne').continuousAt.continuousWithinAt
    · intro z hz
      refine ((g_hasDerivAt ⟨(hs.trans hz.1).le,hz.2.le.trans ht⟩).fun_div
        (hasDerivAt_id z) (hs.trans hz.1).ne').congr_deriv ?_
      simp only [ratioNumerator,id]
      ring
    · intro z hz
      exact div_nonpos_of_nonpos_of_nonneg
        (ratioNumerator_nonpos ⟨(hs.trans hz.1).le,hz.2.le.trans ht⟩) (sq_nonneg z)
  exact hm ⟨le_rfl,hst⟩ ⟨hst,le_rfl⟩ hst

theorem gain_pair {s t : ℝ} (hs : 0≤ s) (ht : 0≤t) (hsum : s+t≤frameCap) :
    g (s+t)≤g s+g t := by
  by_cases hs0 : s=0
  · simp [hs0]
  by_cases ht0 : t=0
  · simp [ht0]
  have hsp : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hst : 0<s+t := add_pos hsp htp
  have h1 := (div_le_div_iff₀ hst hsp).1 (ratio_antitone hsp hsum (by linarith))
  have h2 := (div_le_div_iff₀ hst htp).1 (ratio_antitone htp hsum (by linarith))
  have hh : g (s+t)*(s+t)≤(g s+g t)*(s+t) := by linarith only [h1,h2]
  exact le_of_mul_le_mul_right hh hst

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
