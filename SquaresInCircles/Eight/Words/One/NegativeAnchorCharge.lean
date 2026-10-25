module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.CorrelatedSameBlock
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars

/-!
# Eight squares: the strict positive HG charge at the remaining negative-BT endpoint

The two support formulas use the original exact circle radius.  Their
strict lower bounds follow from concavity on each complete analytic
branch and rational Taylor bounds at its endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorCharge
open PositiveAngularEnvelope CorrelatedSameBlock

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev k0 : ℝ := EndpointBudgetScalars.k0
def p : ℝ := 41/40

def short (v : ℝ) : ℝ :=
  p*v-k0*Real.sin v-(1-Real.cos v)/2

def long (v : ℝ) : ℝ :=
  p*v-2*R*Real.sin (v/2)+Real.sin v

def f (v : ℝ) : ℝ := if v≤1/2 then short v else long v

theorem radius_upper : R<(197878751/100000000 : ℝ) := by
  have hs := EndpointRotationPenalty.R_sq
  have hn := EndpointRotationPenalty.R_nonneg
  dsimp [qCap] at hs
  nlinarith

theorem k0_bounds : 0≤k0 ∧ k0<(914576/1000000 : ℝ) := by
  have hh := EndpointBudgetScalars.radical_bounds
  exact ⟨by linarith [hh.1],hh.2.1⟩

@[simp] theorem short_zero : short 0=0 := by simp [short]

theorem short_taylor_lower {v : ℝ} (hv : v∈Icc 0 frameCap) :
    p*v-(914576/1000000)*(v-v^3/6+v^5/120)-
      (1-(1-v^2/2+v^4/24-v^6/720))/2≤ short v := by
  have hm := mul_le_mul k0_bounds.2.le (sin_upper_five hv.1)
    (transport_trig hv).2.2.1 (by norm_num : (0:ℝ)≤914576/1000000)
  have hc := cos_lower_six hv.1
  dsimp [short]
  linarith

theorem short_endpoints :
    (1/250 : ℝ)<short (1/25) ∧ (1/250 : ℝ)<short (1/2) := by
  have hleft := short_taylor_lower
    (show (1/25 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hright := short_taylor_lower
    (show (1/2 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [p] at hleft hright
  constructor <;> linarith

theorem short_concave : ConcaveOn ℝ (Icc 0 (1/2 : ℝ)) short := by
  apply concave_of_deriv2
    (f' := fun v => p-k0*Real.cos v-Real.sin v/2)
    (f'' := fun v => k0*Real.sin v-Real.cos v/2)
  · intro v _
    have hraw := (((hasDerivAt_id v).const_mul p).sub
      ((Real.hasDerivAt_sin v).const_mul k0)).sub
        (((Real.hasDerivAt_cos v).const_sub 1).div_const 2)
    convert hraw using 1
    · rfl
    · ring
  · intro v _
    convert (((hasDerivAt_const v p).sub
      ((Real.hasDerivAt_cos v).const_mul k0)).sub
        ((Real.hasDerivAt_sin v).div_const 2)) using 1 <;> ring
  · intro v hv
    have hv' : v∈Icc 0 frameCap := ⟨hv.1,by dsimp [frameCap]; linarith [hv.2]⟩
    have hh : (1/2 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
    have hs := (sin_mono hv' hh hv.2).trans (sin_upper_five (by norm_num : (0:ℝ)≤1/2))
    have hc := (cos_lower_six (by norm_num : (0:ℝ)≤1/2)).trans (cos_anti hv' hh hv.2)
    have hm := mul_le_mul k0_bounds.2.le hs (transport_trig hv').2.2.1
      (by norm_num : (0:ℝ)≤914576/1000000)
    norm_num at hm hc
    linarith

theorem short_positive {v : ℝ} (hv : v∈Ioc 0 (1/2 : ℝ)) : 0<short v :=
  concave_pos_of_zero_left short_concave hv short_zero (by linarith [short_endpoints.2])

theorem short_reserve {v : ℝ} (hv : v∈Icc (1/25 : ℝ) (1/2)) :
    (1/250 : ℝ)<short v := by
  have hm := short_concave.min_le_of_mem_Icc
    (show (1/25 : ℝ)∈Icc 0 (1/2) by norm_num)
    (show (1/2 : ℝ)∈Icc 0 (1/2) by norm_num) hv
  exact (lt_min short_endpoints.1 short_endpoints.2).trans_le hm

theorem long_taylor_lower {v : ℝ} (hv : v∈Icc 0 frameCap) :
    p*v-2*(197878751/100000000)*
      (v/2-(v/2)^3/6+(v/2)^5/120)+
      (v-v^3/6+v^5/120-v^7/5040)≤long v := by
  have hh : v/2∈Icc 0 frameCap := by
    constructor <;> dsimp [frameCap] at * <;> linarith [hv.1,hv.2]
  have hm := mul_le_mul radius_upper.le (sin_upper_five hh.1)
    (transport_trig hh).2.2.1 (by norm_num : (0:ℝ)≤197878751/100000000)
  have hs := sin_lower_seven hv.1
  dsimp [long]
  linarith

theorem long_endpoints :
    (1/250 : ℝ)<long (1/2) ∧ (1/250 : ℝ)<long frameCap := by
  have hleft := long_taylor_lower
    (show (1/2 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hright := long_taylor_lower
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [p,frameCap] at hleft hright
  constructor <;> linarith

theorem long_concave : ConcaveOn ℝ (Icc (1/2 : ℝ) frameCap) long := by
  apply concave_of_deriv2
    (f' := fun v => p-R*Real.cos (v/2)+Real.cos v)
    (f'' := fun v => (R/2)*Real.sin (v/2)-Real.sin v)
  · intro v _
    have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) v := (hasDerivAt_id' v).div_const 2
    have hraw : HasDerivAt long (p*1-2*R*(Real.cos (v/2)*(1/2))+Real.cos v) v :=
      (((hasDerivAt_id' v).const_mul p).fun_sub
        (hh.sin.const_mul (2*R))).fun_add (Real.hasDerivAt_sin v)
    convert hraw using 1
    ring
  · intro v _
    have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) v := (hasDerivAt_id' v).div_const 2
    have hraw : HasDerivAt (fun v => p-R*Real.cos (v/2)+Real.cos v)
        (0-R*(-Real.sin (v/2)*(1/2))+-Real.sin v) v :=
      (((hasDerivAt_const v p).fun_sub (hh.cos.const_mul R))).fun_add (Real.hasDerivAt_cos v)
    convert hraw using 1
    ring
  · intro v hv
    have hh : v/2∈Icc 0 frameCap := by
      constructor <;> dsimp [frameCap] at * <;> linarith [hv.1,hv.2]
    obtain ⟨hc,_,hs,_,_⟩ := transport_trig hh
    have hr : R<2 := by linarith [radius_upper]
    have hm := mul_nonneg hs (show 0≤2*Real.cos (v/2)-R/2 by linarith)
    have hid : Real.sin v=2*Real.sin (v/2)*Real.cos (v/2) := by
      calc
        Real.sin v=Real.sin (v/2+v/2) := by congr 1; ring
        _=2*Real.sin (v/2)*Real.cos (v/2) := by rw [Real.sin_add]; ring
    show (R/2)*Real.sin (v/2)-Real.sin v ≤ 0
    rw [hid]
    linarith

theorem long_reserve {v : ℝ} (hv : v∈Icc (1/2 : ℝ) frameCap) :
    (1/250 : ℝ)<long v :=
  (lt_min long_endpoints.1 long_endpoints.2).trans_le
    (long_concave.min_le_of_mem_Icc
      (show (1/2 : ℝ)∈Icc (1/2) frameCap by norm_num [frameCap])
      (show frameCap∈Icc (1/2 : ℝ) frameCap by norm_num [frameCap]) hv)

theorem f_of_short {v : ℝ} (hv : v≤1/2) : f v=short v := by
  simp only [f,ite_eq_left hv]

theorem f_of_long {v : ℝ} (hv : 1/2<v) : f v=long v := by
  simp only [f,ite_eq_right (not_le.mpr hv)]

/-- Positive at every original strictly positive HG error. -/
theorem f_pos {v : ℝ} (hv : v∈Ioc 0 frameCap) : 0<f v := by
  by_cases hshort : v≤1/2
  · rw [f_of_short hshort]
    exact short_positive ⟨hv.1,hshort⟩
  · rw [f_of_long (lt_of_not_ge hshort)]
    have hh := long_reserve ⟨(lt_of_not_ge hshort).le,hv.2⟩
    linarith

/-- The strict reserve needed by the varying-weight middle endpoint. -/
theorem f_reserve {v : ℝ} (hv : v∈Icc (1/25 : ℝ) frameCap) :
    (1/250 : ℝ)<f v := by
  by_cases hshort : v≤1/2
  · rw [f_of_short hshort]
    exact short_reserve ⟨hv.1,hshort⟩
  · rw [f_of_long (lt_of_not_ge hshort)]
    exact long_reserve ⟨(lt_of_not_ge hshort).le,hv.2⟩

end SquaresInCircles.Eight.OneNegativeAnchorCharge
