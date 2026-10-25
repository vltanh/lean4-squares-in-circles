module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.Positive.TDSpanPolynomials
public import SquaresInCircles.Eight.Owners.TD0Span

/-!
# Eight squares: positive-TD2 span: the four intrinsic boundaries of the scalar domain

The continuous weight depends on the unchanged A--T
frame difference. At fixed difference the scalar is concave in the short
negative-GA error. Its two endpoints are four intrinsic polygon edges.
One follows from the fixed-weight span reserve; the other three use their
explicit whole-interval polynomials, with every Taylor direction proved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveTDSpanScalars
open SpanNormBounds PositiveAngularEnvelope

abbrev k : ℝ := EndpointBudgetScalars.k0

def weight (v : ℝ) : ℝ := 59/100+(47/100)*v
def base (t v l : ℝ) : ℝ :=
  TD0Span.f t+2+2*l+Real.cos v-c-R*(N l 0+N l (-v))
def F (t v w : ℝ) : ℝ := base t v (weight v)-EndpointBudgetScalars.positiveGain w

theorem N_formula (l z : ℝ) : N l z=Real.sqrt (1+l^2+2*l*Real.sin z) := by
  unfold N pairNorm
  congr 1
  ring

theorem weight_bounds {v : ℝ} (hv : v∈Icc (13/100:ℝ) frameCap) :
    weight v∈Icc (13/20:ℝ) (23/25) := by
  dsimp [weight,frameCap] at *
  constructor <;> linarith [hv.1,hv.2]

theorem base_as_stress (t v l : ℝ) :
    base t v l=TD0Span.f t+3+2*l-c-2*R*N l 0+V l v := by
  simp [base,SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N]
  ring

theorem base_fixed (t v : ℝ) :
    base t v TD0Span.lambda=TD0Span.f t+3+2*TD0Span.lambda-c-
      2*R*N TD0Span.lambda 0+V TD0Span.lambda v := base_as_stress t v TD0Span.lambda

theorem norm_weight_deriv {l z : ℝ} (hl : 0<l) (hz : |z|≤frameCap) :
    HasDerivAt (fun a => N a z) ((l+Real.sin z)/N l z) l := by
  have hr := PairNormCalculus.pair_radicand_pos hl (show (0:ℝ)<1 by norm_num) hz
  have hN0 := N_pos hl hz
  have hr0 : 1+l^2+2*l*Real.sin z≠0 := by
    have : 0<1+l^2+2*l*Real.sin z := by nlinarith [hr]
    exact this.ne'
  have h1 : HasDerivAt (fun a : ℝ => a^2) (2*l) l := by simpa using hasDerivAt_pow 2 l
  have h2 : HasDerivAt (fun a : ℝ => 1+a^2+2*a*Real.sin z) (2*l+2*Real.sin z) l := by
    have h := (h1.const_add 1).add ((hasDerivAt_id' l).mul_const (2*Real.sin z))
    have hf : (fun a : ℝ => 1+a^2+2*a*Real.sin z)=fun a => 1+a^2+a*(2*Real.sin z) := by
      funext a; ring
    rw [hf]
    exact h.congr_deriv (by ring)
  have h3 := h2.sqrt hr0
  have hf : (fun a => N a z)=fun a => Real.sqrt (1+a^2+2*a*Real.sin z) := by
    funext a; exact N_formula a z
  rw [hf]
  refine h3.congr_deriv ?_
  have hs : Real.sqrt (1+l^2+2*l*Real.sin z)≠0 := by rw [← N_formula]; exact hN0.ne'
  rw [N_formula]
  field_simp

theorem base_weight_deriv {t v l : ℝ} (hl : 0<l) (hv : |v|≤frameCap) :
    HasDerivAt (base t v)
      (2-R*(l/N l 0+(l-Real.sin v)/N l (-v))) l := by
  have hd0 := norm_weight_deriv hl (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hdv := norm_weight_deriv hl (show |-v|≤frameCap by simpa using hv)
  have hlin : HasDerivAt (fun a : ℝ => TD0Span.f t+2+2*a+Real.cos v-c) (2*1) l :=
    ((((hasDerivAt_id' l).const_mul (2:ℝ)).const_add (TD0Span.f t+2)).add_const
      (Real.cos v)).sub_const c
  have h := hlin.sub ((hd0.add hdv).const_mul R)
  rw [Real.sin_zero,add_zero,Real.sin_neg,← sub_eq_add_neg] at h
  show HasDerivAt (fun a => TD0Span.f t+2+2*a+Real.cos v-c-R*(N a 0+N a (-v))) _ l
  exact h.congr_deriv (by ring)

/-- Positive-square ratio bounds on the whole coefficient rectangle.
They retain the actual norm denominators and have no sampled premise. -/
theorem aligned_ratio_bounds {l v : ℝ}
    (hl : l∈Icc (13/20:ℝ) (7/10)) (hv : v∈Icc (13/100:ℝ) (11/50)) :
    l/N l 0≤1147/2000 ∧ (l-Real.sin v)/N l (-v)≤4987/10000 := by
  have hl0 : 0<l := by linarith [hl.1]
  have hvi : v∈Icc 0 frameCap := ⟨by linarith [hv.1],by norm_num [frameCap] at *; linarith [hv.2]⟩
  have hvabs : |v|≤frameCap := by rw [abs_of_nonneg hvi.1]; exact hvi.2
  have hN0 := N_pos hl0 (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hNv := N_pos hl0 (show |-v|≤frameCap by simpa using hvabs)
  have hZ := N_sq hl0 (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hM := N_sq hl0 (show |-v|≤frameCap by simpa using hvabs)
  simp only [Real.sin_zero,Real.sin_neg] at hZ hM
  have hl2 := pow_le_pow_left₀ hl0.le hl.2 2
  have hs0 : (12963/100000:ℝ)≤Real.sin v := by
    have hs13 := sin_lower_seven (show (0:ℝ)≤13/100 by norm_num)
    have hm := CorrelatedSameBlock.sin_mono
      (show (13/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hvi hv.1
    norm_num at hs13
    linarith
  have hsu : Real.sin v≤11/50 := (Real.sin_le hvi.1).trans hv.2
  have hfirst : l≤(1147/2000)*N l 0 := by
    nlinarith
  have hz0 : 0≤l-Real.sin v := by linarith [hl.1]
  let r : ℝ := 4987/10000
  let z := Real.sin v
  have hfactorA := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hl.2) (show 0≤1-r^2 by norm_num [r]))
    (show 0≤7/10+l-2*z by dsimp [z]; linarith [hl.1])
  have hfactorZ := mul_nonneg (show 0≤z-12963/100000 by exact sub_nonneg.mpr hs0)
    (show 0≤2*(7/10)*(1-r^2)-z-12963/100000 by dsimp [r,z]; linarith)
  have hidA : r^2*(1+l^2-2*l*z)-(l-z)^2-
      (r^2*(1+(7/10:ℝ)^2-2*(7/10)*z)-(7/10-z)^2)=
      (7/10-l)*(1-r^2)*(7/10+l-2*z) := by ring
  have hidZ : r^2*(1+(7/10:ℝ)^2-2*(7/10)*z)-(7/10-z)^2-
      (r^2*(1+(7/10:ℝ)^2-2*(7/10)*(12963/100000))-(7/10-12963/100000)^2)=
      (z-12963/100000)*(2*(7/10)*(1-r^2)-z-12963/100000) := by ring
  have hpoly : 0≤r^2*(1+l^2-2*l*z)-(l-z)^2 := by
    norm_num [r] at hidA hidZ hfactorA hfactorZ ⊢
    linarith
  have hsecond : l-Real.sin v≤(4987/10000)*N l (-v) := by
    apply le_of_sq_le_sq _ (mul_pos (by norm_num) hNv).le
    rw [mul_pow,hM]
    dsimp [r,z] at hpoly
    linarith
  exact ⟨(div_le_iff₀ hN0).2 hfirst,(div_le_iff₀ hNv).2 hsecond⟩

theorem base_weight_lower {l v : ℝ}
    (hl : l∈Icc (13/20:ℝ) (7/10)) (hv : v∈Icc (13/100:ℝ) (11/50)) :
    -(61/500:ℝ)≤2-R*(l/N l 0+(l-Real.sin v)/N l (-v)) := by
  obtain ⟨h0,h1⟩ := aligned_ratio_bounds hl hv
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hm := mul_le_mul_of_nonneg_left (add_le_add h0 h1) hR0
  have hR := radius_bounds.2
  have hmul := mul_le_mul_of_nonneg_right hR.le
    (show (0:ℝ)≤1147/2000+4987/10000 by norm_num)
  linarith

theorem aligned_boundary {v : ℝ} (hv : v∈Icc (13/100:ℝ) (11/50)) :
    0<F (11/50-v) v 0 := by
  have hti : 11/50-v∈Icc 0 (9/100:ℝ) := ⟨by linarith [hv.2],by linarith [hv.1]⟩
  have hvi : v∈Icc 0 frameCap := ⟨by linarith [hv.1],by norm_num [frameCap] at *; linarith [hv.2]⟩
  have hl : weight v∈Icc (13/20:ℝ) (7/10) := by
    dsimp [weight]
    constructor <;> linarith [hv.1,hv.2]
  have hx : (13/20:ℝ)∈Icc (13/20:ℝ) (7/10) := by norm_num
  have hd (l : ℝ) (hl : l∈Icc (13/20:ℝ) (7/10)) :=
    base_weight_deriv (t := 11/50-v) (show 0<l by linarith [hl.1])
      (show |v|≤frameCap by rw [abs_of_nonneg hvi.1]; exact hvi.2)
  have hg := derivative_reserve
    (fun l hl => (hd l hl).continuousAt.continuousWithinAt)
    (fun l hl => hd l (Ioo_subset_Icc_self hl))
    (fun l hl => base_weight_lower (Ioo_subset_Icc_self hl) hv) hx hl hl.1
  have hfixed := TD0Span.scalar_reserve hti hvi (by linarith)
  rw [← base_fixed] at hfixed
  have hdiff : weight v-13/20≤217/5000 := by dsimp [weight]; linarith [hv.2]
  simp [F,EndpointBudgetScalars.positiveGain]
  dsimp [TD0Span.lambda] at hfixed
  linarith

theorem boundary_data (i : PositiveTDSpanPolynomials.Edge) {v : ℝ}
    (hv : v∈Icc (PositiveTDSpanPolynomials.lo i:ℝ) (PositiveTDSpanPolynomials.hi i:ℝ)) :
    Polynomial.aeval v (PositiveTDSpanPolynomials.t i)∈Icc 0 (9/100:ℝ) ∧
      Polynomial.aeval v (PositiveTDSpanPolynomials.w i)∈Icc 0 (12/25:ℝ) ∧
      v∈Icc (13/100:ℝ) frameCap := by
  obtain ⟨h1,h2⟩ := hv
  cases i <;>
  · simp only [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,
      PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w,map_zero,map_sub,
      Polynomial.aeval_X,Polynomial.aeval_C,eq_ratCast,frameCap,Set.mem_Icc] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩ <;> linarith

theorem polynomial_boundary (i : PositiveTDSpanPolynomials.Edge) {v : ℝ}
    (hv : v∈Icc (PositiveTDSpanPolynomials.lo i:ℝ) (PositiveTDSpanPolynomials.hi i:ℝ)) :
    0<F (Polynomial.aeval v (PositiveTDSpanPolynomials.t i)) v
      (Polynomial.aeval v (PositiveTDSpanPolynomials.w i)) := by
  obtain ⟨ht,hw,hvi⟩ := boundary_data i hv
  obtain ⟨T,hT⟩ : ∃ T, Polynomial.aeval v (PositiveTDSpanPolynomials.t i)=T := ⟨_,rfl⟩
  obtain ⟨W,hW⟩ : ∃ W, Polynomial.aeval v (PositiveTDSpanPolynomials.w i)=W := ⟨_,rfl⟩
  rw [hT] at ht
  rw [hW] at hw
  rw [hT,hW]
  have hv0 : 0≤v := by linarith [hvi.1]
  have hl := weight_bounds hvi
  have hl0 : 0<weight v := by linarith [hl.1]
  have hsT := sin_lower_seven ht.1
  have hcT := cos_lower_six ht.1
  have hcV := cos_lower_six hv0
  have hsV := sin_lower_seven hv0
  have hsW := sin_upper_five hw.1
  have hcW := cos_lower_six hw.1
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have ht6 := pow_le_pow_left₀ ht.1 ht.2 6
  norm_num at ht2 ht6
  have hct0 : 0≤1-T^2/2+T^4/24-T^6/720 := by
    linarith [pow_nonneg ht.1 4]
  have hc := diagonal_bounds.2
  have hcoef := mul_le_mul
    (show (3/2-179843/200000:ℝ)≤3/2-c by linarith) hcT hct0 (show (0:ℝ)≤3/2-c by linarith)
  have hsW0 : 0≤Real.sin W :=
    Real.sin_nonneg_of_nonneg_of_le_pi hw.1 (by linarith [hw.2,Real.pi_gt_three])
  have hk := EndpointBudgetScalars.radical_bounds.2.1
  have hkS := mul_le_mul hk.le hsW hsW0 (by norm_num : (0:ℝ)≤914576/1000000)
  have hdem : Polynomial.aeval v (PositiveTDSpanPolynomials.demand i)=
      (2-179843/200000)+2*(59/100+(47/100)*v)
      +(3/2-179843/200000)*(1-T^2/2+T^4/24-T^6/720)
      +(13/12)*(T-T^3/6+T^5/120-T^7/5040)
      +(1-v^2/2+v^4/24-v^6/720)
      -(114322/125000)*(W-W^3/6+W^5/120)
      +(1/2)*(1-W^2/2+W^4/24-W^6/720) := by
    simp only [PositiveTDSpanPolynomials.demand,map_add,map_sub,map_mul,map_ofNat,
      Polynomial.aeval_C,eq_ratCast,PositiveTDSpanPolynomials.lambda_eval,
      PositiveTDSpanPolynomials.C6_eval,PositiveTDSpanPolynomials.S5_eval,
      PositiveTDSpanPolynomials.S7_eval,Polynomial.aeval_X,hT,hW,
      PositiveTDSpanPolynomials.cbar,PositiveTDSpanPolynomials.kbar]
    push_cast
    ring
  have hD : Polynomial.aeval v (PositiveTDSpanPolynomials.demand i)≤
      TD0Span.f T+2+2*weight v+Real.cos v-c-EndpointBudgetScalars.positiveGain W := by
    rw [hdem]
    simp only [TD0Span.f,EndpointBudgetScalars.positiveGain,weight]
    linarith only [hc,hcoef,hsT,hcV,hkS,hcW]
  have hp0 : 0≤1+(weight v)^2 := by positivity
  have hp1 : 0≤1+(weight v)^2-2*weight v*Real.sin v := by
    have hp := PairNormCalculus.pair_radicand_pos hl0 (show (0:ℝ)<1 by norm_num)
      (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv0]; exact hvi.2)
    simp only [one_pow,Real.sin_neg] at hp
    linarith
  have hp0u : 1+(weight v)^2≤Polynomial.aeval v PositiveTDSpanPolynomials.radicand0 := by
    simp [PositiveTDSpanPolynomials.radicand0,weight]
  have hp1u : 1+(weight v)^2-2*weight v*Real.sin v≤
      Polynomial.aeval v PositiveTDSpanPolynomials.radicand1 := by
    have hm := mul_le_mul_of_nonneg_left hsV (show 0≤2*weight v by positivity)
    have he : Polynomial.aeval v PositiveTDSpanPolynomials.radicand1=
        1+(weight v)^2-2*weight v*(v-v^3/6+v^5/120-v^7/5040) := by
      simp only [PositiveTDSpanPolynomials.radicand1,map_sub,map_add,map_one,map_pow,map_mul,
        map_ofNat,PositiveTDSpanPolynomials.lambda_eval,PositiveTDSpanPolynomials.S7_eval,
        Polynomial.aeval_X,weight]
    rw [he]
    linarith only [hm]
  have hRu : R≤((PositiveTDSpanPolynomials.Rbar:ℚ):ℝ) := by
    rw [show ((PositiveTDSpanPolynomials.Rbar:ℚ):ℝ)=494697/250000 by
      norm_num [PositiveTDSpanPolynomials.Rbar]]
    exact radius_bounds.2.le
  have hpos := PositiveTDSpanPolynomials.radical_transfer i hv hD
    (show (0:ℝ)≤R from Real.sqrt_nonneg qCap) hRu hp0 hp1 hp0u hp1u
  have hN0 : N (weight v) 0=Real.sqrt (1+(weight v)^2) := by
    rw [N_formula,Real.sin_zero]; congr 1; ring
  have hNv : N (weight v) (-v)=Real.sqrt (1+(weight v)^2-2*weight v*Real.sin v) := by
    rw [N_formula,Real.sin_neg]; congr 1; ring
  simp only [F,base,hN0,hNv]
  linarith only [hpos]

theorem gain_deriv (w : ℝ) :
    HasDerivAt EndpointBudgetScalars.positiveGain
      (k*Real.cos w+(1/2)*Real.sin w) w := by
  have h1 : HasDerivAt (fun x => k*Real.sin x) (k*Real.cos w) w :=
    (Real.hasDerivAt_sin w).const_mul _
  have h2 : HasDerivAt (fun x => (1-Real.cos x)/2) ((0- -Real.sin w)/2) w :=
    ((hasDerivAt_const w (1:ℝ)).sub (Real.hasDerivAt_cos w)).div_const 2
  have hfun : EndpointBudgetScalars.positiveGain=fun x => k*Real.sin x+(1-Real.cos x)/2 := by
    funext x; rfl
  rw [hfun]
  exact (h1.add h2).congr_deriv (by ring)

theorem gain_monotone : MonotoneOn EndpointBudgetScalars.positiveGain (Icc 0 (12/25:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · unfold EndpointBudgetScalars.positiveGain
    fun_prop
  · exact fun w _ => gain_deriv w
  · intro w hw
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig
      (show w∈Icc 0 frameCap by constructor <;> norm_num [frameCap] at * <;> linarith [hw.1,hw.2])
    have hk0 : 0≤k := by linarith [EndpointBudgetScalars.radical_bounds.1]
    exact add_nonneg (mul_nonneg hk0 (by linarith)) (mul_nonneg (by norm_num) hs0)

theorem gain_curvature {w : ℝ} (hw : w∈Icc 0 (12/25:ℝ)) :
    0≤(1/2)*Real.cos w-k*Real.sin w := by
  have hwi : w∈Icc 0 frameCap := ⟨hw.1,by norm_num [frameCap] at *; linarith [hw.2]⟩
  have he : (12/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos := CorrelatedSameBlock.cos_anti hwi he hw.2
  have hsin := CorrelatedSameBlock.sin_mono hwi he hw.2
  have hc48 := cos_lower_six (show (0:ℝ)≤12/25 by norm_num)
  have hs48 := sin_upper_five (show (0:ℝ)≤12/25 by norm_num)
  have hm := mul_le_mul EndpointBudgetScalars.radical_bounds.2.1.le (hsin.trans hs48)
    (transport_trig hwi).2.2.1 (by norm_num : (0:ℝ)≤914576/1000000)
  norm_num at hc48 hm
  linarith

/-- Concavity is in the short negative-GA error with v fixed. The weight
therefore stays fixed throughout this analytic comparison. -/
theorem fixed_v_concave {v : ℝ} (_hv : v∈Icc (13/100:ℝ) frameCap) :
    ConcaveOn ℝ (Icc (max 0 (11/50-v)) (min (9/100) (frameCap-v)))
      (fun t => F t v (t+v-11/50)) := by
  have hd1 : ∀ x, HasDerivAt (fun t => F t v (t+v-11/50))
      (-(3/2-c)*Real.sin x+(13/12)*Real.cos x-
        (k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50))) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => t+v-11/50) 1 x :=
      ((hasDerivAt_id' x).add_const v).sub_const (11/50)
    have hg0 := (gain_deriv (x+v-11/50)).comp x hlin
    have hg : HasDerivAt (fun t => EndpointBudgetScalars.positiveGain (t+v-11/50))
        ((k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50))*1) x := hg0
    have hf : HasDerivAt (fun t => TD0Span.f t+2+2*weight v+Real.cos v-c-
        R*(N (weight v) 0+N (weight v) (-v)))
        (-(3/2-c)*Real.sin x+(13/12)*Real.cos x) x :=
      (((((TD0Span.f_deriv x).add_const 2).add_const (2*weight v)).add_const
        (Real.cos v)).sub_const c).sub_const _
    exact (hf.sub hg).congr_deriv (by ring)
  have hd2 : ∀ x, HasDerivAt (fun x => -(3/2-c)*Real.sin x+(13/12)*Real.cos x-
        (k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50)))
      (-(3/2-c)*Real.cos x-(13/12)*Real.sin x+k*Real.sin (x+v-11/50)-
        (1/2)*Real.cos (x+v-11/50)) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => t+v-11/50) 1 x :=
      ((hasDerivAt_id' x).add_const v).sub_const (11/50)
    have hs : HasDerivAt (fun t => Real.sin (t+v-11/50)) (Real.cos (x+v-11/50)*1) x :=
      (Real.hasDerivAt_sin _).comp x hlin
    have hc : HasDerivAt (fun t => Real.cos (t+v-11/50)) (-Real.sin (x+v-11/50)*1) x :=
      (Real.hasDerivAt_cos _).comp x hlin
    have h := (((Real.hasDerivAt_sin x).const_mul (-(3/2-c))).add
      ((Real.hasDerivAt_cos x).const_mul (13/12:ℝ))).sub
      ((hc.const_mul k).add (hs.const_mul (1/2:ℝ)))
    exact h.congr_deriv (by ring)
  apply concave_of_deriv2 (fun x _ => hd1 x) (fun x _ => hd2 x)
  intro t ht
  have ht0 : 0≤t := (le_max_left _ _).trans ht.1
  have ht9 : t≤9/100 := ht.2.trans (min_le_left _ _)
  have hw0 : 0≤t+v-11/50 := by linarith [(le_max_right (0:ℝ) (11/50-v)).trans ht.1]
  have hw48 : t+v-11/50≤12/25 := by
    have h := ht.2.trans (min_le_right (9/100:ℝ) (frameCap-v))
    norm_num [frameCap] at h
    linarith
  have hcurv := gain_curvature ⟨hw0,hw48⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig
    (show t∈Icc 0 frameCap by constructor <;> norm_num [frameCap] at * <;> linarith)
  have hm := mul_nonneg (show 0≤3/2-c by linarith [diagonal_bounds.2])
    (show 0≤Real.cos t by linarith)
  nlinarith

/-- Strict positivity on the entire original scalar polygon, including
its four intrinsic boundary faces and all weak frame ties. -/
theorem domain_positive {t v w : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hv : v∈Icc (13/100:ℝ) frameCap)
    (htv : 11/50≤t+v ∧ t+v≤frameCap)
    (hw : w∈Icc 0 (t+v-11/50)) : 0<F t v w := by
  let l := max 0 (11/50-v)
  let r := min (9/100) (frameCap-v)
  have htr : t∈Icc l r := by
    constructor
    · exact max_le ht.1 (by linarith [htv.1])
    · exact le_min ht.2 (by linarith [htv.2])
  have hlr : l≤r := htr.1.trans htr.2
  have hleft : 0<F l v (l+v-11/50) := by
    by_cases h : 11/50≤v
    · have hl : l=0 := max_eq_left (by linarith)
      rw [hl]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.zero
        (show v∈Icc (PositiveTDSpanPolynomials.lo .zero:ℝ) (PositiveTDSpanPolynomials.hi .zero:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,frameCap] using And.intro h hv.2)
      simpa [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w] using hb
    · have hl : l=11/50-v := max_eq_right (by linarith)
      rw [hl]
      have hzero : (11/50-v)+v-11/50=0 := by ring
      rw [hzero]
      exact aligned_boundary ⟨hv.1,by linarith⟩
  have hright : 0<F r v (r+v-11/50) := by
    by_cases h : v≤61/100
    · have hr : r=9/100 := min_eq_left (by dsimp [frameCap]; linarith)
      rw [hr]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.short
        (show v∈Icc (PositiveTDSpanPolynomials.lo .short:ℝ) (PositiveTDSpanPolynomials.hi .short:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi] using And.intro hv.1 h)
      convert hb using 1 <;> simp [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w] <;> ring
    · have hr : r=frameCap-v := min_eq_right (by dsimp [frameCap]; linarith)
      rw [hr]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.spread
        (show v∈Icc (PositiveTDSpanPolynomials.lo .spread:ℝ) (PositiveTDSpanPolynomials.hi .spread:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,frameCap] using
            And.intro (by linarith : (61/100:ℝ)≤v) hv.2)
      convert hb using 1 <;> simp [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w,frameCap] <;> ring
  have hconc := fixed_v_concave hv
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr) htr
  have hp : 0<F t v (t+v-11/50) := (lt_min hleft hright).trans_le hmin
  have hlarge : t+v-11/50∈Icc 0 (12/25:ℝ) := by
    constructor <;> norm_num [frameCap] at * <;> linarith [htv.1,htv.2]
  have hsmall : w∈Icc 0 (12/25:ℝ) := ⟨hw.1,hw.2.trans hlarge.2⟩
  have hm := gain_monotone hsmall hlarge hw.2
  dsimp [F] at hp ⊢
  linarith

end SquaresInCircles.Eight.PositiveTDSpanScalars
