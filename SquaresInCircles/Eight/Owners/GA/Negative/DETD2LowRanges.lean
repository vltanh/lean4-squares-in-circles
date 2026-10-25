module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowD
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2SourceData

/-!
# Eight squares: the low coefficient domain before any E-angle concentration

The upper
bound on the tilted B coefficient is obtained from its actual increasing
split factor and its decreasing total-angle envelope. The tighter
coefficient bounds apply only after the original D support is interior.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowRanges
open Candidate Secondary PositiveAngularEnvelope

abbrev factor (z : ℝ) : ℝ := Real.cos z+Explicit.eta*Real.sin z
abbrev factorFirst (z : ℝ) : ℝ := -Real.sin z+Explicit.eta*Real.cos z

theorem factor_derivative (z : ℝ) : HasDerivAt factor (factorFirst z) z := by
  exact (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul Explicit.eta)

theorem factor_monotone : MonotoneOn factor (Icc (0:ℝ) (1/6)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (factor_derivative z).continuousAt.continuousWithinAt)
    (fun z _ => factor_derivative z)
  intro z hz
  have hz' := Ioo_subset_Icc_self hz
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hs := Real.sin_le hz'.1
  have hz2 := pow_le_pow_left₀ hz'.1 hz'.2 2
  dsimp [factorFirst,Explicit.eta]
  linarith [hz'.2]

theorem factor_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (1/6)) : 1≤factor z := by
  have hh := factor_monotone (by norm_num) hz hz.1
  have h0 : factor 0=1 := by simp [factor]
  linarith

theorem factorFirst_upper {z : ℝ} (hz : z∈Icc (0:ℝ) (1/6)) : factorFirst z≤Explicit.eta := by
  have hs := (transport_trig (show z∈Icc 0 frameCap from
    ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)).2.2.1
  dsimp [factorFirst,Explicit.eta]
  linarith [Real.cos_le_one z]

theorem c_derivative (θ : ℝ) : HasDerivAt (Explicit.c .low)
    (-69/20+18*(θ-1/6)) θ := by
  have hx : HasDerivAt (fun x : ℝ => x-Explicit.L) 1 θ := (hasDerivAt_id' θ).sub_const _
  have hh := ((hx.const_mul (69/20:ℝ)).const_sub (10389/10000:ℝ)).fun_add
    ((hx.fun_pow 2).const_mul (9:ℝ))
  exact hh.congr_deriv (by simp only [Explicit.L]; push_cast; ring)

theorem tilted_envelope_antitone :
    AntitoneOn (fun θ => Explicit.c .low θ*factor θ) (Icc (0:ℝ) (1/6)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun θ _ => ((c_derivative θ).mul (factor_derivative θ)).continuousAt.continuousWithinAt)
    (fun θ _ => (c_derivative θ).mul (factor_derivative θ))
  intro θ hθ
  have ht := Ioo_subset_Icc_self hθ
  have hc := Explicit.low_ranges ht
  have hc0 : 0≤Explicit.c .low θ := by linarith [hc.2.2.2.2.1]
  have hcd : -69/20+18*(θ-1/6)≤-(69/20:ℝ) := by linarith [ht.2]
  have h1 := mul_le_mul_of_nonpos_left (factor_lower ht) (by linarith : -69/20+18*(θ-1/6)≤0)
  have h2 := mul_le_mul_of_nonneg_left (factorFirst_upper ht) hc0
  dsimp [Explicit.eta] at h2
  nlinarith [hc.2.2.2.2.2.1]

theorem tilted_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    Explicit.m .low θ z<233/125 := by
  have hc := Explicit.low_ranges hθ
  have hz' : z∈Icc (0:ℝ) (1/6) := ⟨hz.1,hz.2.trans hθ.2⟩
  have hfirst := mul_le_mul_of_nonneg_left (factor_monotone hz' hθ hz.2)
    (show 0≤Explicit.c .low θ by linarith [hc.2.2.2.2.1])
  have hsecond := tilted_envelope_antitone (by norm_num) hθ hθ.1
  have h0 : Explicit.c .low 0*factor 0=18639/10000 := by
    simp only [factor,Explicit.c,Explicit.L,Real.cos_zero,Real.sin_zero]
    norm_num
  change Explicit.m .low θ z≤Explicit.c .low θ*factor θ at hfirst
  simp only at hsecond
  linarith

theorem l_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (10073/10000:ℝ)≤Explicit.l .low θ := by
  have hx : 0≤1/6-θ := by linarith [hθ.2]
  dsimp [Explicit.l,Explicit.L]
  nlinarith [sq_nonneg (θ-1/6)]

theorem pairs {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (i : Fin 3) :
    0<Explicit.p .low θ z i ∧ Explicit.p .low θ z i≤Explicit.q .low θ z i ∧
      Explicit.q .low θ z i≤2*Explicit.p .low θ z i ∧
      Explicit.p .low θ z i≤LowPositive.pMax ∧ Explicit.q .low θ z i≤LowPositive.qMax := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hmax := tilted_upper hθ hz
  have hlm : Explicit.l .low θ≤Explicit.m .low θ z := hr.2.2.2.2.2.2.1.trans hm.1
  have hp := (Source.family_coefficients .low hθ hz).2.2 i
  refine ⟨hp.1,hp.2.1,hp.2.2,?_,?_⟩
  all_goals
    fin_cases i <;>
      simp only [Explicit.p,Explicit.q,Fin.reduceFinMk,Matrix.cons_val,
        min_eq_left hlm,max_eq_right hlm,LowPositive.pMax,LowPositive.qMax] <;>
      linarith [hr.2.1,hr.2.2.2.1]

theorem HB_ratio {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.q .low θ z i≤(3/2)*Explicit.p .low θ z i := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  rcases hi with rfl|rfl
  · simp only [Explicit.p,Explicit.q,Matrix.cons_val_zero]
    linarith [hr.1]
  · simp only [Explicit.p,Explicit.q,Matrix.cons_val,
      min_eq_left hlm,max_eq_right hlm]
    nlinarith [hm.2,hr.2.2.1]

theorem interior_q_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (hint : Explicit.c .low θ≤LowD.sec s)
    (i : Fin 3) : Explicit.q .low θ z i<273/200 := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hc0 : 0<Explicit.c .low θ := by linarith [hr.2.2.2.2.1]
  have hcU : Explicit.c .low θ≤327/250 := hint.trans (NegativeELargeA.secant_range hs).2
  have hfactor := PositiveTD.Explicit.factor_upper z
  have hprod := mul_lt_mul_of_pos_left hfactor hc0
  have hmU : Explicit.m .low θ z<273/200 := by
    change Explicit.m .low θ z<Explicit.c .low θ*(1043/1000) at hprod
    nlinarith
  have hlU : Explicit.l .low θ<273/200 := by
    linarith [hr.2.2.2.2.2.2.1]
  fin_cases i <;> simp only [Explicit.q]
  · norm_num
  · exact hlU
  · exact max_lt hlU hmU

theorem interior_ranges {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 frameCap) (hint : Explicit.c .low θ≤LowD.sec s) :
    Explicit.k .low θ<17/25 ∧ Explicit.l .low θ<283/250 ∧ (27/100:ℝ)<Real.sin s := by
  let u : ℝ := 1/6-θ
  have hu : u∈Icc (0:ℝ) (1/6) :=
    ⟨by dsimp [u]; linarith [hθ.2],by dsimp [u]; linarith [hθ.1]⟩
  have hform : Explicit.c .low θ=10389/10000+(69/20)*u+9*u^2 := by
    dsimp [Explicit.c,Explicit.L,u]
    ring
  have hcU := hint.trans (NegativeELargeA.secant_range hs).2
  have huU : u<67/1000 := by
    by_contra hh
    have hlow : 67/1000≤u := le_of_not_gt hh
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤67/1000) hlow 2
    nlinarith
  have hu2 : u^2≤(67/1000)*u := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr huU.le)]
  have hk : Explicit.k .low θ=6708/10000-(3/20)*u+4*u^2 := by
    dsimp [Explicit.k,Explicit.L,u]
    ring
  have hl : Explicit.l .low θ=10073/10000+(17/10)*u+(11/5)*u^2 := by
    dsimp [Explicit.l,Explicit.L,u]
    ring
  have hcos := NegativeESecant.cos_pos hs
  have hprod := (le_div_iff₀ hcos).1 hint
  have hcl := (Explicit.low_ranges hθ).2.2.2.2.1
  have hcosU : (10389/10000)*Real.cos s≤1 := by
    have hh := mul_le_mul_of_nonneg_right hcl hcos.le
    linarith
  have hcos2 := pow_le_pow_left₀ (show 0≤(10389/10000:ℝ)*Real.cos s by positivity) hcosU 2
  have hsin := (transport_trig hs).2.2.1
  refine ⟨by nlinarith,by nlinarith,?_⟩
  by_contra hh
  have hsU : Real.sin s≤27/100 := le_of_not_gt hh
  have hs2 := pow_le_pow_left₀ hsin hsU 2
  nlinarith [Real.sin_sq_add_cos_sq s]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowRanges
