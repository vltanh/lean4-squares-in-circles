module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Polynomial

/-!
# The saturated aligned-prefix scalar for core E

Multiplication by the positive original cosine removes the secant
from the only variable radical.  Its envelope is a fixed positive
quartic and its certificate covers the complete saturated interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem saturated_weight_bounds {t : ℝ} (ht : t∈Icc 0 frameCap) :
    m≤m/Real.cos t ∧ m/Real.cos t<141/100 := by
  have tr := transport_trig ht
  have hc : 0<Real.cos t := by linarith [tr.1]
  constructor
  · apply (le_div_iff₀ hc).2
    dsimp [m]
    linarith [tr.2.1]
  · apply (div_lt_iff₀ hc).2
    dsimp [m]
    linarith [tr.1]

theorem endpointWeight_bounds {t : ℝ} (ht : t∈Icc 0 frameCap) :
    kappa≤endpointWeight t ∧ endpointWeight t<141/100 ∧
      endpointWeight t*Real.cos t≤m ∧ endpointWeight t*Real.sin t≤7506931/1000000 := by
  have tr := transport_trig ht
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [tr.1])
  by_cases hsmall : t≤1/5
  · rw [endpointWeight,if_pos hsmall]
    refine ⟨le_rfl,by norm_num [kappa],?_,?_⟩
    · dsimp [kappa,m]
      linarith [tr.2.1]
    · dsimp [kappa]
      linarith [Real.sin_le_one t]
  · rw [endpointWeight,if_neg hsmall]
    have hb := saturated_weight_bounds ht
    have hpos : 0≤m/Real.cos t := le_trans (by norm_num [m]) hb.1
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hpos
    refine ⟨by dsimp [m,kappa] at hb ⊢; linarith [hb.1],hb.2,?_,?_⟩
    · rw [div_mul_cancel₀ m hc]
    · linarith [hb.2]

theorem fixed_first_norm : R*tailNorm kappa (3/5) 0<11369/5000 := by
  have hn := tailNorm_sq (by norm_num [kappa] : 0<kappa)
    (by norm_num : (0:ℝ)<3/5) (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have hs : (R*tailNorm kappa (3/5) 0)^2=Q0*(kappa^2+(3/5)^2) := by
    rw [mul_pow,R_sq,hn]
    simp
  norm_num [Q0,kappa] at hs
  nlinarith

theorem one_norm_envelope {N X P L : ℝ} (hN : 0≤N) (hP : 0<P)
    (hX : N^2≤X) (hpoly : 0<2*P*L-(1979/1000)*(X+P^2)) : R*N<L := by
  have hh : 2*P*N≤X+P^2 := by nlinarith [sq_nonneg (N-P)]
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1979/1000)
  have hmain : (1979/1000)*N<L := by
    apply (mul_lt_mul_iff_left₀ (show 0<2*P by positivity)).1
    nlinarith only [hpoly,hm]
  exact (mul_le_mul_of_nonneg_right radius_upper.le hN).trans_lt hmain

theorem scaled_norm_square {t : ℝ} (ht : t∈Icc 0 frameCap) :
    (Real.cos t*tailNorm (m/Real.cos t) (3/5) 0)^2=m^2+(9/25)*(Real.cos t)^2 := by
  have hc : 0<Real.cos t := by linarith [(transport_trig ht).1]
  have hn := tailNorm_sq (div_pos (by norm_num [m]) hc)
    (by norm_num : (0:ℝ)<3/5) (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  rw [mul_pow,hn]
  simp only [Real.sin_zero,mul_zero,sub_zero]
  field_simp [hc.ne']
  ring

theorem base_scaled_identity {t : ℝ} (ht : t∈Icc 0 frameCap) :
    Real.cos t*(base t (m/Real.cos t)-pathThreshold)=
      (Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2)*Real.cos t+
        m*(1+(13/12)*Real.sin t)-R*(Real.cos t*tailNorm (m/Real.cos t) (3/5) 0) := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(transport_trig ht).1])
  dsimp [base]
  field_simp [hc]
  ring

/-- The concrete saturated base, including its lower endpoint. -/
theorem saturated_base {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) :
    pathThreshold<base t (m/Real.cos t) := by
  have hdom : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  have hc : 0<Real.cos t := by linarith [(transport_trig hdom).1]
  let N := Real.cos t*tailNorm (m/Real.cos t) (3/5) 0
  let P : ℝ := aeval t BasePolynomial.P
  let X : ℝ := aeval t BasePolynomial.energy
  let L : ℝ := aeval t BasePolynomial.L
  have hN : 0≤N := mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hP : 0<P := by dsimp [P]; linarith [BasePolynomial.envelope_positive hdom]
  have hU : Real.cos t≤aeval t BasePolynomial.U := by
    simpa [BasePolynomial.U] using cos_upper_four hdom.1
  have hUpos : 0≤aeval t BasePolynomial.U := hc.le.trans hU
  have hsq := pow_le_pow_left₀ hc.le hU 2
  have hX : N^2≤X := by
    dsimp [N,X]
    rw [scaled_norm_square hdom]
    simp only [BasePolynomial.energy,map_add,map_mul,map_pow,aeval_C]
    norm_num [m]
    nlinarith only [hsq]
  have hpoly : 0<2*P*L-(1979/1000)*(X+P^2) := by
    simpa [BasePolynomial.H,P,L,X] using BasePolynomial.positive ht
  have hnorm := one_norm_envelope hN hP hX hpoly
  have hcoef := BasePolynomial.coefficient_positive hdom
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hdom.1) hcoef.le
  have hpi : aeval t BasePolynomial.coefficient≤
      Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2 := by
    norm_num [BasePolynomial.coefficient,kappa,pathThreshold,m]
    linarith [Arithmetic.pi_hand_enclosure.1,fixed_first_norm]
  have hactual := mul_le_mul_of_nonneg_right hpi hc.le
  have hsin := mul_le_mul_of_nonneg_left (sin7_lower hdom.1)
    (show 0≤m*(13/12) by norm_num [m])
  have hL : L≤
      (Real.pi-t+(5/2)*kappa+6/5-R*tailNorm kappa (3/5) 0-pathThreshold+m/2)*Real.cos t+
        m*(1+(13/12)*Real.sin t) := by
    dsimp [L]
    simp only [BasePolynomial.L,map_add,map_mul,aeval_C,map_one,
      TailPolynomial.C6_eval,TailPolynomial.S7_eval]
    norm_num [m] at hsin ⊢
    nlinarith only [hcos,hactual,hsin]
  have hpos : 0<Real.cos t*(base t (m/Real.cos t)-pathThreshold) := by
    rw [base_scaled_identity hdom]
    dsimp [N,L] at hnorm
    dsimp [L] at hL
    linarith only [hnorm,hL]
  have hh := (mul_pos_iff_of_pos_left hc).1 hpos
  linarith

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
