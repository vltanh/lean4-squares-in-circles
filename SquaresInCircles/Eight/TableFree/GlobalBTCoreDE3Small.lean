module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Polynomial

/-!
# Both core-E tails for the complete small-DE interval

The variable prefix is bounded by its explicit two-norm polynomial.
The small DE dependence is concave with its smaller endpoint at zero.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem prefix_strict {p : ℝ} (hp : p∈Icc 0 frameCap) : pathThreshold<«prefix» p := by
  have hk : 0<kappa := by norm_num [kappa]
  have hc := weight_pos hp
  have hnorm1 := tailNorm_sq hk hc hp
  have hnorm2 := tailNorm_sq hk hc (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hp.1)
    (show 0≤2*kappa*weight p by positivity)
  have hX1 : (tailNorm kappa (weight p) p)^2≤aeval p PrefixPolynomial.X1 := by
    rw [hnorm1]
    simp only [PrefixPolynomial.X1,map_sub,map_add,map_mul,map_pow,aeval_C,
      PrefixPolynomial.c_eval,TailPolynomial.S7_eval]
    norm_num [kappa] at hs ⊢
    linarith
  have hX2 : (tailNorm kappa (weight p) 0)^2≤aeval p PrefixPolynomial.X2 := by
    rw [hnorm2]
    simp [PrefixPolynomial.X2,kappa]
  have hP := PrefixPolynomial.envelopes_positive hp
  have hpoly : 0<2*aeval p PrefixPolynomial.P1*aeval p PrefixPolynomial.P2*
      aeval p PrefixPolynomial.L-(1979/1000)*
        (aeval p PrefixPolynomial.P2*(aeval p PrefixPolynomial.X1+(aeval p PrefixPolynomial.P1)^2)+
          aeval p PrefixPolynomial.P1*(aeval p PrefixPolynomial.X2+(aeval p PrefixPolynomial.P2)^2)) := by
    simpa [PrefixPolynomial.H] using PrefixPolynomial.positive hp
  have hn := two_norm_envelope (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (show 0<aeval p PrefixPolynomial.P1 by linarith [hP.1])
    (show 0<aeval p PrefixPolynomial.P2 by linarith [hP.2]) hX1 hX2 hpoly
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hp.1) hk.le
  have hL : aeval p PrefixPolynomial.L≤
      Real.pi-p+3*kappa+2*weight p+kappa*Real.cos p-pathThreshold := by
    simp only [PrefixPolynomial.L,map_add,map_sub,map_mul,aeval_C,aeval_X,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval]
    norm_num [kappa,pathThreshold] at hcos ⊢
    linarith [Arithmetic.pi_hand_enclosure.1]
  have hn' : R*(tailNorm kappa (weight p) p+tailNorm kappa (weight p) 0)<
      aeval p PrefixPolynomial.L := hn
  dsimp only [«prefix»]
  linarith

def smallDE (t : ℝ) : ℝ := -t+(kappa/2)*Real.cos t+kappa*(13/12)*Real.sin t
def smallDED (t : ℝ) : ℝ := -1-(kappa/2)*Real.sin t+kappa*(13/12)*Real.cos t
def smallDEDD (t : ℝ) : ℝ := -(kappa/2)*Real.cos t-kappa*(13/12)*Real.sin t

theorem smallDE_deriv (t : ℝ) : HasDerivAt smallDE (smallDED t) t := by
  have h := (((hasDerivAt_id t).neg).add ((Real.hasDerivAt_cos t).const_mul (kappa/2))).add
    ((Real.hasDerivAt_sin t).const_mul (kappa*(13/12)))
  exact h.congr_deriv (by simp only [smallDED]; ring)

theorem smallDED_deriv (t : ℝ) : HasDerivAt smallDED (smallDEDD t) t := by
  have h := (((Real.hasDerivAt_sin t).const_mul (-(kappa/2))).const_add (-1)).add
    ((Real.hasDerivAt_cos t).const_mul (kappa*(13/12)))
  convert h using 1
  · funext x; simp only [smallDED,Pi.add_apply]; ring
  · simp only [smallDEDD]; ring

theorem smallDE_concave : ConcaveOn ℝ (Icc 0 (1/5:ℝ)) smallDE := by
  apply concave_of_deriv2 (fun t _ => smallDE_deriv t) (fun t _ => smallDED_deriv t)
  intro t ht
  have hd : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have tr := transport_trig hd
  dsimp [smallDEDD,kappa]
  linarith [tr.1,tr.2.2.1]

theorem smallDE_endpoint : smallDE 0<smallDE (1/5) := by
  have hs := sin_lower_seven (by norm_num : (0:ℝ)≤1/5)
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤1/5)
  norm_num at hs hc
  norm_num [smallDE,kappa]
  linarith

theorem smallDE_lower {t : ℝ} (ht : t∈Icc 0 (1/5:ℝ)) : smallDE 0≤ smallDE t := by
  have hh := smallDE_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (1/5:ℝ) by norm_num)
    (show (1/5:ℝ)∈Icc 0 (1/5:ℝ) by norm_num) ht
  rw [min_eq_left smallDE_endpoint.le] at hh
  exact hh

theorem last_first_difference (p t : ℝ) :
    last p t kappa-first p t kappa=(kappa-weight p)*(1-Real.cos p) := by
  dsimp [last,first]
  ring

theorem small_endpoints {p t : ℝ} (hp : p∈Icc 0 frameCap)
    (ht : t∈Icc 0 (1/5:ℝ)) :
    pathThreshold<first p t kappa ∧ pathThreshold<last p t kappa := by
  have hg := smallDE_lower ht
  have hfirst : «prefix» p≤first p t kappa := by
    simp only [smallDE,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,neg_zero,add_zero] at hg
    dsimp [«prefix»,first]
    linarith only [hg]
  have hlast : first p t kappa≤last p t kappa := by
    have hm := mul_nonneg (sub_nonneg.mpr (weight_bounds hp).2.2)
      (sub_nonneg.mpr (Real.cos_le_one p))
    rw [← last_first_difference p t] at hm
    linarith
  have hstrict := (prefix_strict hp).trans_le hfirst
  exact ⟨hstrict,hstrict.trans_le hlast⟩

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
