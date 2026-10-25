module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarLowSplit
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Blocks
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2OrdinarySlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHPositiveD
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHSameBlock
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Far-low signed-mass comparisons on the complete original intervals

Uncompiled far-low companion. The only new scalar reference is the
left endpoint .45 of the full remaining-negative interval [.45,.6].
The negative derivative decreases, so that reference controls the entire
interval for both original H and G coefficients. Positive mass retains
its .005 EH charge. The original B negative mass is dominated by H.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSlopes
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open NegativeAPositiveTD.PositiveSlope Arithmetic SecondWord.ReferenceTrig

theorem pair_data {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤Blocks.p .far .low θ z i ∧
    Blocks.p .far .low θ z i≤Blocks.q .far .low θ z i ∧
    Blocks.q .far .low θ z i≤(5/3)*Blocks.p .far .low θ z i :=
  Blocks.far_pair .low hθ hz i

theorem ordinary_q_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 3) : Explicit.q .far .low θ z i≤111/100 := by
  have hr := Explicit.far_low_ranges hθ
  have hm := Explicit.far_low_tilted hθ hz
  fin_cases i
  · show (1:ℝ)≤111/100
    norm_num
  · show Explicit.l .far .low θ≤111/100
    linarith [hr.2.1.2]
  · show max (Explicit.l .far .low θ) (Explicit.m .far .low θ z)≤111/100
    exact max_le (by linarith [hr.2.1.2]) hm.2.1

theorem q_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) : Blocks.q .far .low θ z i≤111/100 := by
  have hh := ordinary_q_upper hθ hz (Blocks.ordinaryIndex i)
  fin_cases i <;> exact hh

theorem positive_lower {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    -(12199/20000)*t≤Blocks.positive .far .low θ z t i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost+Explicit.errorCharge .far≤(12199/20000:ℝ) by
        dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
        linarith [diagonal_bounds.2]) ht.1
    linarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (show 0<Blocks.p .far .low θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .low θ z i≤2*Blocks.p .far .low θ z i by linarith [hp.1,hp.2.2]) ht
    have hq := mul_le_mul_of_nonneg_right (q_upper hθ hz i) ht.1
    simp only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,if_neg hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    nlinarith

theorem U_larger_comparison {p q Q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hqQ : q≤Q) (ht : t∈Icc 0 frameCap) : U R p Q t≤U R p q t := by
  have hQ := hq.trans_le hqQ
  have hd {x : ℝ} (hx : x∈Icc 0 frameCap) :=
    (U_hasDerivAt hp hq hx).sub (U_hasDerivAt hp hQ hx)
  have hm : MonotoneOn (fun x => U R p q x-U R p Q x) (Icc 0 frameCap) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (hd hx).continuousAt.continuousWithinAt)
      (fun x hx => hd (Ioo_subset_Icc_self hx))
      (fun x hx => sub_nonneg.mpr
        (NegativeDEPositiveTD.LowPositive.larger_comparison hp hq hqQ (Ioo_subset_Icc_self hx)))
  have hh := hm (by norm_num [frameCap]) ht ht.1
  simp only [U_zero,sub_self] at hh
  linarith

theorem H_le_G {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Explicit.U .far .low θ z 0 t≤Explicit.U .far .low θ z 1 t := by
  have hl := (Explicit.far_low_ranges hθ).2.1
  show U R (121/200) 1 t≤U R (121/200) (Explicit.l .far .low θ) t
  exact U_larger_comparison (by norm_num) (by linarith [hl.1]) hl.2 ht

theorem slope_formula (p q t : ℝ) :
    Vd R p q t= -q*Real.sin t+R*p*q*Real.cos t/pairNorm p q (-t) := by
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  rw [zero_sub,Real.cos_neg]
  ring

theorem H_initial_slope : Vd R (121/200) 1 0<(41/40:ℝ) := by
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<121/200)
    (by norm_num : (0:ℝ)<1) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<121/200)
    (by norm_num : (0:ℝ)<1) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at hn2
  simp only [pairEnergy] at hn2
  have hN : (11687/10000:ℝ)<pairNorm (121/200) 1 0 := by nlinarith
  rw [slope_formula]
  norm_num only [Real.sin_zero,Real.cos_zero,neg_zero,mul_zero,zero_add,mul_one]
  apply (div_lt_iff₀ hn).2
  nlinarith [radius_bounds.2]

theorem H_upper {θ z t : ℝ} (ht : t∈Icc 0 frameCap) :
    Explicit.V .far .low θ z 0 t≤(41/40)*t := by
  have hh := V_tangent_zero (p:=(121/200:ℝ)) (q:=1)
    (by norm_num) (by norm_num) (by norm_num) ht
  have hp := mul_le_mul_of_nonneg_right H_initial_slope.le ht.1
  exact hh.trans hp

theorem H_le_B {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Explicit.V .far .low θ z 0 t≤Explicit.V .far .low θ z 2 t := by
  have hr := Explicit.far_low_ranges hθ
  have hm := Explicit.far_low_tilted hθ hz
  have hp := Explicit.family_pairs .far .low hθ hz 2
  have hh := V_chord_lower hp.1 hp.2.1 hp.2.2 ht
  have hlo : (91/100:ℝ)≤Explicit.p .far .low θ z 2 := by
    simpa [Explicit.p,min_eq_left hm.2.2.1.le] using hr.2.1.1
  have hpaid := mul_le_mul_of_nonneg_right hlo ht.1
  have hH := H_upper (θ:=θ) (z:=z) ht
  change (87/70)*Explicit.p .far .low θ z 2*t≤Explicit.V .far .low θ z 2 t at hh
  linarith [ht.1]

theorem left_trig :
    (4349/10000:ℝ)<Real.sin (9/20) ∧ Real.sin (9/20)<87/200 ∧
      Real.cos (9/20)<18009/20000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤9/20 by norm_num)
  have hu := sin_le_sin9 (show (0:ℝ)≤9/20 by norm_num)
  have hc := cos_le_cos12 (show (0:ℝ)≤9/20 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hu hc
  exact ⟨by linarith,by linarith,by linarith⟩

theorem left_negative_slope {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    Vd R (121/200) q (9/20)<(881/1000:ℝ) := by
  have hq0 : 0<q := by linarith [hq.1]
  have ht : (9/20:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have htr := transport_trig ht
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<121/200) hq0
    (show |-(9/20:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<121/200) hq0
    (show |-(9/20:ℝ)|≤frameCap by norm_num [frameCap])
  norm_num only [pairEnergy,pairProduct,Real.sin_neg] at hn2
  have hsprod := mul_le_mul_of_nonneg_left left_trig.2.1.le hq0.le
  have hquad := mul_nonneg (sub_nonneg.mpr hq.1)
    (show 0≤q+91/100-2*(121/200)*(87/200) by linarith [hq.1])
  have hN : (169/200:ℝ)<pairNorm (121/200) q (-(9/20)) := by nlinarith
  have hR : R<(1979/1000:ℝ) := by linarith [radius_bounds.2]
  have hc0 : 0<Real.cos (9/20) := by linarith [htr.1]
  have hRc := mul_lt_mul hR left_trig.2.2.le hc0 (by norm_num : (0:ℝ)≤1979/1000)
  have hnum := mul_lt_mul_of_pos_right hRc (by norm_num : (0:ℝ)<121/200)
  have hqnum := mul_le_mul_of_nonneg_right hq.2
    (show 0≤R*(121/200)*Real.cos (9/20) by positivity)
  have hquot : R*(121/200)*q*Real.cos (9/20)/pairNorm (121/200) q (-(9/20))<
      ((1979/1000)*(121/200)*(18009/20000))/(169/200) := by
    apply (div_lt_iff₀ hn).2
    have hden := mul_lt_mul_of_pos_left hN
      (by norm_num : (0:ℝ)<((1979/1000)*(121/200)*(18009/20000))/(169/200))
    nlinarith
  have hsin := mul_le_mul hq.1 left_trig.1.le
    (by norm_num : (0:ℝ)≤4349/10000) hq0.le
  rw [slope_formula]
  linarith

theorem negative_slope {q t : ℝ} (hq : q∈Icc (91/100:ℝ) 1)
    (ht : t∈Icc (9/20:ℝ) (3/5)) : Vd R (121/200) q t<(881/1000:ℝ) := by
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (by norm_num : (0:ℝ)<121/200)
    (by linarith [hq.1] : (121/200:ℝ)≤q)
    (by linarith [hq.2] : q≤2*(121/200))
    (show (9/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show t∈Icc 0 frameCap from ⟨by linarith [ht.1],by norm_num [frameCap]; linarith [ht.2]⟩) ht.1
  exact hm.trans_lt (left_negative_slope hq)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSlopes
