module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3SameBlock
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowSecants

/-!
# Complete low-total concentration when the negative mass is larger

Uncompiled Section 4.1. The original secant is bounded before the D
positive cost is compared with an ordinary positive allocation. The
negative B block is dominated by H on the whole angular interval.
Concavity transfers the proved H secant to the shifted interval with
both original masses retained. All pure, same-block and separated
alternatives, including the distinguished D block, then have one lower
bound V_H(theta-s).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope

lemma short_secant {s : ℝ} (hs : s∈Icc (0:ℝ) (1/6)) :
    Explicit.sec s≤(203/200:ℝ) := by
  have hsf : s∈Icc 0 frameCap :=
    ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hc := NegativeESecant.cos_pos hsf
  have hl := cos_lower_two hs.1
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  change 1/Real.cos s≤(203/200:ℝ)
  apply (div_le_iff₀ hc).2
  norm_num at hs2
  nlinarith

lemma secant_le_c {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) :
    Explicit.sec s≤Explicit.c .low θ z := by
  have hsec := short_secant (show s∈Icc (0:ℝ) (1/6) from ⟨hs.1,hs.2.trans hθ.2⟩)
  have hm := (Explicit.low_bounds hθ).2.1
  have hc := (Explicit.low_c hθ hz).1
  linarith

lemma gamma_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) :
    Explicit.gamma .low θ z s≤(13/20:ℝ) := by
  have hc := (Explicit.low_c hθ hz).2
  rw [Explicit.gamma,max_eq_right (secant_le_c hθ hz hs)]
  dsimp [SecantD.slope]
  linarith

lemma positive_lower {θ z s t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    -(13/20)*t≤Blocks.positive .low θ z s t i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right (gamma_upper hθ hz hs) ht.1
    linarith
  · obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := by fin_cases i <;> simp_all
    subst i
    rw [Blocks.positive_ordinary]
    have hh := PositivePure.ordinary_lower .low hθ ht j
    nlinarith only [hh,ht.1]

lemma H_upper {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤(1101/1000)*t := by
  have hk := (PositiveBT3.Analytic.low_ranges hθ).1
  have hh := PositiveTD.V_first_coefficient (by norm_num : (0:ℝ)<1)
    (by linarith [hk.1]) hk.2 (by norm_num [PositiveBT3.K]) ht
  exact hh.trans (PositiveBT3.vstar_linear_upper ht)

lemma H_le_B {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤V R 1 (Explicit.m .low θ) t := by
  have hm := (Explicit.low_bounds hθ).2
  have hb := V_chord_lower (p:=(1:ℝ)) (q:=Explicit.m .low θ)
    (by norm_num) (by linarith [hm.1]) (by linarith [hm.2]) ht
  have hh := H_upper hθ ht
  nlinarith only [hb,hh,ht.1]

lemma negative_comparison {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    V R (Explicit.k .low θ) 1 t≤Blocks.negative .low θ t i := by
  have hm : 1≤Explicit.m .low θ := by linarith [(Explicit.low_bounds hθ).2.1]
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · simpa only [Blocks.negative,Blocks.p,Blocks.q,Explicit.l,
      Matrix.cons_val_succ,Matrix.cons_val_zero,min_eq_left hm,max_eq_right hm]
      using H_le_B hθ ht
  · exact le_rfl

/-- A concave V has no smaller increment when both endpoints shift left. -/
lemma negative_shift {p q θ s : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ) :
    V R p q frameCap-V R p q θ≤V R p q (frameCap-s)-V R p q (θ-s) := by
  have hq := hp.trans_le hpq
  have hd (u : ℝ) (hu : u∈Icc 0 θ) :
      HasDerivAt (fun u => V R p q (frameCap-u)-V R p q (θ-u))
        (Vd R p q (θ-u)-Vd R p q (frameCap-u)) u := by
    have hleft := (V_hasDerivAt hp hq
      (show frameCap-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2,hθ.2],by linarith [hu.1]⟩)).comp u
          ((hasDerivAt_id u).const_sub frameCap)
    have hright := (V_hasDerivAt hp hq
      (show θ-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2],by linarith [hu.1,hθ.2]⟩)).comp u
          ((hasDerivAt_id u).const_sub θ)
    convert hleft.sub hright using 1 <;> ring
  have hm : MonotoneOn (fun u => V R p q (frameCap-u)-V R p q (θ-u))
      (Icc 0 θ) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => hd u (Ioo_subset_Icc_self hu))
    intro u hu
    have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp
      (show θ-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2],by linarith [hu.1,hθ.2]⟩)
      (show frameCap-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2,hθ.2],by linarith [hu.1]⟩)
      (by linarith [hθ.2] : θ-u≤frameCap-u)
    exact sub_nonneg.mpr hh
  simpa only [sub_zero] using hm ⟨le_rfl,hθ.1⟩ hs hs.1

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤
      Blocks.positive .low θ z s (frameCap-θ) i+
        Blocks.negative .low θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .low hθ
  have hp := Explicit.family_pairs .low hθ 0
  have hP : frameCap-θ∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ht.2],by linarith [hs.1]⟩
  have hu := positive_lower hθ hz hs hP i
  have hv := negative_comparison hθ hN j
  have hshift := negative_shift hp.1 hp.2.1 hp.2.2 ht hs
  have hsec := PositiveBT3.LowSecants.H_secant hθ
  change V R (Explicit.k .low θ) 1 θ+(3/4)*(frameCap-θ)<
    V R (Explicit.k .low θ) 1 frameCap at hsec
  linarith [hP.1]

lemma pure_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤Blocks.pure .low θ z s i j := by
  have ht := Explicit.frame_domain .low hθ
  have hh := negative_comparison hθ
    (show θ-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1,ht.2]⟩) j
  simpa only [Blocks.pure,ChargedHybridConcentration.pure,if_pos hs.2,Blocks.negative] using hh

lemma saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤Blocks.saturated .low θ z s i j := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .low θ z s 3 3=
          Blocks.block .low θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,if_pos rfl,Blocks.block]
      rw [he,Blocks.block_D]
      exact separated_lower hθ hz hs 3 3
    · obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i := by fin_cases i <;> simp_all
      subst i
      exact (pure_lower hθ hs r.castSucc r.castSucc).trans
        (SameBlock.ordinary_saturated_lower .low hθ hsf r)
  · simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,
      if_neg hij,Blocks.positive,Blocks.negative] using separated_lower hθ hz hs i j

/-- The full original four-block allocation, not merely an endpoint sample. -/
theorem sum_to_H {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    V R (Explicit.k .low θ) 1 (θ-s)≤∑i,Blocks.block .low θ z s (P i) (N i) i := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .low P N hθ hsf hP hN hPb hNb hbalance
  exact (le_min (pure_lower hθ hs i j) (saturated_lower hθ hz hs i j)).trans hij

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowNegative
