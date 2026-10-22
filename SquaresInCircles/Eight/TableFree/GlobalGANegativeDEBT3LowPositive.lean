module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowRectangle

/-!
# Complete low-total concentration when the positive mass is larger

Uncompiled Section 4.2. H/G positive allocations use the whole-angle
slope reserve. The original D singleton uses its secant-dependent cost,
not an ordinary substitute. The only remaining B/H allocation is the
proved whole rectangle. Negative B and D are compared with H at their
actual angle, and all weak zero-mass and same-block ties are included.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open NegativeAPositiveTD.PositiveSlope

lemma H_linear_lower {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) : (77/100)*t≤V R (Explicit.k .low θ) 1 t := by
  have hr := Explicit.low_bounds hθ
  have hp := Explicit.family_pairs .low hθ 0
  have hcap := PositiveBT3.LowSecants.J_linear_lower
    (show Explicit.k .low θ∈Icc PositiveBT3.LowSecants.k0 PositiveBT3.K by
      simpa [PositiveBT3.LowSecants.k0,PositiveBT3.K] using hr.1)
  have hc := V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2
  have hlinear : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => V R (Explicit.k .low θ) 1 t-(77/100)*t) := by
    refine ⟨hc.1,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    nlinarith only [hh]
  have he : 0≤V R (Explicit.k .low θ) 1 frameCap-(77/100)*frameCap := by
    dsimp [PositiveBT3.LowSecants.J,PositiveBT3.LowSecants.k0,frameCap] at hcap ⊢
    linarith [hr.1.1]
  have hh := hlinear.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  simp only [V_zero,mul_zero,sub_zero,min_eq_left he] at hh
  linarith

lemma H_positive_increment {θ P N : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    -(18/25)*N≤U R (Explicit.k .low θ) 1 P-U R (Explicit.k .low θ) 1 (P-N) := by
  have hp := Explicit.family_pairs .low hθ 0
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :=
    U_hasDerivAt hp.1 (by norm_num : (0:ℝ)<1) ht
  have hh := derivative_reserve
    (f:=U R (Explicit.k .low θ) 1) (df:=Ud (Explicit.k .low θ) 1) (k:=-(18/25:ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have h := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole
        hp.1 hp.2.1 hp.2.2 (Ioo_subset_Icc_self ht)
      simpa only [mul_one] using h.le)
    (show P-N∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show P∈Icc 0 frameCap from ⟨hN.trans hNP,hP⟩) (by linarith)
  simpa only [show P-(P-N)=N by ring] using hh

lemma gamma_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) :
    Explicit.gamma .low θ z s≤77/100 := by
  have hsec := (NegativeELargeA.secant_range hs).2
  have hc := (Explicit.low_c hθ hz).2
  have hmax : max (Explicit.sec s) (Explicit.c .low θ z)≤(327/250:ℝ) :=
    max_le (by simpa [SecantD.qUpper] using hsec) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hmax (by norm_num [SecantD.slope] : 0≤SecantD.slope)
  dsimp [Explicit.gamma,SecantD.slope] at hh ⊢
  linarith

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i j : Fin 4) :
    Blocks.positive .low θ z s (s-θ) i≤
      Blocks.positive .low θ z s (frameCap-θ) i+
        Blocks.negative .low θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .low hθ
  have hsf : s∈Icc 0 frameCap := ⟨ht.1.trans hs.1,hs.2⟩
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hNP : frameCap-s≤frameCap-θ := by linarith [hs.1]
  have hPcap : frameCap-θ≤frameCap := by linarith [ht.1]
  have hn : frameCap-s∈Icc 0 frameCap := ⟨hN,by linarith [hsf.1]⟩
  have hH := LowNegative.negative_comparison hθ hn j
  have hlinear := H_linear_lower hθ hn
  have hr := Explicit.low_bounds hθ
  have hm : 1≤Explicit.m .low θ := by linarith [hr.2.1]
  have hdiff : frameCap-θ-(frameCap-s)=s-θ := by ring
  fin_cases i
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    linarith
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    linarith
  · have hh := LowRectangle.original_rectangle
      (k:=Explicit.k .low θ) (m:=Explicit.m .low θ)
      (show Explicit.k .low θ∈Icc LowRectangle.k0 1 from
        ⟨hr.1.1,by linarith [hr.1.2]⟩)
      (show Explicit.m .low θ∈Icc (1:ℝ) LowRectangle.M from ⟨hm,hr.2.2⟩)
      hN hNP hPcap
    rw [hdiff] at hh
    simp only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      Fin.reduceFinMk,reduceCtorEq,if_false,zero_mul,sub_zero,Blocks.p,Blocks.q,
      Matrix.cons_val_succ,Matrix.cons_val_zero,Explicit.l,min_eq_left hm,max_eq_right hm]
    linarith
  · rw [Blocks.positive_D,Blocks.positive_D]
    have hgamma := mul_le_mul_of_nonneg_right (gamma_upper hθ hz hsf) hN
    nlinarith only [hH,hlinear,hgamma]

theorem saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i j : Fin 4) :
    Blocks.pure .low θ z s i j≤Blocks.saturated .low θ z s i j := by
  have hsf : s∈Icc 0 frameCap := ⟨(Explicit.frame_domain .low hθ).1.trans hs.1,hs.2⟩
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .low θ z s 3 3=
          Blocks.block .low θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,if_pos rfl,Blocks.block]
      rw [he,Blocks.block_D]
      by_cases hst : s≤θ
      · have hsEq : s=θ := le_antisymm hst hs.1
        subst s
        have hh := separated_lower hθ hz ⟨le_rfl,hs.2⟩ 3 3
        simpa [Blocks.pure,ChargedHybridConcentration.pure,Blocks.positive_D,sub_self,V_zero] using hh
      · have hh := separated_lower hθ hz hs 3 3
        simpa only [Blocks.pure,ChargedHybridConcentration.pure,if_neg hst,Blocks.positive] using hh
    · obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i := by fin_cases i <;> simp_all
      subst i
      exact SameBlock.ordinary_saturated_lower .low hθ hsf r
  · have hh := separated_lower hθ hz hs i j
    by_cases hst : s≤θ
    · have hsEq : s=θ := le_antisymm hst hs.1
      subst s
      simpa [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
        ChargedHybridConcentration.saturated,hij,Blocks.positive,Blocks.negative,
        ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,U_zero,V_zero] using hh
    · simpa only [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
        ChargedHybridConcentration.saturated,if_neg hst,if_neg hij,Blocks.positive,Blocks.negative] using hh

theorem sum_to_pure {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,Blocks.pure .low θ z s i j≤∑k,Blocks.block .low θ z s (P k) (N k) k := by
  have hsf : s∈Icc 0 frameCap := ⟨(Explicit.frame_domain .low hθ).1.trans hs.1,hs.2⟩
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .low P N hθ hsf hP hN hPb hNb hbalance
  rw [min_eq_left (saturated_lower hθ hz hs i j)] at hij
  exact ⟨i,j,hij⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowPositive
