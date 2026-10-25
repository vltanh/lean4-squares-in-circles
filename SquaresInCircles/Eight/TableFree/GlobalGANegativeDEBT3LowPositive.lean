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
  have hk0 : 0<Explicit.k .low θ := by linarith [hr.1.1]
  have hk1 : Explicit.k .low θ≤1 := by linarith [hr.1.2]
  have h1k : (1:ℝ)≤2*Explicit.k .low θ := by linarith [hr.1.1]
  have hcap := PositiveBT3.LowSecants.J_linear_lower (k:=Explicit.k .low θ) hr.1
  simp only [PositiveBT3.LowSecants.J] at hcap
  have hc := V_concave (R:=R) (p:=Explicit.k .low θ) (q:=1) (Real.sqrt_nonneg qCap)
    radius_sq.le hk0 hk1 h1k
  have hlinear : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => V R (Explicit.k .low θ) 1 t-(77/100)*t) := by
    refine ⟨hc.1,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    linarith
  have he : 0≤V R (Explicit.k .low θ) 1 frameCap-(77/100)*frameCap := by
    rw [show (77/100:ℝ)*frameCap=539/1000 by norm_num [frameCap]]
    simp only [PositiveBT3.LowSecants.k0] at hcap
    linarith [hr.1.1]
  have hh := hlinear.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  simp only [V_zero,mul_zero,sub_zero,min_eq_left he] at hh
  linarith

lemma H_positive_increment {θ P N : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    -(18/25)*N≤U R (Explicit.k .low θ) 1 P-U R (Explicit.k .low θ) 1 (P-N) := by
  have hr := Explicit.low_bounds hθ
  have hk0 : 0<Explicit.k .low θ := by linarith [hr.1.1]
  have hk1 : Explicit.k .low θ≤1 := by linarith [hr.1.2]
  have h1k : (1:ℝ)≤2*Explicit.k .low θ := by linarith [hr.1.1]
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (U R (Explicit.k .low θ) 1) (Ud (Explicit.k .low θ) 1 t) t :=
    U_hasDerivAt hk0 (by norm_num : (0:ℝ)<1) ht
  have hh := derivative_reserve
    (f:=U R (Explicit.k .low θ) 1) (df:=Ud (Explicit.k .low θ) 1) (k:=-(18/25:ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have h := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole
        (p:=Explicit.k .low θ) (q:=1) hk0 hk1 h1k (Ioo_subset_Icc_self ht)
      linarith)
    (show P-N∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show P∈Icc 0 frameCap from ⟨hN.trans hNP,hP⟩) (by linarith)
  rw [show P-(P-N)=N by ring] at hh
  exact hh

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
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    rw [show (0:Fin 4)=Fin.castSucc (0:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    generalize frameCap=F at hh hH hlinear hN ⊢
    linarith
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    rw [show (1:Fin 4)=Fin.castSucc (1:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    generalize frameCap=F at hh hH hlinear hN ⊢
    linarith
  · have hh := LowRectangle.original_rectangle
      (k:=Explicit.k .low θ) (m:=Explicit.m .low θ)
      (show Explicit.k .low θ∈Icc LowRectangle.k0 1 from
        ⟨hr.1.1,by linarith [hr.1.2]⟩)
      (show Explicit.m .low θ∈Icc (1:ℝ) LowRectangle.M from ⟨hm,hr.2.2⟩)
      hN hNP hPcap
    rw [hdiff] at hh
    rw [show (2:Fin 4)=Fin.castSucc (2:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (min (Explicit.l .low θ) (Explicit.m .low θ))
        (max (Explicit.l .low θ) (Explicit.m .low θ)) (s-θ)≤
      U R (min (Explicit.l .low θ) (Explicit.m .low θ))
        (max (Explicit.l .low θ) (Explicit.m .low θ)) (frameCap-θ)+_
    have hl : Explicit.l .low θ=1 := rfl
    rw [hl,min_eq_left hm,max_eq_right hm]
    linarith
  · rw [Blocks.positive_D,Blocks.positive_D]
    have hgamma := mul_le_mul_of_nonneg_right (gamma_upper hθ hz hsf) hN
    generalize frameCap=F at hgamma hH hlinear ⊢
    linarith

theorem saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i j : Fin 4) :
    Blocks.pure .low θ z s i j≤Blocks.saturated .low θ z s i j := by
  have hsf : s∈Icc 0 frameCap := ⟨(Explicit.frame_domain .low hθ).1.trans hs.1,hs.2⟩
  have hpure (i j : Fin 4) :
      Blocks.pure .low θ z s i j=Blocks.positive .low θ z s (s-θ) i := by
    by_cases hst : s≤θ
    · have he : s=θ := le_antisymm hst hs.1
      subst he
      simp only [Blocks.pure,ChargedHybridConcentration.pure,le_refl,↓reduceIte,sub_self,
        V_zero,Blocks.positive_zero]
    · show (if s≤θ then _ else _)=_
      rw [ite_eq_right hst]
      rfl
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .low θ z s 3 3=
          Blocks.block .low θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,Blocks.block,
          ↓reduceIte]
      rw [he,Blocks.block_D,hpure]
      exact separated_lower hθ hz hs 3 3
    · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
      obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
        ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
      subst i
      exact SameBlock.ordinary_saturated_lower .low hθ hsf r
  · have he : Blocks.saturated .low θ z s i j=
        Blocks.positive .low θ z s (frameCap-θ) i+Blocks.negative .low θ (frameCap-s) j := by
      simp only [Blocks.saturated,ChargedHybridConcentration.saturated,hij,↓reduceIte]
      rfl
    rw [he,hpure]
    exact separated_lower hθ hz hs i j

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
