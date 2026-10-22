module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2PositiveSlopes
public import SquaresInCircles.Eight.TableFree.OrdinaryPositiveEnvelope

/-!
# Removing the saturated alternatives on the high coefficient interval

Uncompiled transcription of Section 9 of the negative-A angle companion.
The exact surplus is retained. The four derivative margins are .0105,
.01325, .078 and .067, with the D linear positive piece included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighSaturated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope PositiveTD.Hybrid
open NegativeSlope

def fullCase (atG : Bool) : Lower := if atG then .GAfull else .ABfull
def halfCase (atG : Bool) : Lower := if atG then .GAhalf else .ABhalf
def largerCap (atG : Bool) : ℝ := if atG then 11/10 else 23/20

theorem case_angles (atG : Bool) :
    (lowerAngle (fullCase atG):ℝ)=frameCap ∧
    (lowerAngle (halfCase atG):ℝ)=(1/2:ℝ) ∧
    lowerRatio (halfCase atG)=lowerRatio (fullCase atG) := by
  cases atG <;> norm_num [fullCase,halfCase,lowerAngle,lowerRatio,frameCap]

theorem negative_growth (e : Lower) {p q x y : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hpr : (lowerRatio e:ℝ)*q≤p)
    (hx : x∈Icc 0 (lowerAngle e:ℝ)) (hy : y∈Icc 0 (lowerAngle e:ℝ))
    (hxy : x≤y) :
    (lowerValue e:ℝ)*q*(y-x)≤V R p q y-V R p q x := by
  have hq := hp.trans_le hpq
  have hd := lower_angle_domain e
  have hf (t : ℝ) (ht : t∈Icc 0 (lowerAngle e:ℝ)) :=
    V_hasDerivAt hp hq (show t∈Icc 0 frameCap from ⟨ht.1,ht.2.trans hd.2⟩)
  exact derivative_reserve
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t (Ioo_subset_Icc_self ht))
    (fun t ht => (lower_bound e hp hpq hqp hpr (Ioo_subset_Icc_self ht)).le)
    hx hy hxy

variable {ι : Type*} [DecidableEq ι]

theorem positive_lower {p q : ι→ℝ} {d i : ι} {a t : ℝ}
    (ha : a≤2/5) (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hq : 1≤q i) (ht : t∈Icc 0 frameCap) :
    -(109/200)*q i*t≤positive R a p q d i t := by
  by_cases hi : i=d
  · simp only [positive,if_pos hi]
    have hm := mul_le_mul_of_nonneg_right
      (show a≤(109/200)*q i by linarith) ht.1
    linarith
  · simpa only [positive,if_neg hi] using U_lower
      (Real.sqrt_nonneg qCap) (Real.sq_sqrt (by norm_num [qCap])).le hp hpq hqp ht

theorem positive_half_growth {p q : ι→ℝ} {d i : ι} {a x y : ℝ}
    (ha : a≤2/5) (hp : 0<p i) (hpq : p i≤q i) (hqp : q i≤2*p i)
    (hq : 1≤q i) (hx : x∈Icc 0 (1/2:ℝ)) (hy : y∈Icc 0 (1/2:ℝ))
    (hxy : x≤y) :
    -(31/50)*q i*(y-x)≤positive R a p q d i y-positive R a p q d i x := by
  by_cases hi : i=d
  · simp only [positive,if_pos hi]
    have hm := mul_le_mul_of_nonneg_right
      (show a≤(31/50)*q i by linarith) (sub_nonneg.mpr hxy)
    linarith
  · simp only [positive,if_neg hi]
    have hf (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) :=
      PositiveSlope.U_hasDerivAt hp (hp.trans_le hpq)
        (show t∈Icc 0 frameCap by exact ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩)
    exact derivative_reserve
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => hf t (Ioo_subset_Icc_self ht))
      (fun t ht => (PositiveSlope.half_bound hp hpq hqp (Ioo_subset_Icc_self ht)).le)
      hx hy hxy

theorem pure_le_saturated (atG : Bool) {p q : ι→ℝ} {d i j : ι} {a s z : ℝ}
    (ha : a≤2/5)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hqlo : ∀i,1≤q i) (hqhi : ∀i,q i≤largerCap atG)
    (hratio : ∀i,(lowerRatio (fullCase atG):ℝ)*q i≤p i)
    (hsine : ∀i,q i*Real.sin (frameCap-s)≤p i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc (1/5:ℝ) frameCap) :
    Concentration.pure R a p q d i j s z≤
      Concentration.saturated R a p q d i j s z := by
  let P : ℝ := frameCap-z
  let N : ℝ := frameCap-s
  have hP : P∈Icc 0 frameCap := by
    dsimp [P]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hPhalf : P∈Icc 0 (1/2:ℝ) := by
    dsimp [P,frameCap] at ⊢
    dsimp [frameCap] at hz
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hN : N∈Icc 0 frameCap := by
    dsimp [N]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hf (a₁ a₂ : ℝ) (h₁ : a₁∈Icc 0 frameCap)
      (h₂ : a₂∈Icc 0 frameCap) (h₁₂ : a₁≤a₂) (k : ι) :
      (lowerValue (fullCase atG):ℝ)*q k*(a₂-a₁)≤V R (p k) (q k) a₂-V R (p k) (q k) a₁ := by
    apply negative_growth (fullCase atG) (hp k) (hpq k) (hqp k) (hratio k)
    · simpa only [(case_angles atG).1] using h₁
    · simpa only [(case_angles atG).1] using h₂
    · exact h₁₂
  have hh (a₁ a₂ : ℝ) (h₁ : a₁∈Icc 0 (1/2:ℝ))
      (h₂ : a₂∈Icc 0 (1/2:ℝ)) (h₁₂ : a₁≤a₂) (k : ι) :
      (lowerValue (halfCase atG):ℝ)*q k*(a₂-a₁)≤V R (p k) (q k) a₂-V R (p k) (q k) a₁ := by
    apply negative_growth (halfCase atG) (hp k) (hpq k) (hqp k)
    · simpa only [(case_angles atG).2.2] using hratio k
    · simpa only [(case_angles atG).2.1] using h₁
    · simpa only [(case_angles atG).2.1] using h₂
    · exact h₁₂
  have hpay (k : ι) : a≤(lowerValue (fullCase atG):ℝ)*q k := by
    have hq := hqlo k
    cases atG <;> norm_num [fullCase,lowerValue] at ⊢ <;> linarith
  by_cases hsz : s≤z
  · have hPN : P≤N := by dsimp [P,N]; linarith
    have hsurplus : N-P=z-s := by dsimp [P,N]; ring
    have hdiff : N-P∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [hN.2,hP.1]⟩
    simp only [Concentration.pure,if_pos hsz,Concentration.saturated]
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      by_cases hid : i=d
      · simp only [block,if_pos hid]
        have hg := hf (N-P) N hdiff hN (by linarith [hP.1]) i
        have hp₁ := mul_le_mul_of_nonneg_right (hpay i) hP.1
        rw [hsurplus] at hg
        change V R (p i) (q i) (z-s)≤ -a*P+V R (p i) (q i) N
        nlinarith
      · simp only [block,if_neg hid]
        have hsine' : q i*Real.sin N≤p i := by simpa [N] using hsine i
        have hc := SameBlock.negative_surplus (hp i).le
          (show P∈Icc 0 N from ⟨hP.1,hPN⟩) hN hsine'
        simpa only [hsurplus] using hc
    · simp only [if_neg hij]
      have hg := hf (N-P) N hdiff hN (by linarith [hP.1]) j
      have hu := positive_lower (d:=d) ha (hp i) (hpq i) (hqp i) (hqlo i) hP
      have hqi := mul_le_mul_of_nonneg_right (hqhi i) hP.1
      have hqj := mul_le_mul_of_nonneg_right (hqlo j) hP.1
      rw [hsurplus] at hg
      change V R (p j) (q j) (z-s)≤positive R a p q d i P+V R (p j) (q j) N
      cases atG <;> norm_num [fullCase,lowerValue,largerCap] at hg hqi <;> nlinarith
  · have hzs : z≤s := (lt_of_not_ge hsz).le
    have hNP : N≤P := by dsimp [P,N]; linarith
    have hsurplus : P-N=s-z := by dsimp [P,N]; ring
    have hdiff : P-N∈Icc 0 (1/2:ℝ) :=
      ⟨by linarith,by linarith [hPhalf.2,hN.1]⟩
    have hNhalf : N∈Icc 0 (1/2:ℝ) := ⟨hN.1,hNP.trans hPhalf.2⟩
    simp only [Concentration.pure,if_neg hsz,Concentration.saturated]
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      by_cases hid : i=d
      · simp only [block,positive,if_pos hid]
        have hg := hf 0 N (by norm_num [frameCap]) hN hN.1 i
        have hp₁ := mul_le_mul_of_nonneg_right (hpay i) hN.1
        simp only [V_zero,sub_zero] at hg
        change -a*(s-z)≤ -a*P+V R (p i) (q i) N
        nlinarith [hsurplus]
      · simp only [block,positive,if_neg hid]
        have hratio' : q i≤(17/10)*p i := by
          have hr := hratio i
          have hq := hqlo i
          cases atG <;> norm_num [fullCase,lowerRatio] at hr <;> linarith
        have hc := SameBlock.positive_surplus (hp i).le hratio' hP ⟨hN.1,hNP⟩
        simpa only [hsurplus] using hc
    · simp only [if_neg hij]
      have hg := hh 0 N (by norm_num) hNhalf hN.1 j
      have hu := positive_half_growth (d:=d) ha (hp i) (hpq i) (hqp i)
        (hqlo i) hdiff hPhalf (by linarith [hN.1])
      have hqi := mul_le_mul_of_nonneg_right (hqhi i) hN.1
      have hqj := mul_le_mul_of_nonneg_right (hqlo j) hN.1
      simp only [V_zero,sub_zero] at hg
      rw [hsurplus] at hu
      change positive R a p q d i (s-z)≤positive R a p q d i P+V R (p j) (q j) N
      cases atG <;> norm_num [halfCase,lowerValue,largerCap] at hg hqi <;> nlinarith

theorem explicit_sine_condition (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) :
    Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i*
        Real.sin (frameCap-s)≤
      Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i := by
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hsin := (transport_trig hN).2.2.2.1
  cases atG
  · have hb := Explicit.high_AB_pair_bounds hz hs i
    have hq0 : 0≤Source.qWeights false (Explicit.k .high z) (Explicit.l .high z)
        (Explicit.m .high z) s i := by linarith [hb.2.1]
    have hh := mul_le_mul_of_nonneg_left hsin.le hq0
    nlinarith [hb.1]
  · obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := Explicit.high_ranges hz
    have hkl := Explicit.high_ratio_lower hz
    have hml := Explicit.high_tilted hz
    have hl : 0<Explicit.l .high z := by linarith
    have hm : 0<Explicit.m .high z := by linarith [hml.1]
    fin_cases i
    · simp only [Source.pWeights,Source.qWeights,Matrix.cons_val_zero,one_mul]
      linarith
    · simp only [Source.pWeights,Source.qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero,
        lambdaG,↓reduceIte]
      have ht := transport_trig hsf
      have hc : 0<Real.cos s := by linarith [ht.1]
      have hcap := transport_trig
        (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      have hprod : 0≤Real.cos frameCap*Real.sin s :=
        mul_nonneg (by linarith [hcap.1]) ht.2.2.1
      have hsine : Real.sin (frameCap-s)≤Real.sin frameCap*Real.cos s := by
        rw [Real.sin_sub]
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hsine hl.le
      have hsec : secant (Explicit.l .high z) s*Real.sin (frameCap-s)≤
          Explicit.l .high z*Real.sin frameCap := by
        dsimp [secant]
        rw [div_mul_eq_mul_div,div_le_iff₀ hc]
        nlinarith only [hscaled]
      have hright := mul_le_mul_of_nonneg_left hcap.2.2.2.1.le hl.le
      linarith
    · simp only [Source.pWeights,Source.qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero,
        lambdaB,↓reduceIte]
      rcases le_total (Explicit.l .high z) (Explicit.m .high z) with hle | hle
      · rw [max_eq_right hle,min_eq_left hle]
        have hh := mul_le_mul_of_nonneg_left hsin.le hm.le
        nlinarith [hml.2.1]
      · rw [max_eq_left hle,min_eq_right hle]
        have hh := mul_le_mul_of_nonneg_left hsin.le hl.le
        nlinarith [hml.1]
    · simp only [Source.pWeights,Source.qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero,one_mul]
      linarith

theorem explicit_pure_le_saturated (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    Concentration.pure R (diagonal-1/2)
      (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      3 i j s z≤
    Concentration.saturated R (diagonal-1/2)
      (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
      3 i j s z := by
  have hp := Explicit.ordered_pair_domain .high atG hz hs
  have hb (i : Fin 4) :
      (lowerRatio (fullCase atG):ℝ)*
          Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i<
        Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i ∧
      1≤Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i ∧
      Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i<largerCap atG := by
    cases atG
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_AB_pair_bounds hz hs i
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_GA_pair_bounds hz hs i
  exact pure_le_saturated atG (by linarith [diagonal_bounds.2])
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
    (fun i => (hb i).2.1) (fun i => (hb i).2.2.le) (fun i => (hb i).1.le)
    (explicit_sine_condition atG hz hs) (Explicit.angle_domain atG hs).2 hz

theorem intrinsic_eq_pure (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    Source.intrinsic atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z i j=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
        Concentration.pure R (diagonal-1/2)
          (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
          (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
          3 i j s z := by
  have hh := explicit_pure_le_saturated atG hz hs i j
  simpa only [Source.intrinsic,Explicit.m,min_eq_left hh]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighSaturated
