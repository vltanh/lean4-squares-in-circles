module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3HighNegative
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Positive

/-!
# Every high intrinsic BT3 reference alternative

Uncompiled Section 5, high interval. All four ordinary pairs satisfy
the existing full and half-angle derivative margins. The optional
index used in the generic lemma below merely expresses an ordinary
family as a hybrid family with an unused distinguished index; its
conclusion is stated only for the original four pairs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open NegativeAPositiveTD.HighSaturated NegativeAPositiveTD.NegativeSlope

theorem ordinary_pure_le_saturated (atG : Bool) {p q : Fin 4→ℝ} {i j : Fin 4} {s z : ℝ}
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hqlo : ∀i,1≤q i) (hqhi : ∀i,q i≤largerCap atG)
    (hratio : ∀i,(lowerRatio (fullCase atG):ℝ)*q i≤p i)
    (hsine : ∀i,q i*Real.sin (frameCap-s)≤p i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc (1/5:ℝ) frameCap) :
    Concentration.pure .high p q i j s z≤Concentration.saturated .high p q i j s z := by
  let p' : Option (Fin 4)→ℝ := fun x => x.elim 1 p
  let q' : Option (Fin 4)→ℝ := fun x => x.elim 1 q
  have hp' (x : Option (Fin 4)) : 0<p' x := by cases x <;> simp [p'] <;> first | norm_num | apply hp
  have hpq' (x : Option (Fin 4)) : p' x≤q' x := by cases x <;> simp [p',q'] <;> apply hpq
  have hqp' (x : Option (Fin 4)) : q' x≤2*p' x := by cases x <;> simp [p',q'] <;> apply hqp
  have hqlo' (x : Option (Fin 4)) : 1≤q' x := by cases x <;> simp [q'] <;> apply hqlo
  have hqhi' (x : Option (Fin 4)) : q' x≤largerCap atG := by
    cases x
    · cases atG <;> norm_num [q',largerCap]
    · apply hqhi
  have hr' (x : Option (Fin 4)) : (lowerRatio (fullCase atG):ℝ)*q' x≤p' x := by
    cases x
    · cases atG <;> norm_num [p',q',fullCase,lowerRatio]
    · apply hratio
  have hsin' (x : Option (Fin 4)) : q' x*Real.sin (frameCap-s)≤p' x := by
    cases x
    · simpa [p',q'] using Real.sin_le_one (frameCap-s)
    · apply hsine
  have hh := NegativeAPositiveTD.HighSaturated.pure_le_saturated atG
    (d:=(none:Option (Fin 4))) (i:=some i) (j:=some j) (a:=0) (by norm_num)
    hp' hpq' hqp' hqlo' hqhi' hr' hsin' hs hz
  simpa [Concentration.pure,Concentration.saturated,Concentration.positive,Concentration.block,
    NegativeAPositiveTD.Concentration.pure,NegativeAPositiveTD.Concentration.saturated,
    PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,p',q'] using hh

theorem sine_condition (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    Explicit.q .high atG z s i*Real.sin (frameCap-s)≤Explicit.p .high atG z s i := by
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hsin := (transport_trig hN).2.2.2.1
  cases atG
  · have hb := Explicit.high_AB_pair_bounds hz hs i
    have hh := mul_le_mul_of_nonneg_left hsin.le (show 0≤Explicit.q .high false z s i by linarith [hb.2.1])
    nlinarith [hb.1]
  · have hb := Explicit.high_ranges hz
    have hr := Explicit.high_ratios hz
    have hc := Explicit.high_rotation hz
    have hl : 0<Explicit.l .high z := by linarith [hb.2.1.1]
    fin_cases i
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,Matrix.cons_val_zero,one_mul]
      linarith [hb.1.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,
        ↓reduceIte,Matrix.cons_val_succ,Matrix.cons_val_zero]
      have ht := transport_trig hsf
      have hcos : 0<Real.cos s := by linarith [ht.1]
      have hcap := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      have hprod := mul_nonneg (show 0≤Real.cos frameCap by linarith [hcap.1]) ht.2.2.1
      have hsine : Real.sin (frameCap-s)≤Real.sin frameCap*Real.cos s := by
        rw [Real.sin_sub]
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hsine hl.le
      have hsec : secant (Explicit.l .high z) s*Real.sin (frameCap-s)≤Explicit.l .high z*Real.sin frameCap := by
        dsimp [secant,NegativeAPositiveTD.secant]
        rw [div_mul_eq_mul_div,div_le_iff₀ hcos]
        nlinarith only [hscaled]
      have hright := mul_le_mul_of_nonneg_left hcap.2.2.2.1.le hl.le
      linarith [hr.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
        ↓reduceIte,Matrix.cons_val_succ,Matrix.cons_val_zero,
        min_eq_right hr.2.2.2.2.le,max_eq_left hr.2.2.2.2.le]
      have hh := mul_le_mul_of_nonneg_left hsin.le hl.le
      linarith [hr.2.2.1]
    · simp only [Explicit.p,Explicit.q,pWeights,qWeights,↓reduceIte,
        Matrix.cons_val_succ,Matrix.cons_val_zero,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le,one_mul]
      linarith [hc.1]

theorem pure_le_saturated (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z≤
      Concentration.saturated .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z := by
  have hp := Explicit.ordered_pair_domain .high atG hz hs
  have hb (i : Fin 4) :
      (lowerRatio (fullCase atG):ℝ)*Explicit.q .high atG z s i<Explicit.p .high atG z s i ∧
      1≤Explicit.q .high atG z s i ∧ Explicit.q .high atG z s i<largerCap atG := by
    cases atG
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_AB_pair_bounds hz hs i
    · simpa [fullCase,lowerRatio,largerCap] using Explicit.high_GA_pair_bounds hz hs i
  exact ordinary_pure_le_saturated atG (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => (hp i).2.2) (fun i => (hb i).2.1) (fun i => (hb i).2.2.le)
    (fun i => (hb i).1.le) (sine_condition atG hz hs) (Explicit.angle_domain atG hs).2
    ⟨by linarith [hz.1],hz.2⟩

theorem D_dominates_H {z t : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .high z) 1 t≤V R (Explicit.c .high z) 1 t := by
  have hb := Explicit.basic_domain .high hz
  have hc := Explicit.high_rotation hz
  exact V_monotone_smaller (Real.sqrt_nonneg _) (by norm_num) ht
    ⟨by linarith [hb.1.1],by linarith [hb.1.2]⟩
    ⟨by linarith [hc.1],hc.2.2.le⟩ hc.2.1.le

theorem negative_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      V R (Explicit.p .high atG z s i) (Explicit.q .high atG z s i) (z-s) := by
  by_cases hiD : i=3
  · subst i
    have hh := HighNegative.unaffected_positive atG hz hs hsz 0 (by cases atG <;> exact Or.inl rfl)
    have hc := Explicit.high_rotation hz
    have hd := D_dominates_H hz (show z-s∈Icc 0 frameCap from
      ⟨by linarith,by linarith [hs.1,hz.2]⟩)
    simp only [Explicit.p,Explicit.q,pWeights,qWeights,↓reduceIte,Matrix.cons_val_zero,
      Matrix.cons_val_succ,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le] at hh ⊢
    linarith
  by_cases hu : HighNegative.Unaffected atG i
  · exact HighNegative.unaffected_positive atG hz hs hsz i hu
  · have ha := HighNegative.affected_positive atG hz hs hsz
    have hml := (Explicit.high_ratios hz).2.2.2.2
    have hw := (Explicit.secant_bounds .high atG hz hs).1
    cases atG <;> fin_cases i <;> simp [HighNegative.Unaffected] at hu <;> simp_all only
    · simpa [Explicit.p,Explicit.q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
        Angular.affected,min_eq_right (hml.le.trans hw),max_eq_left (hml.le.trans hw)] using ha
    · simpa [Explicit.p,Explicit.q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,Angular.affected] using ha

theorem pure_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,if_pos hsz] using negative_positive atG hz hs hsz j
  · have hh := Positive.reduces_to_equal .high atG hz hs (le_of_not_ge hsz) i
    have he : 0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z := by
      cases atG
      · exact (high_endpoints hz).2.2.2.2
      · exact (high_endpoints hz).2.2.2.1
    simp only [Concentration.pure,if_neg hsz]
    linarith

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s z+
      min (Concentration.pure .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z)
        (Concentration.saturated .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) i j s z) := by
  rw [min_eq_left (pure_le_saturated atG hz hs i j)]
  exact pure_positive atG hz hs i j

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.High
